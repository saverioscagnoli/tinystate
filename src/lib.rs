#![no_std]
#![warn(clippy::use_self)]

mod err;
mod traits;
mod transition;

#[cfg(feature = "derive")]
pub use tinystate_derive::Events;
#[cfg(feature = "derive")]
pub use tinystate_derive::States;

pub use crate::err::BuildError;
pub use crate::traits::Events;
pub use crate::traits::States;
pub use crate::transition::Action;
pub use crate::transition::Edge;
pub use crate::transition::Outcome;
pub use crate::transition::Transition;

pub(crate) type Cell<S, E, C> = Option<Transition<S, E, C>>;

pub struct StateMachine<S: States, E: Events, const NS: usize, const NE: usize, C> {
    initial: S,
    state: S,
    ctx: C,
    table: [[Cell<S, E, C>; NE]; NS],
}

impl<S: States, E: Events, const NS: usize, const NE: usize, C> StateMachine<S, E, NS, NE, C> {
    pub fn current(&self) -> &S {
        &self.state
    }

    pub fn context(&self) -> &C {
        &self.ctx
    }

    pub fn context_mut(&mut self) -> &mut C {
        &mut self.ctx
    }

    pub fn trigger(&mut self, event: E) -> Outcome {
        let (si, ei) = (self.state.index(), event.index());

        let Some(t) = &self.table[si][ei] else {
            return Outcome::NoTransition;
        };

        if let Some(g) = t.guard
            && !g(&self.ctx, &self.state, &event)
        {
            return Outcome::Guarded;
        }

        let (action_goto, run, effect) = match &t.action {
            Action::Goto(s) => (Some(s.clone()), None, t.effect),
            Action::Run(f) => (None, Some(*f), t.effect),
            Action::SelfLoop => (None, None, t.effect),
        };

        // Resolve the destination first: a declining `Run` must not leave the
        // effect applied. `None` means a self loop, which still runs it.
        let next: Option<S> = match (action_goto, run) {
            (Some(s), _) => Some(s),
            (None, Some(f)) => match f(&mut self.ctx, &self.state, &event) {
                Some(s) => Some(s),
                _ => return Outcome::Declined,
            },
            (None, None) => None,
        };

        if let Some(fx) = effect {
            fx(&mut self.ctx, &self.state, &event);
        }

        match next {
            Some(s) => {
                self.state = s;
                Outcome::Moved
            }
            None => Outcome::Stayed,
        }
    }

    pub fn can_trigger(&self, event: &E) -> bool {
        let (si, ei) = (self.state.index(), event.index());

        match &self.table[si][ei] {
            None => false,
            Some(t) => t.guard.is_none_or(|g| g(&self.ctx, &self.state, event)),
        }
    }

    pub fn edge(&self, si: usize, ei: usize) -> Option<usize> {
        match &self.table.get(si)?.get(ei)?.as_ref()?.action {
            Action::Goto(s) => Some(s.index()),
            Action::SelfLoop => Some(si),
            Action::Run(_) => None,
        }
    }

    pub fn edge_kind(&self, si: usize, ei: usize) -> Edge {
        match self
            .table
            .get(si)
            .and_then(|r| r.get(ei))
            .and_then(|c| c.as_ref())
        {
            None => Edge::None,
            Some(t) => match &t.action {
                Action::Goto(s) => Edge::Static(s.index()),
                Action::SelfLoop => Edge::Static(si),
                Action::Run(_) => Edge::Dynamic,
            },
        }
    }

    pub fn edges(&self) -> impl Iterator<Item = (usize, usize, usize)> + '_ {
        (0..NS).flat_map(move |si| {
            (0..NE).filter_map(move |ei| self.edge(si, ei).map(|di| (si, ei, di)))
        })
    }

    pub fn cost(&self, si: usize, ei: usize) -> Option<f32> {
        Some(self.table.get(si)?.get(ei)?.as_ref()?.cost)
    }

    pub fn is_fully_static(&self) -> bool {
        (0..NS).all(|si| (0..NE).all(|ei| !matches!(self.edge_kind(si, ei), Edge::Dynamic)))
    }

    pub fn reset(&mut self) {
        self.state = self.initial.clone();
    }

    pub fn reset_to(&mut self, state: S) {
        self.state = state;
    }

    pub fn initial(&self) -> &S {
        &self.initial
    }
}

impl<S: States, E: Events, const NS: usize, const NE: usize, C: Default>
    StateMachine<S, E, NS, NE, C>
{
    pub fn reset_all(&mut self) {
        self.state = self.initial.clone();
        self.ctx = C::default();
    }
}

pub struct StateMachineBuilder<S: States, E: Events, const NS: usize, const NE: usize, C = ()> {
    initial: Option<S>,
    ctx: C,
    table: [[Cell<S, E, C>; NE]; NS],
    last: Option<(usize, usize)>,
    err: Option<BuildError>,
}

impl<S: States, E: Events, const NS: usize, const NE: usize, C: Default> Default
    for StateMachineBuilder<S, E, NS, NE, C>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<S: States, E: Events, const NS: usize, const NE: usize, C: Default>
    StateMachineBuilder<S, E, NS, NE, C>
{
    pub fn new() -> Self {
        Self::with_context(C::default())
    }
}

impl<S: States, E: Events, const NS: usize, const NE: usize, C>
    StateMachineBuilder<S, E, NS, NE, C>
{
    pub fn with_context(ctx: C) -> Self {
        const { assert!(NS == S::COUNT, "Number of states (NS) must equal S::COUNT") }
        const { assert!(NE == E::COUNT, "Number of events (NE) must equal E::COUNT") }

        Self {
            initial: None,
            ctx,
            table: core::array::from_fn(|_| core::array::from_fn(|_| None)),
            err: None,
            last: None,
        }
    }

    pub fn initial(mut self, state: S) -> Self {
        self.initial = Some(state);
        self
    }

    fn set(mut self, from: S::Tag, event: E::Tag, action: Action<S, E, C>) -> Self {
        let (si, ei) = (S::tag_index(from), E::tag_index(event));

        if self.table[si][ei].is_some() && self.err.is_none() {
            self.err = Some(BuildError::Duplicate {
                state: S::NAMES[si],
                event: E::NAMES[ei],
            });
        }

        self.table[si][ei] = Some(Transition::new(action));
        self.last = Some((si, ei));
        self
    }

    fn modify(mut self, f: impl FnOnce(&mut Transition<S, E, C>)) -> Self {
        match self.last {
            Some((si, ei)) => {
                if let Some(t) = &mut self.table[si][ei] {
                    f(t);
                }
            }
            None if self.err.is_none() => {
                self.err = Some(BuildError::ModifierWithoutTransition);
            }
            None => {}
        }

        self
    }

    pub fn transition(self, from: impl Into<S::Tag>, event: impl Into<E::Tag>, to: S) -> Self {
        self.set(from.into(), event.into(), Action::Goto(to))
    }

    pub fn self_loop(self, from: impl Into<S::Tag>, event: impl Into<E::Tag>) -> Self {
        self.set(from.into(), event.into(), Action::SelfLoop)
    }

    pub fn action(
        self,
        from: impl Into<S::Tag>,
        event: impl Into<E::Tag>,
        f: fn(&mut C, &S, &E) -> Option<S>,
    ) -> Self {
        self.set(from.into(), event.into(), Action::Run(f))
    }

    pub fn guard(self, f: fn(&C, &S, &E) -> bool) -> Self {
        self.modify(|t| t.guard = Some(f))
    }

    pub fn effect(self, f: fn(&mut C, &S, &E)) -> Self {
        self.modify(|t| t.effect = Some(f))
    }

    pub fn cost(self, c: f32) -> Self {
        self.modify(|t| t.cost = c)
    }

    pub fn build(self) -> Result<StateMachine<S, E, NS, NE, C>, BuildError> {
        if let Some(e) = self.err {
            return Err(e);
        }

        let state = self.initial.ok_or(BuildError::NoInitialState)?;

        let mut seen = [false; NS];
        let mut stack = [0usize; NS];
        let mut top = 0usize;
        let mut provable = true;

        seen[state.index()] = true;
        stack[top] = state.index();
        top += 1;

        while top > 0 {
            top -= 1;
            let si = stack[top];

            for ei in 0..NE {
                let Some(t) = &self.table[si][ei] else {
                    continue;
                };

                match &t.action {
                    Action::Run(_) => provable = false,
                    Action::SelfLoop => {}
                    Action::Goto(s) => {
                        let di = s.index();

                        if !seen[di] {
                            seen[di] = true;
                            stack[top] = di;
                            top += 1;
                        }
                    }
                }
            }
        }

        if provable && let Some(i) = seen.iter().position(|r| !r) {
            return Err(BuildError::Unreachable { state: S::NAMES[i] });
        }

        Ok(StateMachine {
            initial: state.clone(),
            state,
            ctx: self.ctx,
            table: self.table,
        })
    }
}

#[macro_export]
macro_rules! machine {
    ($s:ty, $e:ty) => {
        $crate::StateMachineBuilder::<
            $s,
            $e,
            { <$s as $crate::States>::COUNT },
            { <$e as $crate::Events>::COUNT },
        >::new()
    };
    ($s:ty, $e:ty, $c:expr) => {
        $crate::StateMachineBuilder::<
            $s,
            $e,
            { <$s as $crate::States>::COUNT },
            { <$e as $crate::Events>::COUNT },
            _,
        >::with_context($c)
    };
}
