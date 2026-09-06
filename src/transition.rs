pub enum Action<S, E, C> {
    Goto(S),
    Run(fn(&mut C, &S, &E) -> Option<S>),
    SelfLoop,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Moved,
    Stayed,
    Guarded,
    Declined,
    NoTransition,
}

pub struct Transition<S, E, C> {
    pub action: Action<S, E, C>,
    pub guard: Option<fn(&C, &S, &E) -> bool>,
    pub effect: Option<fn(&mut C, &S, &E)>,
    pub cost: f32,
}

impl<S, E, C> Transition<S, E, C> {
    pub const fn new(action: Action<S, E, C>) -> Self {
        Self {
            action,
            guard: None,
            effect: None,
            cost: 0.0,
        }
    }
}

pub enum Edge {
    None,
    Static(usize),
    Dynamic,
}
