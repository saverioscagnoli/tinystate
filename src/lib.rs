//! # tinystate
//!
//! A small, fast and `no_std` finite state machine for Rust.
//!
//! `tinystate` provides a compile-time validated state machine implementation with zero runtime overhead (only when building it its O(n^2), but since NE and NS are known is O(1) :P).
//! All state transitions are defined at compile time using const generics.
//!
//! ## Quick Start
//!
//! ```rust
//! use tinystate::{StateMachineBuilder, States, Events};
//!
//! #[derive(Debug, Clone, Copy, Default)]
//! enum TrafficLight {
//!     #[default]
//!     Red,
//!     Yellow,
//!     Green,
//! }
//!
//! impl States for TrafficLight {
//!     fn index(&self) -> usize {
//!         *self as usize
//!     }
//!     fn from_index(i: usize) -> Self {
//!         match i {
//!             0 => Self::Red,
//!             1 => Self::Yellow,
//!             2 => Self::Green,
//!             _ => unreachable!(),
//!         }
//!     }
//! }
//!
//! #[derive(Debug, Clone, Copy)]
//! enum Timer { Tick }
//!
//! impl Events for Timer {
//!     fn index(&self) -> usize { 0 }
//!     fn from_index(_: usize) -> Self { Self::Tick }
//! }
//!
//! let mut light = StateMachineBuilder::<TrafficLight, Timer, 3, 1>::new()
//!     .initial(TrafficLight::Red)
//!     .transition(TrafficLight::Red, Timer::Tick, TrafficLight::Green)
//!     .transition(TrafficLight::Green, Timer::Tick, TrafficLight::Yellow)
//!     .transition(TrafficLight::Yellow, Timer::Tick, TrafficLight::Red)
//!     .build()
//!     .unwrap();
//!
//! light.trigger(Timer::Tick);
//! assert!(matches!(light.current(), TrafficLight::Green));
//! ```

#![no_std]
#![forbid(unsafe_code)]
#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]
#![warn(clippy::unwrap_used)]
#![warn(clippy::expect_used)]
#![warn(clippy::missing_const_for_fn)]

mod err;
mod transition;

use core::marker::PhantomData;

pub use crate::err::ValidationError;
pub use crate::transition::Transition;
pub use crate::transition::TransitionMatrix;

#[rustfmt::skip]
#[cfg(feature = "derive")]
pub use tinystate_derive::{Events, States};

/// Trait for state types in a state machine.
///
/// Implement this trait to define the states of your DFA. Each state must be
/// convertible to and from a unique index for efficient matrix-based lookups.
///
/// # Example
///
/// ```rust
/// use tinystate::States;
///
/// #[derive(Debug, Clone, Copy, Default)]
/// enum DoorState {
///     #[default]
///     Closed,
///     Open,
///     Locked,
/// }
///
/// impl States for DoorState {
///     fn index(&self) -> usize {
///         *self as usize
///     }
///
///     fn from_index(i: usize) -> Self {
///         match i {
///             0 => Self::Closed,
///             1 => Self::Open,
///             2 => Self::Locked,
///             _ => unreachable!(),
///         }
///     }
/// }
/// ```
///
/// Or you can use the #[derive(States)] macro to automatically do this.
/// (Works only on unfielded enums)
pub trait States: Copy + Default {
    /// Returns the unique index for this state.
    fn index(&self) -> usize;

    /// Constructs a state from its index.
    fn from_index(index: usize) -> Self;
}

/// Trait for event types that trigger state transitions.
///
/// Implement this trait to define the events that can cause state transitions
/// in your DFA. Each event must be convertible to and from a unique index.
///
/// # Example
///
/// ```rust
/// use tinystate::Events;
///
/// #[derive(Debug, Clone, Copy)]
/// enum DoorEvent {
///     Push,
///     Pull,
///     Lock,
/// }
///
/// impl Events for DoorEvent {
///     fn index(&self) -> usize {
///         *self as usize
///     }
///
///     fn from_index(i: usize) -> Self {
///         match i {
///             0 => Self::Push,
///             1 => Self::Pull,
///             2 => Self::Lock,
///             _ => unreachable!(),
///         }
///     }
/// }
/// ```
/// Or you can use the #[derive(Events)] macro to automatically do this.
/// (Works only on unfielded enums)
pub trait Events: Copy {
    /// Returns the unique index for this event.
    fn index(&self) -> usize;

    /// Constructs an event from its index.
    fn from_index(index: usize) -> Self;
}

/// A deterministic finite automaton (DFA) state machine.
///
/// The state machine stores a transition matrix and tracks the current state.
/// All transitions are defined at compile time through the const generics `NS` (number of states)
/// and `NE` (number of events).
///
/// # Type Parameters
///
/// - `S`: The state type implementing [`States`]
/// - `E`: The event type implementing [`Events`]
/// - `NS`: The total number of states (const generic)
/// - `NE`: The total number of events (const generic)
///
/// # Example
///
/// ```rust
/// use tinystate::StateMachineBuilder;
/// # use tinystate::{States, Events};
/// # #[derive(Debug, Clone, Copy, Default)]
/// # enum MyState { #[default] A, B }
/// # impl States for MyState {
/// #     fn index(&self) -> usize { *self as usize }
/// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
/// # }
///
/// # #[derive(Debug, Clone, Copy)]
/// # enum MyEvent { X }
/// # impl Events for MyEvent {
/// #     fn index(&self) -> usize { 0 }
/// #     fn from_index(_: usize) -> Self { Self::X }
/// # }
///
/// let mut sm = StateMachineBuilder::<MyState, MyEvent, 2, 1>::new()
///     .initial(MyState::A)
///     .transition(MyState::A, MyEvent::X, MyState::B)
///     .transition(MyState::B, MyEvent::X, MyState::A)
///     .build()
///     .unwrap();
/// ```
pub struct StateMachine<S: States, E: Events, const NS: usize, const NE: usize> {
    /// Transition matrix: `[current_state][event] = next_state`
    matrix: TransitionMatrix<S, NS, NE>,
    current: S,
    _d: PhantomData<E>,
}

impl<S: States, E: Events, const NS: usize, const NE: usize> StateMachine<S, E, NS, NE> {
    const fn new(initial: S, matrix: TransitionMatrix<S, NS, NE>) -> Self {
        Self {
            matrix,
            current: initial,
            _d: PhantomData,
        }
    }

    /// Triggers a state transition based on the given event.
    ///
    /// This unconditionally transitions to the next state defined in the transition matrix.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    ///
    /// # #[derive(Debug, Clone, Copy, Default, PartialEq)]
    /// # enum S { #[default] A, B }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    ///
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    ///
    /// let mut sm = StateMachineBuilder::<S, E, 2, 1>::new()
    ///     .initial(S::A)
    ///     .transition(S::A, E::X, S::B)
    ///     .transition(S::B, E::X, S::A)
    ///     .build()
    ///     .unwrap();
    ///
    /// sm.trigger(E::X);
    /// assert_eq!(sm.current(), &S::B);
    /// ```
    #[inline]
    pub fn trigger(&mut self, event: E) {
        let (i, j) = (self.current.index(), event.index());
        let t = self.matrix[i][j];

        self.current = t.to;
    }

    /// Checks if an event would cause a state change.
    ///
    /// Returns `true` if triggering the event would transition to a different state,
    /// `false` if it would remain in the current state (self-loop).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    /// # #[derive(Debug, Clone, Copy, Default)]
    /// # enum S { #[default] A, B }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    ///
    /// let sm = StateMachineBuilder::<S, E, 2, 1>::new()
    ///     .initial(S::A)
    ///     .transition(S::A, E::X, S::B)
    ///     .self_loop(S::B, E::X)
    ///     .build()
    ///     .unwrap();
    ///
    /// assert!(sm.can_trigger(E::X)); // Would transition A -> B
    /// ```
    #[inline]
    pub fn can_trigger(&self, event: E) -> bool {
        let (i, j) = (self.current.index(), event.index());
        let t = self.matrix[i][j];

        // Returns true if the event causes a state change
        t.to.index() != self.current.index()
    }

    /// Conditionally triggers a state transition.
    ///
    /// Only transitions if the provided condition returns `true` for the current state.
    /// Returns `true` if the transition occurred, `false` otherwise.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    /// # #[derive(Debug, Clone, Copy, Default, PartialEq)]
    /// # enum S { #[default] A, B }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    /// let mut sm = StateMachineBuilder::<S, E, 2, 1>::new()
    ///     .initial(S::A)
    ///     .transition(S::A, E::X, S::B)
    ///     .transition(S::B, E::X, S::A)
    ///     .build()
    ///     .unwrap();
    ///
    /// let transitioned = sm.trigger_if(E::X, |s| matches!(s, S::A));
    /// assert!(transitioned);
    /// assert_eq!(sm.current(), &S::B);
    /// ```
    #[inline]
    pub fn trigger_if<F>(&mut self, event: E, condition: F) -> bool
    where
        F: FnOnce(&S) -> bool,
    {
        if condition(&self.current) {
            self.trigger(event);
            true
        } else {
            false
        }
    }

    /// Triggers a transition only if its cost is within budget.
    ///
    /// Only available with the `costs` feature enabled.
    /// Returns `true` if the transition occurred, `false` if the cost exceeded the budget.
    ///
    /// # Feature Flag
    ///
    /// This method requires the `costs` feature to be enabled.
    #[cfg(feature = "costs")]
    pub fn trigger_if_affordable(&mut self, event: E, budget: f32) -> Result<f32, f32> {
        let (i, j) = (self.current.index(), event.index());
        let cost = self.matrix[i][j].cost;

        if cost <= budget {
            self.trigger(event);

            Ok(cost)
        } else {
            Err(cost)
        }
    }

    /// Attempts to trigger a transition, returning the result.
    ///
    /// Returns `Ok(new_state)` if the state changed, or `Err(old_state)` if it remained the same.
    ///
    /// # Errors
    ///
    /// Returns `Err(old_state)` if the event triggered a self-loop (state did not change).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    /// # #[derive(Debug, Clone, Copy, Default, PartialEq)]
    /// # enum S { #[default] A, B }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    /// let mut sm = StateMachineBuilder::<S, E, 2, 1>::new()
    ///     .initial(S::A)
    ///     .transition(S::A, E::X, S::B)
    ///     .self_loop(S::B, E::X)
    ///     .build()
    ///     .unwrap();
    ///
    /// assert_eq!(sm.try_trigger(E::X), Ok(S::B));
    /// assert_eq!(sm.try_trigger(E::X), Err(S::B)); // Self-loop
    /// ```
    #[inline]
    pub fn try_trigger(&mut self, event: E) -> Result<S, S> {
        let old_state = self.current;
        self.trigger(event);

        if self.current.index() == old_state.index() {
            Err(old_state)
        } else {
            Ok(self.current)
        }
    }

    /// Returns the next state without transitioning.
    ///
    /// Useful for previewing what state an event would lead to.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    /// # #[derive(Debug, Clone, Copy, Default, PartialEq)]
    /// # enum S { #[default] A, B }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    /// let sm = StateMachineBuilder::<S, E, 2, 1>::new()
    ///     .initial(S::A)
    ///     .transition(S::A, E::X, S::B)
    ///     .transition(S::B, E::X, S::A)
    ///     .build()
    ///     .unwrap();
    ///
    /// assert_eq!(sm.next_state(E::X), S::B);
    /// ```
    #[inline]
    pub fn next_state(&self, event: E) -> S {
        let (i, j) = (self.current.index(), event.index());
        self.matrix[i][j].to
    }

    /// Returns a reference to the current state.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    /// # #[derive(Debug, Clone, Copy, Default, PartialEq)]
    /// # enum S { #[default] A, B }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    /// let sm = StateMachineBuilder::<S, E, 2, 1>::new()
    ///     .initial(S::A)
    ///     .transition(S::A, E::X, S::B)
    ///     .transition(S::B, E::X, S::A)
    ///     .build()
    ///     .unwrap();
    ///
    /// assert_eq!(sm.current(), &S::A);
    /// ```
    #[inline]
    pub const fn current(&self) -> &S {
        &self.current
    }
}

/// Builder for constructing and validating state machines.
///
/// The builder pattern ensures all transitions are defined before the state machine is created.
/// Validation occurs at build time to catch configuration errors early.
///
/// # Type Parameters
///
/// - `S`: The state type implementing [`States`]
/// - `E`: The event type implementing [`Events`]
/// - `NS`: The total number of states (const generic)
/// - `NE`: The total number of events (const generic)
///
/// # Example
///
/// ```rust
/// use tinystate::StateMachineBuilder;
/// # use tinystate::{States, Events};
/// # #[derive(Debug, Clone, Copy, Default)]
/// # enum S { #[default] A, B }
/// # impl States for S {
/// #     fn index(&self) -> usize { *self as usize }
/// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
/// # }
/// # #[derive(Debug, Clone, Copy)]
/// # enum E { X }
/// # impl Events for E {
/// #     fn index(&self) -> usize { 0 }
/// #     fn from_index(_: usize) -> Self { Self::X }
/// # }
///
/// let sm = StateMachineBuilder::<S, E, 2, 1>::new()
///     .initial(S::A)
///     .transition(S::A, E::X, S::B)
///     .transition(S::B, E::X, S::A)
///     .build()
///     .unwrap();
/// ```
pub struct StateMachineBuilder<S: States, E: Events, const NS: usize, const NE: usize> {
    matrix: TransitionMatrix<S, NS, NE>,
    defined: [[bool; NE]; NS],
    initial: Option<S>,
    _d: PhantomData<E>,
}

impl<S: States, E: Events, const NS: usize, const NE: usize> StateMachineBuilder<S, E, NS, NE> {
    /// Creates a new state machine builder.
    ///
    /// All transitions are initially undefined and must be configured before calling [`build`](Self::build).
    ///
    /// # Example
    ///
    /// ```rust
    /// use tinystate::StateMachineBuilder;
    /// # use tinystate::{States, Events};
    /// # #[derive(Debug, Clone, Copy, Default)]
    /// # enum S { #[default] A }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::A }
    /// # }
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    ///
    /// let builder = StateMachineBuilder::<S, E, 1, 1>::new();
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self {
            matrix: TransitionMatrix::new([[Transition::default(); NE]; NS]),
            defined: [[false; NE]; NS],
            initial: None,
            _d: PhantomData,
        }
    }

    /// Sets the initial state of the state machine.
    ///
    /// This must be called before building the state machine.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    /// # #[derive(Debug, Clone, Copy, Default)]
    /// # enum S { #[default] A, B }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    /// let builder = StateMachineBuilder::<S, E, 2, 1>::new()
    ///     .initial(S::A);
    /// ```
    #[must_use]
    pub const fn initial(mut self, state: S) -> Self {
        self.initial = Some(state);
        self
    }

    /// Adds a single state transition.
    ///
    /// Defines that when in `from` state and `event` occurs, transition to `to` state.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    ///
    /// # #[derive(Debug, Clone, Copy, Default)]
    /// # enum S { #[default] A, B }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    ///
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    ///
    /// let builder = StateMachineBuilder::<S, E, 2, 1>::new()
    ///     .transition(S::A, E::X, S::B);
    /// ```
    #[must_use]
    pub fn transition(mut self, from: S, event: E, to: S) -> Self {
        let (i, j) = (from.index(), event.index());

        self.matrix[i][j].to = to;
        self.defined[i][j] = true;
        self
    }

    /// Adds a state transition with an associated cost.
    ///
    /// Only available with the `costs` feature enabled.
    ///
    /// # Feature Flag
    ///
    /// This method requires the `costs` feature to be enabled.
    #[must_use]
    #[cfg(feature = "costs")]
    pub fn transition_cost(mut self, from: S, cost: f32, event: E, to: S) -> Self {
        let (i, j) = (from.index(), event.index());
        let t = &mut self.matrix[i][j];

        self.defined[i][j] = true;

        t.to = to;
        t.cost = cost;

        self
    }

    /// Adds multiple transitions from the same source state.
    ///
    /// Convenient for defining all outgoing transitions from a state at once.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    ///
    /// # #[derive(Debug, Clone, Copy, Default)]
    /// # enum S { #[default] A, B, C }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, 1 => Self::B, _ => Self::C } }
    /// # }
    ///
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X, Y }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::X, _ => Self::Y } }
    /// # }
    ///
    /// let builder = StateMachineBuilder::<S, E, 3, 2>::new()
    ///     .transitions_from(S::A, &[(E::X, S::B), (E::Y, S::C)]);
    /// ```
    #[must_use]
    pub fn transitions_from(mut self, from: S, transitions: &[(E, S)]) -> Self {
        let i = from.index();

        for &(event, to) in transitions {
            let j = event.index();

            self.matrix[i][j].to = to;
            self.defined[i][j] = true;
        }

        self
    }

    /// Adds a self-loop transition where a state transitions back to itself.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    ///
    /// # #[derive(Debug, Clone, Copy, Default)]
    /// # enum S { #[default] A }
    ///
    /// # impl States for S {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::A }
    /// # }
    ///
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    ///
    /// let builder = StateMachineBuilder::<S, E, 1, 1>::new()
    ///     .self_loop(S::A, E::X);
    /// ```
    #[must_use]
    pub fn self_loop(mut self, state: S, event: E) -> Self {
        let (i, j) = (state.index(), event.index());

        self.matrix[i][j].to = state;
        self.defined[i][j] = true;
        self
    }

    /// Adds a self-loop transition with an associated cost.
    ///
    /// Only available with the `costs` feature enabled.
    ///
    /// # Feature Flag
    ///
    /// This method requires the `costs` feature to be enabled.
    #[must_use]
    #[cfg(feature = "costs")]
    pub fn self_loop_cost(mut self, state: S, event: S, cost: f32) -> Self {
        let (i, j) = (state.index(), event.index());
        let t = &mut self.matrix[i][j];

        self.defined[i][j] = true;

        t.to = state;
        t.cost = cost;

        self
    }

    fn validate_dimensions() -> Result<(), ValidationError<S, E>> {
        for i in 0..NS {
            let state = S::from_index(i);

            if state.index() != i {
                return Err(ValidationError::InvalidStateIndex {
                    expected: i,
                    got: state.index(),
                });
            }
        }

        for j in 0..NE {
            let event = E::from_index(j);

            if event.index() != j {
                return Err(ValidationError::InvalidEventIndex {
                    expected: j,
                    got: event.index(),
                });
            }
        }

        Ok(())
    }

    fn validated(self) -> Result<Self, ValidationError<S, E>> {
        Self::validate_dimensions()?;

        for i in 0..NS {
            for j in 0..NE {
                if !self.defined[i][j] {
                    return Err(ValidationError::UndefinedTransition {
                        from: S::from_index(i),
                        event: E::from_index(j),
                    });
                }
            }
        }

        Ok(self)
    }

    /// Builds and validates the state machine.
    ///
    /// Returns an error if:
    /// - The initial state is not set
    /// - Any transition is undefined
    /// - State or event indices are invalid
    ///
    /// # Errors
    ///
    /// Returns a [`ValidationError`] if the state machine configuration is invalid.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinystate::{StateMachineBuilder, States, Events};
    /// # #[derive(Debug, Clone, Copy, Default)]
    /// # enum S { #[default] A, B }
    /// # impl States for S {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    ///
    /// # #[derive(Debug, Clone, Copy)]
    /// # enum E { X }
    /// # impl Events for E {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::X }
    /// # }
    ///
    /// let result = StateMachineBuilder::<S, E, 2, 1>::new()
    ///     .initial(S::A)
    ///     .transition(S::A, E::X, S::B)
    ///     .transition(S::B, E::X, S::A)
    ///     .build();
    ///
    /// assert!(result.is_ok());
    /// ```
    pub fn build(self) -> Result<StateMachine<S, E, NS, NE>, ValidationError<S, E>> {
        let b = self.validated()?;
        let initial = b.initial.ok_or(ValidationError::NoInitialState::<S, E>)?;

        Ok(StateMachine::new(initial, b.matrix))
    }
}

impl<S: States, E: Events, const NS: usize, const NE: usize> Default
    for StateMachineBuilder<S, E, NS, NE>
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq, States)]
    enum TrafficLightState {
        Red,
        Yellow,
        Green,
    }

    #[derive(Debug, PartialEq, Events)]
    enum TrafficLightEvent {
        Timer,
    }

    #[test]
    fn test_traffic_light() {
        let mut sm = StateMachineBuilder::<TrafficLightState, TrafficLightEvent, 3, 1>::new()
            .initial(TrafficLightState::Red)
            .transition(
                TrafficLightState::Red,
                TrafficLightEvent::Timer,
                TrafficLightState::Green,
            )
            .transition(
                TrafficLightState::Green,
                TrafficLightEvent::Timer,
                TrafficLightState::Yellow,
            )
            .transition(
                TrafficLightState::Yellow,
                TrafficLightEvent::Timer,
                TrafficLightState::Red,
            )
            .build()
            .unwrap();

        assert_eq!(*sm.current(), TrafficLightState::Red);

        sm.trigger(TrafficLightEvent::Timer);
        assert_eq!(*sm.current(), TrafficLightState::Green);

        sm.trigger(TrafficLightEvent::Timer);
        assert_eq!(*sm.current(), TrafficLightState::Yellow);

        sm.trigger(TrafficLightEvent::Timer);
        assert_eq!(*sm.current(), TrafficLightState::Red);
    }

    #[derive(Debug, PartialEq, States)]
    enum DoorState {
        Closed,
        Open,
        Locked,
    }

    #[derive(Debug, PartialEq, Events)]
    enum DoorEvent {
        Push,
        Pull,
        Lock,
        Unlock,
    }

    #[test]
    fn test_door_with_multiple_events() {
        let mut sm = StateMachineBuilder::<DoorState, DoorEvent, 3, 4>::new()
            .initial(DoorState::Closed)
            // From Closed
            .transition(DoorState::Closed, DoorEvent::Push, DoorState::Open)
            .transition(DoorState::Closed, DoorEvent::Pull, DoorState::Closed)
            .transition(DoorState::Closed, DoorEvent::Lock, DoorState::Locked)
            .transition(DoorState::Closed, DoorEvent::Unlock, DoorState::Closed)
            // From Open
            .transition(DoorState::Open, DoorEvent::Push, DoorState::Open)
            .transition(DoorState::Open, DoorEvent::Pull, DoorState::Closed)
            .transition(DoorState::Open, DoorEvent::Lock, DoorState::Open)
            .transition(DoorState::Open, DoorEvent::Unlock, DoorState::Open)
            // From Locked
            .self_loop(DoorState::Locked, DoorEvent::Push)
            .self_loop(DoorState::Locked, DoorEvent::Pull)
            .self_loop(DoorState::Locked, DoorEvent::Lock)
            .transition(DoorState::Locked, DoorEvent::Unlock, DoorState::Closed)
            .build()
            .unwrap();

        assert_eq!(*sm.current(), DoorState::Closed);

        sm.trigger(DoorEvent::Push);
        assert_eq!(*sm.current(), DoorState::Open);

        sm.trigger(DoorEvent::Pull);
        assert_eq!(*sm.current(), DoorState::Closed);

        sm.trigger(DoorEvent::Lock);
        assert_eq!(*sm.current(), DoorState::Locked);

        sm.trigger(DoorEvent::Push); // Should stay locked
        assert_eq!(*sm.current(), DoorState::Locked);

        sm.trigger(DoorEvent::Unlock);
        assert_eq!(*sm.current(), DoorState::Closed);

        sm.trigger(DoorEvent::Push);
        assert_eq!(*sm.current(), DoorState::Open);
    }

    #[test]
    fn test_can_trigger() {
        let sm = StateMachineBuilder::<TrafficLightState, TrafficLightEvent, 3, 1>::new()
            .initial(TrafficLightState::Red)
            .transition(
                TrafficLightState::Red,
                TrafficLightEvent::Timer,
                TrafficLightState::Green,
            )
            .transition(
                TrafficLightState::Green,
                TrafficLightEvent::Timer,
                TrafficLightState::Yellow,
            )
            .transition(
                TrafficLightState::Yellow,
                TrafficLightEvent::Timer,
                TrafficLightState::Red,
            )
            .build()
            .unwrap();

        // Should return true because Timer causes a state change from Red to Green
        assert!(sm.can_trigger(TrafficLightEvent::Timer));
    }

    #[test]
    fn test_can_trigger_self_loop() {
        let sm = StateMachineBuilder::<DoorState, DoorEvent, 3, 4>::new()
            .initial(DoorState::Locked)
            .self_loop(DoorState::Locked, DoorEvent::Push)
            .transition(DoorState::Locked, DoorEvent::Pull, DoorState::Locked)
            .transition(DoorState::Locked, DoorEvent::Lock, DoorState::Locked)
            .transition(DoorState::Locked, DoorEvent::Unlock, DoorState::Closed)
            .transition(DoorState::Closed, DoorEvent::Push, DoorState::Open)
            .transition(DoorState::Closed, DoorEvent::Pull, DoorState::Closed)
            .transition(DoorState::Closed, DoorEvent::Lock, DoorState::Locked)
            .transition(DoorState::Closed, DoorEvent::Unlock, DoorState::Closed)
            .transition(DoorState::Open, DoorEvent::Push, DoorState::Open)
            .transition(DoorState::Open, DoorEvent::Pull, DoorState::Closed)
            .transition(DoorState::Open, DoorEvent::Lock, DoorState::Open)
            .transition(DoorState::Open, DoorEvent::Unlock, DoorState::Open)
            .build()
            .unwrap();

        // Should return false because Push causes a self-loop (no state change)
        assert!(!sm.can_trigger(DoorEvent::Push));

        // Should return true because Unlock causes a state change from Locked to Closed
        assert!(sm.can_trigger(DoorEvent::Unlock));
    }

    #[test]
    fn test_trigger_if() {
        let mut sm = StateMachineBuilder::<DoorState, DoorEvent, 3, 4>::new()
            .initial(DoorState::Closed)
            .transition(DoorState::Closed, DoorEvent::Push, DoorState::Open)
            .transition(DoorState::Closed, DoorEvent::Pull, DoorState::Closed)
            .transition(DoorState::Closed, DoorEvent::Lock, DoorState::Locked)
            .transition(DoorState::Closed, DoorEvent::Unlock, DoorState::Closed)
            .transition(DoorState::Open, DoorEvent::Push, DoorState::Open)
            .transition(DoorState::Open, DoorEvent::Pull, DoorState::Closed)
            .transition(DoorState::Open, DoorEvent::Lock, DoorState::Open)
            .transition(DoorState::Open, DoorEvent::Unlock, DoorState::Open)
            .self_loop(DoorState::Locked, DoorEvent::Push)
            .self_loop(DoorState::Locked, DoorEvent::Pull)
            .self_loop(DoorState::Locked, DoorEvent::Lock)
            .transition(DoorState::Locked, DoorEvent::Unlock, DoorState::Closed)
            .build()
            .unwrap();

        // Trigger only if door is closed
        let triggered = sm.trigger_if(DoorEvent::Push, |state| *state == DoorState::Closed);
        assert!(triggered);
        assert_eq!(*sm.current(), DoorState::Open);

        // Try to lock, but only if door is closed (it's open, so shouldn't trigger)
        let triggered = sm.trigger_if(DoorEvent::Lock, |state| *state == DoorState::Closed);
        assert!(!triggered);
        assert_eq!(*sm.current(), DoorState::Open); // Still open
    }

    #[test]
    fn test_try_trigger() {
        let mut sm = StateMachineBuilder::<DoorState, DoorEvent, 3, 4>::new()
            .initial(DoorState::Locked)
            .self_loop(DoorState::Locked, DoorEvent::Push)
            .transition(DoorState::Locked, DoorEvent::Pull, DoorState::Locked)
            .transition(DoorState::Locked, DoorEvent::Lock, DoorState::Locked)
            .transition(DoorState::Locked, DoorEvent::Unlock, DoorState::Closed)
            .transition(DoorState::Closed, DoorEvent::Push, DoorState::Open)
            .transition(DoorState::Closed, DoorEvent::Pull, DoorState::Closed)
            .transition(DoorState::Closed, DoorEvent::Lock, DoorState::Locked)
            .transition(DoorState::Closed, DoorEvent::Unlock, DoorState::Closed)
            .transition(DoorState::Open, DoorEvent::Push, DoorState::Open)
            .transition(DoorState::Open, DoorEvent::Pull, DoorState::Closed)
            .transition(DoorState::Open, DoorEvent::Lock, DoorState::Open)
            .transition(DoorState::Open, DoorEvent::Unlock, DoorState::Open)
            .build()
            .unwrap();

        // Try to push (self-loop, should return Err)
        let result = sm.try_trigger(DoorEvent::Push);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), DoorState::Locked);

        // Try to unlock (state change, should return Ok)
        let result = sm.try_trigger(DoorEvent::Unlock);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), DoorState::Closed);
    }

    #[test]
    fn test_next_state() {
        let sm = StateMachineBuilder::<TrafficLightState, TrafficLightEvent, 3, 1>::new()
            .initial(TrafficLightState::Red)
            .transition(
                TrafficLightState::Red,
                TrafficLightEvent::Timer,
                TrafficLightState::Green,
            )
            .transition(
                TrafficLightState::Green,
                TrafficLightEvent::Timer,
                TrafficLightState::Yellow,
            )
            .transition(
                TrafficLightState::Yellow,
                TrafficLightEvent::Timer,
                TrafficLightState::Red,
            )
            .build()
            .unwrap();

        // Check what the next state would be without actually transitioning
        let next = sm.next_state(TrafficLightEvent::Timer);
        assert_eq!(next, TrafficLightState::Green);

        // Current state should still be Red
        assert_eq!(*sm.current(), TrafficLightState::Red);
    }
}
