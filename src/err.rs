//! Error types for state machine validation.
//!
//! This module defines errors that can occur during state machine construction and validation.

use core::error;
use core::fmt;

use crate::Events;
use crate::States;

/// Errors that can occur during state machine validation.
///
/// These errors are returned by [`StateMachineBuilder::build`](crate::StateMachineBuilder::build)
/// when the state machine configuration is invalid.
///
/// # Example
///
/// ```rust
/// use tinystate::{StateMachineBuilder, ValidationError};
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
/// // Missing initial state will cause an error
/// let result = StateMachineBuilder::<S, E, 1, 1>::new()
///     .self_loop(S::A, E::X)
///     .build();
///
/// assert!(result.is_err());
/// ```
#[derive(Debug)]
pub enum ValidationError<S, E> {
    /// A state's index does not match its expected position.
    InvalidStateIndex { expected: usize, got: usize },

    /// An event's index does not match its expected position.
    InvalidEventIndex { expected: usize, got: usize },

    /// No initial state was set before building.
    NoInitialState,

    /// A required state transition was not defined.
    UndefinedTransition { from: S, event: E },
}

impl<S: States + fmt::Debug, E: Events + fmt::Debug> fmt::Display for ValidationError<S, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidStateIndex { expected, got } => {
                write!(f, "Invalid state index! Expected {expected}, got {got}")
            }
            Self::InvalidEventIndex { expected, got } => {
                write!(f, "Invalid event index! Expected {expected}, got {got}")
            }
            Self::NoInitialState => {
                write!(f, "The initial state is not set!")
            }
            Self::UndefinedTransition { from, event } => write!(
                f,
                "There is no transition that goes from state '{from:?}' on event '{event:?}'"
            ),
        }
    }
}

impl<S: States + fmt::Debug, E: Events + fmt::Debug> error::Error for ValidationError<S, E> {}
