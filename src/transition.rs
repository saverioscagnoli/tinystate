//! Transition types and transition matrix implementation.
//!
//! This module provides the core data structures for representing state transitions
//! and organizing them in a matrix for efficient lookups.

use core::ops::Index;
use core::ops::IndexMut;

use crate::States;

/// A single state transition.
///
/// Represents a transition from one state to another, optionally with an associated cost.
///
/// # Example
///
/// ```rust
/// use tinystate::Transition;
/// # use tinystate::States;
/// # #[derive(Debug, Clone, Copy, Default)]
/// # enum MyState { #[default] A, B }
/// # impl States for MyState {
/// #     fn index(&self) -> usize { *self as usize }
/// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
/// # }
///
/// let transition = Transition::new(MyState::B);
/// ```
#[derive(Debug, Clone, Copy)]
#[derive(Default)]
pub struct Transition<S: States> {
    /// The destination state of this transition.
    pub to: S,

    /// The cost associated with this transition (requires `costs` feature).
    #[cfg(feature = "costs")]
    pub cost: f32,
}

impl<S: States> Transition<S> {
    /// Creates a new transition to the specified state.
    ///
    /// # Example
    ///
    /// ```rust
    /// use tinystate::Transition;
    /// # use tinystate::States;
    /// # #[derive(Debug, Clone, Copy, Default)]
    /// # enum MyState { #[default] A, B }
    /// # impl States for MyState {
    /// #     fn index(&self) -> usize { *self as usize }
    /// #     fn from_index(i: usize) -> Self { match i { 0 => Self::A, _ => Self::B } }
    /// # }
    ///
    /// let transition = Transition::new(MyState::B);
    /// ```
    pub const fn new(to: S) -> Self {
        Self {
            to,
            #[cfg(feature = "costs")]
            cost: 0.0,
        }
    }

    /// Creates a new transition with an associated cost.
    ///
    /// Only available with the `costs` feature enabled.
    ///
    /// # Feature Flag
    ///
    /// This method requires the `costs` feature to be enabled.
    #[cfg(feature = "costs")]
    pub const fn new_with_cost(to: S, cost: f32) -> Self {
        Self { to, cost }
    }

    /// Sets the cost for this transition (builder pattern).
    ///
    /// Only available with the `costs` feature enabled.
    ///
    /// # Feature Flag
    ///
    /// This method requires the `costs` feature to be enabled.
    #[must_use]
    #[cfg(feature = "costs")]
    pub const fn with_cost(mut self, cost: f32) -> Self {
        self.cost = cost;
        self
    }
}

/// A matrix of state transitions.
///
/// This structure organizes transitions in a 2D matrix where:
/// - Rows represent source states (indexed by state index)
/// - Columns represent events (indexed by event index)
/// - Each cell contains the destination state for that state-event pair
///
/// The matrix allows O(1) lookup of the next state given a current state and event.
///
/// # Type Parameters
///
/// - `S`: The state type implementing [`States`](crate::States)
/// - `NS`: The number of states (rows)
/// - `NE`: The number of events (columns)
#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct TransitionMatrix<S: States, const NS: usize, const NE: usize>([[Transition<S>; NE]; NS]);

impl<S: States, const NS: usize, const NE: usize> TransitionMatrix<S, NS, NE> {
    /// Creates a new transition matrix from a 2D array.
    ///
    /// # Example
    ///
    /// ```rust
    /// use tinystate::{TransitionMatrix, Transition};
    /// # use tinystate::States;
    /// # #[derive(Debug, Clone, Copy, Default)]
    /// # enum MyState { #[default] A }
    /// # impl States for MyState {
    /// #     fn index(&self) -> usize { 0 }
    /// #     fn from_index(_: usize) -> Self { Self::A }
    /// # }
    ///
    /// let matrix = TransitionMatrix::new([[Transition::new(MyState::A); 1]; 1]);
    /// ```
    pub const fn new(arr: [[Transition<S>; NE]; NS]) -> Self {
        Self(arr)
    }
}

impl<S: States, const NS: usize, const NE: usize> Index<usize> for TransitionMatrix<S, NS, NE> {
    type Output = [Transition<S>; NE];

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<S: States, const NS: usize, const NE: usize> IndexMut<usize> for TransitionMatrix<S, NS, NE> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}
