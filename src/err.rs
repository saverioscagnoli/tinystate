use core::error;
use core::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuildError {
    /// [`StateMachineBuilder::initial`] was never called.
    ///
    /// [`StateMachineBuilder::initial`]: crate::StateMachineBuilder::initial
    NoInitialState,
    /// A modifier (`guard`, `effect`, `cost`) was called before any transition.
    ModifierWithoutTransition,
    /// The same `(state, event)` cell was filled twice.
    Duplicate {
        state: &'static str,
        event: &'static str,
    },
    /// No sequence of events can reach this state from the initial one.
    ///
    /// Only reported for machines whose edges are all static: a dynamic
    /// `action` may return any state, so reachability cannot be proven.
    Unreachable { state: &'static str },
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoInitialState => write!(f, "no initial state set for the machine"),
            Self::ModifierWithoutTransition => {
                write!(f, "modifier called before any transition was added")
            }
            Self::Duplicate { state, event } => {
                write!(f, "duplicate transition for state {state}, event {event}")
            }
            Self::Unreachable { state } => {
                write!(f, "state {state} is unreachable from the initial state")
            }
        }
    }
}

impl error::Error for BuildError {}
