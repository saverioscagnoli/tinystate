//! Builder validation: every `BuildError` path, plus the cases that must build.

use tinystate::BuildError;
use tinystate::Events;
use tinystate::States;
use tinystate::machine;

#[derive(States)]
#[derive(Debug, Clone, Copy, PartialEq)]
enum S {
    A,
    B,
    C,
}

#[derive(Events)]
#[derive(Debug, Clone, Copy)]
// Nothing here triggers, so the variants are only ever named as tags.
#[allow(dead_code)]
enum E {
    Go,
    Stop,
}

#[test]
fn missing_initial_state() {
    let err = machine!(S, E)
        .transition(STag::A, ETag::Go, S::B)
        .transition(STag::B, ETag::Go, S::C)
        .build()
        .err();

    assert_eq!(err, Some(BuildError::NoInitialState));
}

#[test]
fn duplicate_cell() {
    let err = machine!(S, E)
        .initial(S::A)
        .transition(STag::A, ETag::Go, S::B)
        .transition(STag::A, ETag::Go, S::C)
        .build()
        .err();

    assert_eq!(
        err,
        Some(BuildError::Duplicate {
            state: "A",
            event: "Go"
        })
    );
}

#[test]
fn modifier_before_any_transition() {
    let err = machine!(S, E)
        .initial(S::A)
        .guard(|_: &(), _: &S, _: &E| true)
        .build()
        .err();

    assert_eq!(err, Some(BuildError::ModifierWithoutTransition));
}

#[test]
fn unreachable_state() {
    // C is never the target of anything, and is not the initial state.
    let err = machine!(S, E)
        .initial(S::A)
        .transition(STag::A, ETag::Go, S::B)
        .transition(STag::C, ETag::Go, S::B)
        .build()
        .err();

    assert_eq!(err, Some(BuildError::Unreachable { state: "C" }));
}

#[test]
fn self_loop_does_not_reach_anything_new() {
    let err = machine!(S, E)
        .initial(S::A)
        .self_loop(STag::A, ETag::Go)
        .build()
        .err();

    assert_eq!(err, Some(BuildError::Unreachable { state: "B" }));
}

#[test]
fn terminal_states_are_allowed() {
    // C has no way out. That is a legal accepting state, not an error.
    let m = machine!(S, E)
        .initial(S::A)
        .transition(STag::A, ETag::Go, S::B)
        .transition(STag::B, ETag::Go, S::C)
        .build();

    assert!(m.is_ok());
}

#[test]
fn dynamic_action_suppresses_the_reachability_check() {
    // A `Run` may return any state, so unreachability cannot be proven and
    // must not be reported.
    let m = machine!(S, E)
        .initial(S::A)
        .action(STag::A, ETag::Go, |_: &mut (), _: &S, _: &E| Some(S::C))
        .build();

    assert!(m.is_ok());
}

#[test]
fn reachability_follows_a_chain_through_every_event() {
    let m = machine!(S, E)
        .initial(S::A)
        .transition(STag::A, ETag::Go, S::B)
        .transition(STag::B, ETag::Stop, S::C)
        .build();

    assert!(m.is_ok());
}
