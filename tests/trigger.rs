//! The `Outcome` matrix, and when an `effect` is allowed to run.

use tinystate::Events;
use tinystate::Outcome;
use tinystate::StateMachine;
use tinystate::States;
use tinystate::machine;

#[derive(States)]
#[derive(Debug, Clone, Copy, PartialEq)]
enum S {
    Idle,
    Work,
    Done,
}

#[derive(Events)]
#[derive(Debug, Clone, Copy)]
enum E {
    Start,
    Poke,
    Finish,
    Bail,
}

#[derive(Default)]
struct Ctx {
    effects: u32,
    ready: bool,
}

type M = StateMachine<S, E, { S::COUNT }, { E::COUNT }, Ctx>;

fn bump(c: &mut Ctx, _: &S, _: &E) {
    c.effects += 1;
}

fn fsm() -> M {
    machine!(S, E, Ctx::default())
        .initial(S::Idle)
        .transition(STag::Idle, ETag::Start, S::Work)
        .effect(bump)
        .self_loop(STag::Work, ETag::Poke)
        .effect(bump)
        .transition(STag::Work, ETag::Finish, S::Done)
        .guard(|c: &Ctx, _: &S, _: &E| c.ready)
        .effect(bump)
        .action(STag::Work, ETag::Bail, |_: &mut Ctx, _: &S, _: &E| None)
        .effect(bump)
        .build()
        .unwrap()
}

#[test]
fn moved_runs_the_effect() {
    let mut m = fsm();

    assert_eq!(m.trigger(E::Start), Outcome::Moved);
    assert_eq!(*m.current(), S::Work);
    assert_eq!(m.context().effects, 1);
}

#[test]
fn empty_cell_is_no_transition() {
    let mut m = fsm();

    assert_eq!(m.trigger(E::Poke), Outcome::NoTransition);
    assert_eq!(*m.current(), S::Idle);
    assert_eq!(m.context().effects, 0);
}

/// A self loop stays put, but it is still a transition that took place, so
/// its effect must run. Regression: this used to return early and skip it.
#[test]
fn self_loop_stays_and_runs_the_effect() {
    let mut m = fsm();
    m.trigger(E::Start);

    assert_eq!(m.trigger(E::Poke), Outcome::Stayed);
    assert_eq!(*m.current(), S::Work);
    assert_eq!(m.context().effects, 2);

    assert_eq!(m.trigger(E::Poke), Outcome::Stayed);
    assert_eq!(m.context().effects, 3);
}

#[test]
fn guarded_leaves_the_context_untouched() {
    let mut m = fsm();
    m.trigger(E::Start);

    assert_eq!(m.trigger(E::Finish), Outcome::Guarded);
    assert_eq!(*m.current(), S::Work);
    assert_eq!(m.context().effects, 1);
}

#[test]
fn a_passing_guard_lets_the_transition_through() {
    let mut m = fsm();
    m.trigger(E::Start);
    m.context_mut().ready = true;

    assert_eq!(m.trigger(E::Finish), Outcome::Moved);
    assert_eq!(*m.current(), S::Done);
    assert_eq!(m.context().effects, 2);
}

/// An action returning `None` declines, and must not leave the effect applied.
#[test]
fn declined_leaves_the_context_untouched() {
    let mut m = fsm();
    m.trigger(E::Start);

    assert_eq!(m.trigger(E::Bail), Outcome::Declined);
    assert_eq!(*m.current(), S::Work);
    assert_eq!(m.context().effects, 1);
}

#[test]
fn can_trigger_reflects_the_guard() {
    let mut m = fsm();
    m.trigger(E::Start);

    assert!(!m.can_trigger(&E::Finish));
    assert!(m.can_trigger(&E::Poke));
    assert!(!m.can_trigger(&E::Start));

    m.context_mut().ready = true;
    assert!(m.can_trigger(&E::Finish));
}
