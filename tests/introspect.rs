//! Reading the table back, resetting, and the derive-generated tag API.

use tinystate::Edge;
use tinystate::Events;
use tinystate::States;
use tinystate::machine;

#[derive(States)]
#[derive(Debug, Clone, Copy, PartialEq)]
enum Light {
    Red,
    Green,
    Blue,
}

#[derive(Events)]
#[derive(Debug, Clone, Copy)]
enum Step {
    Next,
    Back,
}

#[derive(Default, PartialEq, Debug)]
struct Count(u32);

fn build() -> tinystate::StateMachine<Light, Step, { Light::COUNT }, { Step::COUNT }, Count> {
    machine!(Light, Step, Count::default())
        .initial(Light::Red)
        .transition(LightTag::Red, StepTag::Next, Light::Green)
        .cost(1.5)
        .transition(LightTag::Green, StepTag::Next, Light::Blue)
        .self_loop(LightTag::Green, StepTag::Back)
        .transition(LightTag::Blue, StepTag::Back, Light::Red)
        .effect(|c: &mut Count, _: &Light, _: &Step| c.0 += 1)
        .build()
        .unwrap()
}

#[test]
fn edges_lists_every_static_edge() {
    let m = build();
    let got: Vec<_> = m.edges().collect();

    // (state, event, destination), row-major.
    assert_eq!(got, vec![(0, 0, 1), (1, 0, 2), (1, 1, 1), (2, 1, 0)]);
}

#[test]
fn a_self_loop_points_at_its_own_row() {
    let m = build();
    let green = LightTag::Green.index();

    assert_eq!(m.edge(green, StepTag::Back.index()), Some(green));
}

#[test]
fn empty_cells_have_no_edge() {
    let m = build();

    assert_eq!(m.edge(LightTag::Red.index(), StepTag::Back.index()), None);
    assert!(matches!(
        m.edge_kind(LightTag::Red.index(), StepTag::Back.index()),
        Edge::None
    ));
}

#[test]
fn out_of_range_indices_are_not_edges() {
    let m = build();

    assert_eq!(m.edge(99, 0), None);
    assert_eq!(m.edge(0, 99), None);
}

#[test]
fn a_static_machine_is_fully_static() {
    assert!(build().is_fully_static());
}

#[test]
fn an_action_makes_the_machine_dynamic() {
    let m = machine!(Light, Step)
        .initial(Light::Red)
        .action(LightTag::Red, StepTag::Next, |_: &mut (), _: &Light, _: &Step| {
            Some(Light::Green)
        })
        .build()
        .unwrap();

    assert!(!m.is_fully_static());
    assert_eq!(m.edge(LightTag::Red.index(), StepTag::Next.index()), None);
    assert!(matches!(
        m.edge_kind(LightTag::Red.index(), StepTag::Next.index()),
        Edge::Dynamic
    ));
}

#[test]
fn cost_defaults_to_zero_and_is_readable() {
    let m = build();

    assert_eq!(
        m.cost(LightTag::Red.index(), StepTag::Next.index()),
        Some(1.5)
    );
    assert_eq!(
        m.cost(LightTag::Green.index(), StepTag::Next.index()),
        Some(0.0)
    );
    assert_eq!(m.cost(LightTag::Red.index(), StepTag::Back.index()), None);
}

#[test]
fn reset_returns_to_the_initial_state_and_keeps_the_context() {
    let mut m = build();
    m.trigger(Step::Next);
    m.trigger(Step::Next);
    m.trigger(Step::Back);

    assert_eq!(m.context(), &Count(1));
    assert_eq!(*m.current(), Light::Red);

    m.trigger(Step::Next);
    m.reset();

    assert_eq!(*m.current(), Light::Red);
    assert_eq!(*m.initial(), Light::Red);
    assert_eq!(m.context(), &Count(1));
}

#[test]
fn reset_to_jumps_anywhere() {
    let mut m = build();
    m.reset_to(Light::Blue);

    assert_eq!(*m.current(), Light::Blue);
    assert_eq!(*m.initial(), Light::Red);
}

#[test]
fn reset_all_also_clears_the_context() {
    let mut m = build();
    m.trigger(Step::Next);
    m.trigger(Step::Next);
    m.trigger(Step::Back);
    assert_eq!(m.context(), &Count(1));

    m.reset_all();

    assert_eq!(*m.current(), Light::Red);
    assert_eq!(m.context(), &Count(0));
}

#[test]
fn derive_exposes_names_and_indices() {
    assert_eq!(Light::COUNT, 3);
    assert_eq!(Light::NAMES, &["Red", "Green", "Blue"]);
    assert_eq!(Light::TAGS, &LightTag::ALL);

    assert_eq!(LightTag::Blue.index(), 2);
    assert_eq!(LightTag::Blue.name(), "Blue");
    assert_eq!(Light::Blue.index(), 2);
    assert_eq!(Light::Blue.name(), "Blue");
}

#[test]
fn a_value_converts_to_its_tag_by_value_and_by_reference() {
    let owned: LightTag = Light::Green.into();
    let borrowed: LightTag = (&Light::Green).into();

    assert_eq!(owned, LightTag::Green);
    assert_eq!(borrowed, LightTag::Green);
    assert_eq!(Step::Back.index(), StepTag::Back.index());
}
