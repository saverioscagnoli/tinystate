//! The classic turnstile: the smallest useful machine.
//!
//! Shows the unit-variant path of the API: `transition`, `self_loop`, `guard`,
//! `effect`, `can_trigger`, and reading back the transition table.

use tinystate::Events;
use tinystate::Outcome;
use tinystate::States;
use tinystate::machine;

#[derive(States)]
#[derive(Debug, Clone, Copy)]
enum Gate {
    Locked,
    Unlocked,
}

#[derive(Events)]
#[derive(Debug, Clone, Copy)]
enum Input {
    Coin,
    Push,
}

/// The venue behind the turnstile.
#[derive(Default)]
struct Venue {
    coins: u32,
    inside: u32,
}

const CAPACITY: u32 = 2;

fn main() {
    let mut gate = machine!(Gate, Input, Venue::default())
        .initial(Gate::Locked)
        // Paying unlocks the gate, as long as there is room left inside.
        .transition(GateTag::Locked, InputTag::Coin, Gate::Unlocked)
        .guard(|v, _, _| v.inside < CAPACITY)
        .effect(|v, _, _| v.coins += 1)
        // Paying twice is the customer's problem, but we still take the coin.
        .self_loop(GateTag::Unlocked, InputTag::Coin)
        .effect(|v, _, _| v.coins += 1)
        // Pushing through re-locks the gate behind you.
        .transition(GateTag::Unlocked, InputTag::Push, Gate::Locked)
        .effect(|v, _, _| v.inside += 1)
        // Pushing a locked gate just rattles it.
        .self_loop(GateTag::Locked, InputTag::Push)
        .build()
        .unwrap();

    for input in [
        Input::Push, // Stayed: rattles
        Input::Coin, // Moved:  -> Unlocked
        Input::Coin, // Stayed: pays twice
        Input::Push, // Moved:  -> Locked, 1 inside
        Input::Coin, // Moved:  -> Unlocked
        Input::Push, // Moved:  -> Locked, 2 inside (full)
        Input::Coin, // Guarded: venue is full
    ] {
        let out = gate.trigger(input);
        println!("{input:?} -> {out:?} ({})", gate.current().name());
    }

    let v = gate.context();
    println!("\ncoins: {}, inside: {}", v.coins, v.inside);
    println!("another coin accepted? {}", gate.can_trigger(&Input::Coin));

    // Every edge here is a plain `Goto`/`SelfLoop`, so the whole table is
    // known without running anything.
    assert!(gate.is_fully_static());
    println!("\ntransition table:");
    for (si, ei, di) in gate.edges() {
        println!(
            "  {:>8} --{}--> {}",
            Gate::NAMES[si],
            Input::NAMES[ei],
            Gate::NAMES[di]
        );
    }

    assert_eq!(gate.trigger(Input::Coin), Outcome::Guarded);
}
