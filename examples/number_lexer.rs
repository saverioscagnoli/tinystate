//! A JSON-style number recogniser, written as a DFA.
//!
//! Every edge is static, so the machine is really just a table: the example
//! ends by dumping it as Graphviz. Uses the context-free form of `machine!`.

use tinystate::Events;
use tinystate::Outcome;
use tinystate::StateMachine;
use tinystate::States;
use tinystate::machine;

#[derive(States)]
#[derive(Debug, Clone, Copy)]
enum Lex {
    Start,
    Sign,
    Int,
    /// Saw a `.`, still needs at least one digit.
    Point,
    Frac,
    /// Saw an `e`, still needs a sign or a digit.
    Exp,
    ExpSign,
    ExpDigits,
    Accept,
}

#[derive(Events)]
#[derive(Debug, Clone, Copy)]
enum Tok {
    Digit,
    Sign,
    Point,
    Exp,
    End,
}

/// Characters we know how to feed the machine. Anything else is junk.
fn classify(c: char) -> Option<Tok> {
    match c {
        '0'..='9' => Some(Tok::Digit),
        '+' | '-' => Some(Tok::Sign),
        '.' => Some(Tok::Point),
        'e' | 'E' => Some(Tok::Exp),
        _ => None,
    }
}

type Dfa = StateMachine<Lex, Tok, { Lex::COUNT }, { Tok::COUNT }, ()>;

/// The machine has no way to rewind, so each input gets a fresh one.
fn dfa() -> Dfa {
    machine!(Lex, Tok)
        .initial(Lex::Start)
        .transition(LexTag::Start, TokTag::Sign, Lex::Sign)
        .transition(LexTag::Start, TokTag::Digit, Lex::Int)
        .transition(LexTag::Sign, TokTag::Digit, Lex::Int)
        .self_loop(LexTag::Int, TokTag::Digit)
        .transition(LexTag::Int, TokTag::Point, Lex::Point)
        .transition(LexTag::Int, TokTag::Exp, Lex::Exp)
        .transition(LexTag::Int, TokTag::End, Lex::Accept)
        .transition(LexTag::Point, TokTag::Digit, Lex::Frac)
        .self_loop(LexTag::Frac, TokTag::Digit)
        .transition(LexTag::Frac, TokTag::Exp, Lex::Exp)
        .transition(LexTag::Frac, TokTag::End, Lex::Accept)
        .transition(LexTag::Exp, TokTag::Sign, Lex::ExpSign)
        .transition(LexTag::Exp, TokTag::Digit, Lex::ExpDigits)
        .transition(LexTag::ExpSign, TokTag::Digit, Lex::ExpDigits)
        .self_loop(LexTag::ExpDigits, TokTag::Digit)
        .transition(LexTag::ExpDigits, TokTag::End, Lex::Accept)
        .self_loop(LexTag::Accept, TokTag::End)
        .build()
        .unwrap()
}

fn lex(input: &str) -> Result<(), String> {
    let mut m = dfa();

    for (i, c) in input.chars().enumerate() {
        let Some(tok) = classify(c) else {
            return Err(format!("unexpected {c:?} at {i}"));
        };

        if m.trigger(tok) == Outcome::NoTransition {
            return Err(format!(
                "{c:?} not allowed at {i}, in {}",
                m.current().name()
            ));
        }
    }

    match m.trigger(Tok::End) {
        Outcome::NoTransition => Err(format!("input ends early, in {}", m.current().name())),
        _ => Ok(()),
    }
}

fn main() {
    for input in [
        "0", "-42", "3.14", "-0.5e-10", "6E+23", "", "1.", ".5", "1e", "1.2.3", "12x",
    ] {
        let shown = format!("{input:?}");
        match lex(input) {
            Ok(()) => println!("{shown:>10}  ok"),
            Err(e) => println!("{shown:>10}  {e}"),
        }
    }

    // Which characters could legally come next, halfway through a number?
    let mut m = dfa();
    m.trigger(Tok::Digit);

    let next: Vec<&str> = [Tok::Digit, Tok::Sign, Tok::Point, Tok::Exp, Tok::End]
        .iter()
        .filter(|t| m.can_trigger(t))
        .map(|t| t.name())
        .collect();

    println!("\nafter one digit, in {}: {:?}", m.current().name(), next);

    assert!(m.is_fully_static());
    println!("\ndigraph numbers {{");

    for (si, ei, di) in m.edges() {
        println!(
            "  {} -> {} [label=\"{}\"];",
            Lex::NAMES[si],
            Lex::NAMES[di],
            Tok::NAMES[ei]
        );
    }

    println!("}}");
}
