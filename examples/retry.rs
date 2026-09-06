//! An HTTP fetch with retry and exponential backoff.
//!
//! Shows the dynamic path of the API: states carry payloads, and `action`
//! transitions compute the next state from the current one, the event, and
//! the context.

use tinystate::Events;
use tinystate::States;
use tinystate::machine;

#[derive(States)]
#[derive(Debug, Clone)]
enum Fetch {
    Idle,
    Requesting { attempt: u32 },
    Waiting { attempt: u32, left_ms: u32 },
    Done(u16),
    Failed(&'static str),
}

#[derive(Events)]
#[derive(Debug, Clone, Copy)]
enum Wire {
    Start,
    Response(u16),
    Timeout,
    Tick(u32),
    Reset,
}

#[derive(Default)]
struct Client {
    /// Requests we are still allowed to put on the wire.
    budget: u32,
    sent: u32,
}

const MAX_ATTEMPTS: u32 = 3;

/// 200ms, 400ms, 800ms, ...
fn backoff_ms(attempt: u32) -> u32 {
    200 * (1 << (attempt - 1))
}

/// Retry if we have attempts left, otherwise give up with `why`.
fn retry_or_fail(attempt: u32, why: &'static str) -> Fetch {
    if attempt < MAX_ATTEMPTS {
        Fetch::Waiting {
            attempt,
            left_ms: backoff_ms(attempt),
        }
    } else {
        Fetch::Failed(why)
    }
}

fn send(c: &mut Client, _: &Fetch, _: &Wire) -> Option<Fetch> {
    c.budget -= 1;
    c.sent += 1;
    Some(Fetch::Requesting { attempt: 1 })
}

fn classify(_: &mut Client, s: &Fetch, e: &Wire) -> Option<Fetch> {
    let (Fetch::Requesting { attempt }, Wire::Response(code)) = (s, e) else {
        return None;
    };

    Some(match code {
        200..=299 => Fetch::Done(*code),
        // Server-side hiccup: worth another go.
        500..=599 => retry_or_fail(*attempt, "server error"),
        // Anything else is our fault; retrying will not help.
        _ => Fetch::Failed("client error"),
    })
}

fn on_timeout(_: &mut Client, s: &Fetch, _: &Wire) -> Option<Fetch> {
    let Fetch::Requesting { attempt } = s else {
        return None;
    };
    Some(retry_or_fail(*attempt, "timed out"))
}

fn tick(c: &mut Client, s: &Fetch, e: &Wire) -> Option<Fetch> {
    let (Fetch::Waiting { attempt, left_ms }, Wire::Tick(dt)) = (s, e) else {
        return None;
    };

    // Still cooling down: stay put with a shorter timer.
    if let Some(rest) = left_ms.checked_sub(*dt).filter(|r| *r > 0) {
        return Some(Fetch::Waiting {
            attempt: *attempt,
            left_ms: rest,
        });
    }

    if c.budget == 0 {
        return Some(Fetch::Failed("out of budget"));
    }

    c.budget -= 1;
    c.sent += 1;
    Some(Fetch::Requesting {
        attempt: attempt + 1,
    })
}

fn main() {
    let mut req = machine!(Fetch, Wire, Client { budget: 3, sent: 0 })
        .initial(Fetch::Idle)
        // Only start if we have budget left.
        .action(FetchTag::Idle, WireTag::Start, send)
        .guard(|c: &Client, _, _| c.budget > 0)
        .action(FetchTag::Requesting, WireTag::Response, classify)
        .action(FetchTag::Requesting, WireTag::Timeout, on_timeout)
        .action(FetchTag::Waiting, WireTag::Tick, tick)
        // Terminal states need a way out, otherwise `build` rejects them as
        // dead ends.
        .transition(FetchTag::Done, WireTag::Reset, Fetch::Idle)
        .transition(FetchTag::Failed, WireTag::Reset, Fetch::Idle)
        .build()
        .unwrap();

    let script = [
        Wire::Timeout,       // NoTransition: Idle ignores wire traffic
        Wire::Start,         // -> Requesting { attempt: 1 }
        Wire::Timeout,       // -> Waiting { attempt: 1, left_ms: 200 }
        Wire::Tick(150),     // -> Waiting { left_ms: 50 }
        Wire::Tick(150),     // -> Requesting { attempt: 2 }
        Wire::Response(503), // -> Waiting { attempt: 2, left_ms: 400 }
        Wire::Tick(400),     // -> Requesting { attempt: 3 }
        Wire::Response(200), // -> Done(200)
    ];

    for e in script {
        let out = req.trigger(e);
        println!(
            "{:<16} {:<13} {:?}",
            format!("{e:?}"),
            format!("{out:?}"),
            req.current()
        );
    }

    if let Fetch::Done(code) = req.current() {
        println!("\nstatus {code} after {} requests", req.context().sent);
    }
    req.trigger(Wire::Reset);

    // The same machine, driven into the give-up path. Top the budget back up
    // through the context first.
    println!("\n--- exhausting the retries ---");
    req.context_mut().budget = 5;
    req.trigger(Wire::Start);
    for _ in 0..MAX_ATTEMPTS {
        req.trigger(Wire::Response(500));
        req.trigger(Wire::Tick(10_000));
    }

    match req.current() {
        Fetch::Failed(why) => println!("gave up: {why}"),
        other => println!("unexpected: {other:?}"),
    }
    println!("budget left: {}", req.context().budget);

    // Payload states are not part of the table: only the variant is.
    assert!(!req.is_fully_static());
}
