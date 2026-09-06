use tinystate::Events;
use tinystate::States;
use tinystate::machine;

#[derive(States)]
#[derive(Debug, Clone, Copy)]
enum Hvac {
    Off,
    Idle(f32),
    Heating(f32),
    Cooling(f32),
}

#[derive(Events)]
#[derive(Debug, Clone, Copy)]
enum Signal {
    SetTarget(f32),
    Reading(f32),
    PowerOff,
}

#[derive(Default)]
struct Room {
    temp: f32,
    compressor_starts: u32,
}

const HYST: f32 = 0.5;

fn target_of(s: &Hvac) -> f32 {
    match s {
        Hvac::Off => 20.0,
        Hvac::Idle(t) | Hvac::Heating(t) | Hvac::Cooling(t) => *t,
    }
}

fn set_target(_r: &mut Room, s: &Hvac, e: &Signal) -> Option<Hvac> {
    let Signal::SetTarget(t) = e else { return None };

    if !(5.0..=30.0).contains(t) {
        return None;
    };

    Some(match s {
        Hvac::Off => Hvac::Idle(*t),
        _ => Hvac::Idle(*t),
    })
}

fn regulate(r: &mut Room, s: &Hvac, e: &Signal) -> Option<Hvac> {
    let Signal::Reading(x) = e else { return None };

    r.temp = *x;

    let t = target_of(s);

    Some(if *x < t - HYST {
        r.compressor_starts += 1;
        Hvac::Heating(t)
    } else if *x > t + HYST {
        r.compressor_starts += 1;
        Hvac::Cooling(t)
    } else {
        Hvac::Idle(t)
    })
}

fn main() {
    let mut m = machine!(Hvac, Signal, Room::default())
        .initial(Hvac::Off)
        .action(HvacTag::Off, SignalTag::SetTarget, set_target)
        .action(HvacTag::Idle, SignalTag::SetTarget, set_target)
        .action(HvacTag::Heating, SignalTag::SetTarget, set_target)
        .action(HvacTag::Cooling, SignalTag::SetTarget, set_target)
        .action(HvacTag::Idle, SignalTag::Reading, regulate)
        .action(HvacTag::Heating, SignalTag::Reading, regulate)
        .action(HvacTag::Cooling, SignalTag::Reading, regulate)
        .transition(HvacTag::Idle, SignalTag::PowerOff, Hvac::Off)
        .transition(HvacTag::Heating, SignalTag::PowerOff, Hvac::Off)
        .transition(HvacTag::Cooling, SignalTag::PowerOff, Hvac::Off)
        .build()
        .unwrap();

    for sig in [
        Signal::Reading(18.0), // NoTransition: Off ignores readings
        Signal::SetTarget(21.0),
        Signal::Reading(18.0),   // -> Heating(21.0)
        Signal::Reading(20.8),   // -> Idle(21.0), inside hysteresis
        Signal::SetTarget(99.0), // rejected by range check
        Signal::Reading(23.0),   // -> Cooling(21.0)
        Signal::PowerOff,
    ] {
        let out = m.trigger(sig);
        println!("{out:?} -> {:?}", m.current());
    }

    println!("compressor starts: {}", m.context().compressor_starts);
}
