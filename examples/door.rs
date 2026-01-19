use tinystate::Events;
use tinystate::StateMachineBuilder;
use tinystate::States;

#[derive(Debug, PartialEq, States)]
enum DoorState {
    Closed,
    Open,
    Locked,
}

#[derive(Debug, PartialEq, Events)]
enum DoorEvent {
    Push,
    Pull,
    Lock,
    Unlock,
}

fn main() {
    let mut sm = StateMachineBuilder::<DoorState, DoorEvent, 3, 4>::new()
        .initial(DoorState::Closed)
        .transition(DoorState::Closed, DoorEvent::Push, DoorState::Open)
        .transition(DoorState::Closed, DoorEvent::Pull, DoorState::Closed)
        .transition(DoorState::Closed, DoorEvent::Lock, DoorState::Locked)
        .transition(DoorState::Closed, DoorEvent::Unlock, DoorState::Closed)
        .transition(DoorState::Open, DoorEvent::Push, DoorState::Open)
        .transition(DoorState::Open, DoorEvent::Pull, DoorState::Closed)
        .transition(DoorState::Open, DoorEvent::Lock, DoorState::Open)
        .transition(DoorState::Open, DoorEvent::Unlock, DoorState::Open)
        .self_loop(DoorState::Locked, DoorEvent::Push)
        .self_loop(DoorState::Locked, DoorEvent::Pull)
        .self_loop(DoorState::Locked, DoorEvent::Lock)
        .transition(DoorState::Locked, DoorEvent::Unlock, DoorState::Closed)
        .build()
        .unwrap();

    println!("Door starts: {:?}", sm.current());

    sm.trigger(DoorEvent::Push);
    println!("After Push: {:?}", sm.current());

    sm.trigger(DoorEvent::Pull);
    println!("After Pull: {:?}", sm.current());

    sm.trigger(DoorEvent::Lock);
    println!("After Lock: {:?}", sm.current());

    sm.trigger(DoorEvent::Push);
    println!("After Push (locked): {:?}", sm.current());

    sm.trigger(DoorEvent::Unlock);
    println!("After Unlock: {:?}", sm.current());

    sm.trigger(DoorEvent::Push);
    println!("After Push: {:?}", sm.current());
}
