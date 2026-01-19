use tinystate::Events;
use tinystate::StateMachineBuilder;
use tinystate::States;

#[derive(Debug, PartialEq, States)]
enum VendingState {
    Idle,
    Has25Cents,
    Has50Cents,
    Has75Cents,
    ReadyToDispense,
    Dispensing,
}

#[derive(Debug, Events)]
enum VendingEvent {
    Insert25Cents,
    Insert50Cents,
    SelectItem,
    Cancel,
    DispenseComplete,
}

fn main() {
    let mut machine = StateMachineBuilder::<VendingState, VendingEvent, 6, 5>::new()
        .initial(VendingState::Idle)
        .transition(
            VendingState::Idle,
            VendingEvent::Insert25Cents,
            VendingState::Has25Cents,
        )
        .transition(
            VendingState::Idle,
            VendingEvent::Insert50Cents,
            VendingState::Has50Cents,
        )
        .self_loop(VendingState::Idle, VendingEvent::SelectItem)
        .self_loop(VendingState::Idle, VendingEvent::Cancel)
        .self_loop(VendingState::Idle, VendingEvent::DispenseComplete)
        .transition(
            VendingState::Has25Cents,
            VendingEvent::Insert25Cents,
            VendingState::Has50Cents,
        )
        .transition(
            VendingState::Has25Cents,
            VendingEvent::Insert50Cents,
            VendingState::Has75Cents,
        )
        .self_loop(VendingState::Has25Cents, VendingEvent::SelectItem)
        .transition(
            VendingState::Has25Cents,
            VendingEvent::Cancel,
            VendingState::Idle,
        )
        .self_loop(VendingState::Has25Cents, VendingEvent::DispenseComplete)
        .transition(
            VendingState::Has50Cents,
            VendingEvent::Insert25Cents,
            VendingState::Has75Cents,
        )
        .transition(
            VendingState::Has50Cents,
            VendingEvent::Insert50Cents,
            VendingState::ReadyToDispense,
        )
        .self_loop(VendingState::Has50Cents, VendingEvent::SelectItem)
        .transition(
            VendingState::Has50Cents,
            VendingEvent::Cancel,
            VendingState::Idle,
        )
        .self_loop(VendingState::Has50Cents, VendingEvent::DispenseComplete)
        .transition(
            VendingState::Has75Cents,
            VendingEvent::Insert25Cents,
            VendingState::ReadyToDispense,
        )
        .self_loop(VendingState::Has75Cents, VendingEvent::Insert50Cents)
        .self_loop(VendingState::Has75Cents, VendingEvent::SelectItem)
        .transition(
            VendingState::Has75Cents,
            VendingEvent::Cancel,
            VendingState::Idle,
        )
        .self_loop(VendingState::Has75Cents, VendingEvent::DispenseComplete)
        .self_loop(VendingState::ReadyToDispense, VendingEvent::Insert25Cents)
        .self_loop(VendingState::ReadyToDispense, VendingEvent::Insert50Cents)
        .transition(
            VendingState::ReadyToDispense,
            VendingEvent::SelectItem,
            VendingState::Dispensing,
        )
        .transition(
            VendingState::ReadyToDispense,
            VendingEvent::Cancel,
            VendingState::Idle,
        )
        .self_loop(
            VendingState::ReadyToDispense,
            VendingEvent::DispenseComplete,
        )
        .self_loop(VendingState::Dispensing, VendingEvent::Insert25Cents)
        .self_loop(VendingState::Dispensing, VendingEvent::Insert50Cents)
        .self_loop(VendingState::Dispensing, VendingEvent::SelectItem)
        .self_loop(VendingState::Dispensing, VendingEvent::Cancel)
        .transition(
            VendingState::Dispensing,
            VendingEvent::DispenseComplete,
            VendingState::Idle,
        )
        .build()
        .unwrap();

    println!("Vending Machine Simulator");
    println!("Item cost: $1.00\n");

    println!("State: {:?}", machine.current());

    machine.trigger(VendingEvent::Insert25Cents);
    println!("Inserted 25 cents -> State: {:?}", machine.current());

    machine.trigger(VendingEvent::Insert25Cents);
    println!("Inserted 25 cents -> State: {:?}", machine.current());

    machine.trigger(VendingEvent::Insert25Cents);
    println!("Inserted 25 cents -> State: {:?}", machine.current());

    machine.trigger(VendingEvent::Insert25Cents);
    println!("Inserted 25 cents -> State: {:?}", machine.current());

    machine.trigger(VendingEvent::SelectItem);
    println!("Selected item -> State: {:?}", machine.current());

    machine.trigger(VendingEvent::DispenseComplete);
    println!("Dispensed item -> State: {:?}", machine.current());

    println!("\nStarting new transaction...");
    machine.trigger(VendingEvent::Insert50Cents);
    println!("Inserted 50 cents -> State: {:?}", machine.current());

    machine.trigger(VendingEvent::Cancel);
    println!("Cancelled (refund) -> State: {:?}", machine.current());
}
