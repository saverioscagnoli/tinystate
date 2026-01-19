use tinystate::Events;
use tinystate::StateMachineBuilder;
use tinystate::States;

#[derive(Debug, PartialEq, States)]
enum TrafficLight {
    Red,
    Yellow,
    Green,
}

#[derive(Debug, Events)]
enum Signal {
    Timer,
}

fn main() {
    let mut light = StateMachineBuilder::<TrafficLight, Signal, 3, 1>::new()
        .initial(TrafficLight::Red)
        .transition(TrafficLight::Red, Signal::Timer, TrafficLight::Green)
        .transition(TrafficLight::Green, Signal::Timer, TrafficLight::Yellow)
        .transition(TrafficLight::Yellow, Signal::Timer, TrafficLight::Red)
        .build()
        .unwrap();

    for i in 1..=6 {
        println!("Step {}: {:?}", i, light.current());
        light.trigger(Signal::Timer);
    }

    println!("Final state: {:?}", light.current());
}
