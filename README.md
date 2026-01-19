<div align="center">
  <img src="assets/logo.png" alt="tinystate logo" width="125"/>
  
  # tinystate
  
  [![Crates.io](https://img.shields.io/crates/v/tinystate.svg)](https://crates.io/crates/tinystate) [![Documentation](https://docs.rs/tinystate/badge.svg)](https://docs.rs/tinystate) [![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)
  
</div>

A small, fast and `no_std` finite state machine for Rust.
`tinystate` provides a compile-time validated state machine implementation with zero runtime overhead.

(only when validating it it's O(n^2) at runtime, but since `NE` and `NS` are known it's O(1) :P)

## Contributing

Feel free, I need to make the costs actually useful

## License

MIT
