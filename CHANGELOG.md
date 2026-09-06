# 1.0.0 - 2026/09/07

Breaking rewrite of the traits and the builder.

- `States` and `Events` now have a companion `Tag` type. The derive generates
  it for you, so states can carry payloads while the table stays indexed by
  variant.
- Machines are built with the `machine!` macro and a builder:
  `transition`, `self_loop`, `action`, `guard`, `effect`, `cost`.
- `no_std` for real. The crate no longer pulls in `std`.
- New `Outcome::Declined`, for an `action` that returns `None`. It used to be
  reported as `Guarded`.
- Effects only run when the transition actually takes place. `Guarded`,
  `Declined` and `NoTransition` leave the context untouched, and self loops
  run their effect again.
- `BuildError::Unreachable` now means what it says: a state nothing can reach
  from the initial one. It used to flag states with no way *out*, which meant
  terminal states were rejected. They are allowed now.
- Added `reset`, `reset_to`, `reset_all` and `initial`.
- Added the `cost` getter, and `edge`, `edge_kind`, `edges`, `is_fully_static`
  for reading the table back.
- The derive crate is now `tinystate-derive`.
- Added tests and the `turnstile`, `retry` and `number_lexer` examples.

# 0.1.1 - 2026/01/19

Fixed white pixel in the logo
