//! Derive macros for `tinystate`.
//!
//! This crate provides procedural macros to automatically implement the [`States`] and [`Events`]
//! traits for enum types, eliminating boilerplate code.
//!
//! # Usage
//!
//! Enable the `derive` feature in your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! tinystate = { version = "0.1", features = ["derive"] }
//! ```
//!
//! Then derive the traits on your enums:
//!
//! ```rust,ignore
//! use tinystate::{States, Events};
//!
//! #[derive(States)]
//! enum TrafficLight {
//!     Red,
//!     Yellow,
//!     Green,
//! }
//!
//! #[derive(Events)]
//! enum TrafficEvent {
//!     Timer,
//!     Emergency,
//! }
//! ```
//!
//! # Requirements
//!
//! - Both macros only work on enums with unit variants (no fields)
//! - The first variant of a `States` enum becomes the default state
//!
//! [`States`]: https://docs.rs/tinystate/latest/tinystate/trait.States.html
//! [`Events`]: https://docs.rs/tinystate/latest/tinystate/trait.Events.html

use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;
use syn::Data;
use syn::DeriveInput;
use syn::Fields;

/// Derives the `States` trait for an enum.
///
/// This macro automatically implements the `States` trait along with `Default`, `Copy`, and `Clone`.
/// The first variant of the enum becomes the default state.
///
/// # Requirements
///
/// - Can only be derived for enums
/// - All variants must be unit variants (no fields)
///
/// # Generated Implementations
///
/// - `States` - Maps variants to/from indices starting at 0
/// - `Default` - Uses the first variant as the default
/// - `Copy` and `Clone` - Enables efficient copying
///
/// # Examples
///
/// ```rust,ignore
/// use tinystate::States;
///
/// #[derive(States)]
/// enum DoorState {
///     Closed,  // Index 0, also the default
///     Open,    // Index 1
///     Locked,  // Index 2
/// }
///
/// let state = DoorState::default();
/// assert_eq!(state.index(), 0);
/// assert!(matches!(state, DoorState::Closed));
/// ```
///
/// # Panics
///
/// The derive macro will panic at compile time if:
/// - Applied to a struct or union (not an enum)
/// - Any variant has fields (only unit variants are allowed)
///
/// The generated `from_index` method will panic at runtime if called with an invalid index.
#[proc_macro_derive(States)]
pub fn derive_states(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let variants = match &input.data {
        Data::Enum(data_enum) => &data_enum.variants,
        _ => panic!("States can only be derived for enums"),
    };

    // Check that all variants are unit variants (no fields)
    for variant in variants {
        if !matches!(variant.fields, Fields::Unit) {
            panic!("States can only be derived for enums with unit variants (no fields)");
        }
    }

    let variant_names: Vec<_> = variants.iter().map(|v| &v.ident).collect();

    // Generate match arms for index()
    let index_arms = variant_names.iter().enumerate().map(|(i, variant)| {
        quote! {
            #name::#variant => #i,
        }
    });

    // Generate match arms for from_index()
    let from_index_arms = variant_names.iter().enumerate().map(|(i, variant)| {
        quote! {
            #i => #name::#variant,
        }
    });

    // Get the first variant for Default implementation
    let first_variant = &variant_names[0];

    let expanded = quote! {
        impl States for #name {
            fn index(&self) -> usize {
                match self {
                    #(#index_arms)*
                }
            }

            fn from_index(index: usize) -> Self {
                match index {
                    #(#from_index_arms)*
                    _ => panic!("Invalid index {} for {}", index, stringify!(#name)),
                }
            }
        }

        impl Default for #name {
            fn default() -> Self {
                #name::#first_variant
            }
        }

        impl Copy for #name {}

        impl Clone for #name {
            fn clone(&self) -> Self {
                *self
            }
        }
    };

    TokenStream::from(expanded)
}

/// Derives the `Events` trait for an enum.
///
/// This macro automatically implements the `Events` trait along with `Copy` and `Clone`.
/// Unlike `States`, this does not generate a `Default` implementation.
///
/// # Requirements
///
/// - Can only be derived for enums
/// - All variants must be unit variants (no fields)
///
/// # Generated Implementations
///
/// - `Events` - Maps variants to/from indices starting at 0
/// - `Copy` and `Clone` - Enables efficient copying
///
/// # Examples
///
/// ```rust,ignore
/// use tinystate::Events;
///
/// #[derive(Events)]
/// enum DoorEvent {
///     Push,   // Index 0
///     Pull,   // Index 1
///     Lock,   // Index 2
///     Unlock, // Index 3
/// }
///
/// let event = DoorEvent::Lock;
/// assert_eq!(event.index(), 2);
///
/// let reconstructed = DoorEvent::from_index(2);
/// assert_eq!(reconstructed.index(), event.index());
/// ```
///
/// # Panics
///
/// The derive macro will panic at compile time if:
/// - Applied to a struct or union (not an enum)
/// - Any variant has fields (only unit variants are allowed)
///
/// The generated `from_index` method will panic at runtime if called with an invalid index.
#[proc_macro_derive(Events)]
pub fn derive_events(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let variants = match &input.data {
        Data::Enum(data_enum) => &data_enum.variants,
        _ => panic!("Events can only be derived for enums"),
    };

    // Check that all variants are unit variants (no fields)
    for variant in variants {
        if !matches!(variant.fields, Fields::Unit) {
            panic!("Events can only be derived for enums with unit variants (no fields)");
        }
    }

    let variant_names: Vec<_> = variants.iter().map(|v| &v.ident).collect();

    // Generate match arms for index()
    let index_arms = variant_names.iter().enumerate().map(|(i, variant)| {
        quote! {
            #name::#variant => #i,
        }
    });

    // Generate match arms for from_index()
    let from_index_arms = variant_names.iter().enumerate().map(|(i, variant)| {
        quote! {
            #i => #name::#variant,
        }
    });

    let expanded = quote! {
        impl Events for #name {
            fn index(&self) -> usize {
                match self {
                    #(#index_arms)*
                }
            }

            fn from_index(index: usize) -> Self {
                match index {
                    #(#from_index_arms)*
                    _ => panic!("Invalid index {} for {}", index, stringify!(#name)),
                }
            }
        }

        impl Copy for #name {}

        impl Clone for #name {
            fn clone(&self) -> Self {
                *self
            }
        }
    };

    TokenStream::from(expanded)
}
