use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::Data;
use syn::DeriveInput;
use syn::Fields;
use syn::Ident;
use syn::Result;
use syn::parse_macro_input;
use syn::parse_quote;

#[derive(Clone, Copy)]
enum Kind {
    States,
    Events,
}

impl Kind {
    fn path(self) -> TokenStream2 {
        match self {
            Kind::States => quote!(::tinystate::States),
            Kind::Events => quote!(::tinystate::Events),
        }
    }
    fn what(self) -> &'static str {
        match self {
            Kind::States => "States",
            Kind::Events => "Events",
        }
    }
}

#[proc_macro_derive(States, attributes(tinystate))]
pub fn derive_states(input: TokenStream) -> TokenStream {
    run(parse_macro_input!(input as DeriveInput), Kind::States)
}

#[proc_macro_derive(Events, attributes(tinystate))]
pub fn derive_events(input: TokenStream) -> TokenStream {
    run(parse_macro_input!(input as DeriveInput), Kind::Events)
}

fn run(input: DeriveInput, kind: Kind) -> TokenStream {
    expand(input, kind)
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

fn expand(input: DeriveInput, kind: Kind) -> Result<TokenStream2> {
    let name = &input.ident;
    let vis = &input.vis;

    let Data::Enum(data) = &input.data else {
        return Err(syn::Error::new_spanned(
            name,
            format!("#[derive({})] only supports enums", kind.what()),
        ));
    };
    if data.variants.is_empty() {
        return Err(syn::Error::new_spanned(
            name,
            format!("#[derive({})] requires at least one variant", kind.what()),
        ));
    }

    let tag =
        tag_override(&input)?.unwrap_or_else(|| Ident::new(&format!("{name}Tag"), name.span()));

    let count = data.variants.len();
    let idents: Vec<&Ident> = data.variants.iter().map(|v| &v.ident).collect();
    let names: Vec<String> = idents.iter().map(|i| i.to_string()).collect();
    let indices: Vec<usize> = (0..count).collect();

    let to_tag = data.variants.iter().map(|v| {
        let id = &v.ident;
        let pat = match &v.fields {
            Fields::Unit => quote!(Self::#id),
            Fields::Unnamed(..) => quote!(Self::#id(..)),
            Fields::Named(..) => quote!(Self::#id { .. }),
        };
        quote!(#pat => #tag::#id)
    });

    let trait_path = kind.path();
    let (ig, tg, wc) = input.generics.split_for_impl();

    let mut ref_generics = input.generics.clone();
    ref_generics.params.insert(0, parse_quote!('__ts));
    let (rig, ..) = ref_generics.split_for_impl();

    Ok(quote! {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #vis enum #tag { #(#idents),* }

        impl #tag {
            #vis const ALL: [#tag; #count] = [#(#tag::#idents),*];
            #vis const fn name(self) -> &'static str {
                match self { #(#tag::#idents => #names),* }
            }
            #vis const fn index(self) -> usize {
                match self { #(#tag::#idents => #indices),* }
            }
        }

        impl #ig #trait_path for #name #tg #wc {
            type Tag = #tag;
            const COUNT: usize = #count;
            const NAMES: &'static [&'static str] = &[#(#names),*];
            const TAGS: &'static [#tag] = &#tag::ALL;

            fn tag(&self) -> #tag { match self { #(#to_tag),* } }
            fn tag_index(tag: #tag) -> usize { tag.index() }
        }

        impl #ig ::core::convert::From<#name #tg> for #tag #wc {
            fn from(v: #name #tg) -> Self { <#name #tg as #trait_path>::tag(&v) }
        }

        impl #rig ::core::convert::From<&'__ts #name #tg> for #tag #wc {
            fn from(v: &'__ts #name #tg) -> Self { <#name #tg as #trait_path>::tag(v) }
        }
    })
}

fn tag_override(input: &DeriveInput) -> Result<Option<Ident>> {
    let mut found = None;
    for attr in input
        .attrs
        .iter()
        .filter(|a| a.path().is_ident("tinystate"))
    {
        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("tag") {
                found = Some(meta.value()?.parse::<Ident>()?);
                Ok(())
            } else {
                Err(meta.error("unknown attribute; expected `tag = Ident`"))
            }
        })?;
    }
    Ok(found)
}
