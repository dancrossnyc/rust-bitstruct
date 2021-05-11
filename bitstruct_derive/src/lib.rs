use std::{cmp::Ordering, convert::TryInto, ops::Range};

use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    Token,
};

#[proc_macro]
pub fn bitstruct(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(tokens as BitStructInput);
    expand_bitstruct(input)
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

fn expand_bitstruct(input: BitStructInput) -> syn::Result<TokenStream> {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let name = &input.name;
    let raw_vis = &input.raw_vis;
    let raw = &input.raw.as_type();
    let fields = input
        .fields
        .iter()
        .map(|field| expand_field_methods(&input, field))
        .collect::<Result<Vec<TokenStream>, syn::Error>>()?;
    Ok(quote! {
        #(#attrs)*
        #vis struct #name(#raw_vis #raw);
        impl #name {
            #(#fields)*
        }
    })
}

fn expand_field_methods(input: &BitStructInput, field: &FieldDef) -> syn::Result<TokenStream> {
    if field.bits.bit_len() > field.target.bit_len() {
        return Err(syn::Error::new(
            field.name.span(),
            format!(
                "target type {:?} too small to represent {} bits",
                field.target,
                field.bits.bit_len()
            ),
        ));
    }

    let target_ty = field.target.as_type();
    let mask = hexlit(input.raw, field.bits.get_mask());
    let start_bit = hexlit(input.raw, field.bits.0.start.into());
    let mask_and_shift: syn::Expr = syn::parse_quote! {
        ((self.0 & #mask) >> #start_bit)
    };
    let cast: syn::Expr = syn::parse_quote! {
        #mask_and_shift as #target_ty
    };

    let field_attrs = &field.attrs;
    let field_vis = &field.vis;
    let field_name = &field.name;
    Ok(quote! {
        #(#field_attrs)*
        #field_vis const fn #field_name(&self) -> #target_ty {
            #cast
        }
    })
}

/// Helper methods on ParseStream that attempt to parse an item but only advance the cursor on success.
trait TryParse {
    fn try_parse<T: Parse>(&self) -> syn::Result<T>;
    fn try_call<T>(&self, function: fn(_: ParseStream<'_>) -> syn::Result<T>) -> syn::Result<T>;
}

impl TryParse for ParseStream<'_> {
    fn try_parse<T: Parse>(&self) -> syn::Result<T> {
        use syn::parse::discouraged::Speculative;
        let fork = self.fork();
        match fork.parse::<T>() {
            Ok(value) => {
                self.advance_to(&fork);
                Ok(value)
            }
            err => err,
        }
    }

    fn try_call<T>(&self, function: fn(_: ParseStream<'_>) -> syn::Result<T>) -> syn::Result<T> {
        use syn::parse::discouraged::Speculative;
        let fork = self.fork();
        match fork.call(function) {
            Ok(value) => {
                self.advance_to(&fork);
                Ok(value)
            }
            err => err,
        }
    }
}

#[derive(Debug)]
struct BitStructInput {
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    name: syn::Ident,
    raw_vis: syn::Visibility,
    raw: RawDef,
    fields: Punctuated<FieldDef, Token![;]>,
}

impl Parse for BitStructInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(syn::Attribute::parse_outer)?;
        let vis = input.parse()?;
        input.parse::<Token![struct]>()?;
        let name = input.parse()?;
        let within_parens;
        syn::parenthesized!(within_parens in input);
        let raw_vis = within_parens.parse()?;
        let raw = within_parens.parse()?;
        let within_braces;
        syn::braced!(within_braces in input);
        let fields = Punctuated::parse_terminated(&within_braces)?;
        Ok(BitStructInput {
            attrs,
            vis,
            name,
            raw_vis,
            raw,
            fields,
        })
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum RawDef {
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl RawDef {
    fn as_str(self) -> &'static str {
        match self {
            RawDef::U8 => "u8",
            RawDef::U16 => "u16",
            RawDef::U32 => "u32",
            RawDef::U64 => "u64",
            RawDef::U128 => "u128",
        }
    }

    fn as_type(self) -> syn::Type {
        syn::parse_str(self.as_str()).unwrap()
    }

    fn bit_len(self) -> u8 {
        match self {
            RawDef::U8 => 8,
            RawDef::U16 => 16,
            RawDef::U32 => 32,
            RawDef::U64 => 64,
            RawDef::U128 => 128,
        }
    }
}

impl Parse for RawDef {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident: syn::Ident = input.parse()?;
        if ident == "u8" {
            Ok(RawDef::U8)
        } else if ident == "u16" {
            Ok(RawDef::U16)
        } else if ident == "u32" {
            Ok(RawDef::U32)
        } else if ident == "u64" {
            Ok(RawDef::U64)
        } else if ident == "u128" {
            Ok(RawDef::U128)
        } else {
            Err(input.error(format!(
                "`{}` is not supported; needs to be one of u8,u16,u32,u64,u128",
                ident
            )))
        }
    }
}

#[derive(Debug)]
struct FieldDef {
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    name: syn::Ident,
    target: Target,
    bits: BitRange,
}

impl Parse for FieldDef {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(syn::Attribute::parse_outer)?;
        let vis = input.parse()?;
        let name = input.parse()?;
        input.parse::<Token![:]>()?;
        let target: Target = input.parse()?;
        input.parse::<Token![=]>()?;
        let bits: BitRange = input.parse()?;
        if target.bit_len() < bits.bit_len() {
            return Err(input.error(format!(
                "target {:?} can only represent {} bits; {} specified",
                target,
                target.bit_len(),
                bits.bit_len(),
            )));
        }
        Ok(FieldDef {
            attrs,
            vis,
            name,
            target,
            bits,
        })
    }
}

#[derive(Debug, Eq, PartialEq)]
enum Target {
    // Basic integer type: u8,u16,u32,u64,u128
    Int(RawDef),
}

impl Target {
    fn bit_len(&self) -> u8 {
        match self {
            Target::Int(raw) => raw.bit_len(),
        }
    }

    fn as_type(&self) -> syn::Type {
        let Target::Int(raw) = self;
        raw.as_type()
    }
}

mod kw {
    syn::custom_keyword!(bool);
}

impl Parse for Target {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Target::Int(input.parse()?))
    }
}

#[derive(Debug, Eq, PartialEq)]
struct BitRange(Range<u8>);

impl BitRange {
    fn bit_len(&self) -> u8 {
        self.0.len().try_into().unwrap()
    }

    fn get_mask(&self) -> u128 {
        let mut mask = !0u128;
        mask <<= 128 - self.0.end;
        mask >>= 128 - self.0.end;
        mask >>= self.0.start;
        mask <<= self.0.start;
        mask
    }
}

impl Parse for BitRange {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        fn parse_end_range(input: ParseStream) -> syn::Result<u8> {
            let range_limits: syn::RangeLimits = input.parse()?;
            let end_bit: u8 = input.parse::<syn::LitInt>()?.base10_parse()?;
            Ok(match range_limits {
                syn::RangeLimits::HalfOpen(_) => end_bit,
                syn::RangeLimits::Closed(_) => end_bit + 1,
            })
        }

        let start_bit: u8 = input.parse::<syn::LitInt>()?.base10_parse()?;
        let range = match input.try_call(parse_end_range) {
            Ok(end_bit) => start_bit..end_bit,
            Err(_) => start_bit..start_bit + 1,
        };
        match range.start.cmp(&range.end) {
            Ordering::Less => {}
            Ordering::Equal => return Err(input.error("empty bit range specified")),
            Ordering::Greater => {
                return Err(input
                    .error("least significant bit must be specified before most significant bit"))
            }
        };
        Ok(BitRange(range))
    }
}

fn hexlit(typ: RawDef, value: u128) -> syn::LitInt {
    let num_hex_chars = typ.bit_len() as usize / 4;
    syn::LitInt::new(
        &format!(
            "0x{value:0width$x}{suffix:}",
            value = value,
            suffix = typ.as_str(),
            width = num_hex_chars
        ),
        proc_macro2::Span::call_site(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parse_bitstruct_input() {
        let bitstruct: BitStructInput = syn::parse2(quote! {
            #[derive(Clone,Copy)]
            pub(crate) struct Foo(pub u16) {
                #[inline]
                pub f1: u8 = 0 .. 8;
                pub f2: u8 = 8 .. 12;
            }
        })
        .unwrap();
        assert_eq!(bitstruct.name, quote::format_ident!("Foo"));
        assert_eq!(bitstruct.fields.len(), 2);
        assert_eq!(bitstruct.fields[0].attrs.len(), 1);
        assert_eq!(bitstruct.fields[1].attrs.len(), 0);
    }

    #[test]
    fn parse_field_def() {
        let field_def: FieldDef = syn::parse2(quote! {
            pub field1: u8 = 3 .. 4
        })
        .unwrap();
        assert_eq!(field_def.name, quote::format_ident!("field1"));
        assert_eq!(field_def.target, Target::Int(RawDef::U8));
        assert_eq!(field_def.bits, BitRange(3..4));
    }

    #[test]
    fn parse_target() {
        assert_eq!(
            Target::Int(RawDef::U8),
            syn::parse2::<Target>(quote! {u8}).unwrap(),
        );
        assert_eq!(
            Target::Int(RawDef::U16),
            syn::parse2::<Target>(quote! {u16}).unwrap(),
        );
        assert_eq!(
            Target::Int(RawDef::U128),
            syn::parse2::<Target>(quote! {u128}).unwrap(),
        );
    }

    #[test]
    fn parse_bitrange() {
        assert_eq!(
            BitRange(0..10),
            syn::parse2::<BitRange>(quote! {0..10}).unwrap()
        );
        assert_eq!(
            BitRange(0..12),
            syn::parse2::<BitRange>(quote! {0..=11}).unwrap()
        );
        assert_eq!(
            BitRange(14..15),
            syn::parse2::<BitRange>(quote! {14}).unwrap()
        );
    }
}
