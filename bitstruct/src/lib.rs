pub use bitstruct_derive::bitstruct;

pub trait FromRaw<Raw, Target> {
    fn from_raw(raw: Raw) -> Target;
}

pub trait IntoRaw<Raw, Target> {
    fn into_raw(target: Target) -> Raw;
}

/// Blanket impl of FromRaw for any type that has Into<Target> implemented.
/// This allows types that have universal conversions to define Into<Target>
/// rather than a conversion per bitfield. If the Target type does not have a
/// universal representation (i.e. it varies depending on the bitstruct) you
/// should instead implement FromRaw for each particular bitstruct field that
/// contains the Target type.
impl<T, Raw, Target> FromRaw<Raw, Target> for T
where
    Raw: Into<Target>,
{
    fn from_raw(raw: Raw) -> Target {
        raw.into()
    }
}

/// Blanket impl of IntoRaw for any type that has Into<Raw> implemented.
/// This allows types that have universal conversions to define Into<Raw>
/// rather than a conversion per bitfield. If the Target type does not have a
/// universal representation (i.e. it varies depending on the bitstruct) you
/// should instead implement IntoRaw for each particular bitstruct field that
/// contains the Target type.
impl<T, Raw, Target> IntoRaw<Raw, Target> for T
where
    Target: Into<Raw>,
{
    fn into_raw(target: Target) -> Raw {
        target.into()
    }
}
