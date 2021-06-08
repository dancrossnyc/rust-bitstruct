use bitstruct::bitstruct;

#[test]
fn basic() {
    bitstruct! {
        struct MyReg(pub u32) {
            field1: u8 = 0 .. 3;
            field2: bool = 3;
            field3: u8 = 4 .. 8;
            field4: u16 = 8 .. 24;
            field5: u8 = 24 .. 32;
        }
    }
    let x = MyReg(0)
        .with_field1(7)
        .with_field2(true)
        .with_field3(9)
        .with_field4(106)
        .with_field5(253);
    assert_eq!(x.field1(), 7);
    assert_eq!(x.field2(), true);
    assert_eq!(x.field3(), 9);
    assert_eq!(x.field4(), 106);
    assert_eq!(x.field5(), 253);
}

#[test]
fn convert() {
    // Simple wrapper with a universal conversion between u8 and Self.
    #[derive(Debug, Eq, PartialEq)]
    struct WrappedU8(u8);

    impl From<u8> for WrappedU8 {
        fn from(x: u8) -> WrappedU8 {
            WrappedU8(x)
        }
    }
    impl From<WrappedU8> for u8 {
        fn from(x: WrappedU8) -> u8 {
            x.0
        }
    }

    // Simple wrapper with a conversion specific to MyReg bitfield.
    #[derive(Debug, Eq, PartialEq)]
    struct WrappedU16(u16);

    impl bitstruct::FromRaw<u16, WrappedU16> for MyReg {
        fn from_raw(x: u16) -> WrappedU16 {
            WrappedU16(x)
        }
    }
    impl bitstruct::IntoRaw<u16, WrappedU16> for MyReg {
        fn into_raw(x: WrappedU16) -> u16 {
            x.0
        }
    }

    bitstruct! {
        struct MyReg(u32) {
            field1: WrappedU8 = 4 .. 12;
            field2: WrappedU16 = 12 .. 28;
        }
    }

    let x = MyReg(0)
        .with_field1(WrappedU8(42))
        .with_field2(WrappedU16(1024));
    assert_eq!(x.field1(), WrappedU8(42));
    assert_eq!(x.field2(), WrappedU16(1024));
}

mod proptests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn tests(
            f1 in 0u8 ..= 3,
            f2: bool,
            f3 in 0u8 ..= 127,
            f4: u16,
            f5 in 0u8 ..= 63
        ) {
            bitstruct! {
                struct MyReg(u32) {
                    field1: u8 = 0 .. 2;
                    field2: bool = 2;
                    field3: u8 = 3 .. 10;
                    field4: u16 = 10 .. 26;
                    field5: u8 = 26 .. 32;
                    all: u32 = 0 .. 32;
                }
            }
            let bs = MyReg(0)
                .with_field1(f1)
                .with_field2(f2)
                .with_field3(f3)
                .with_field4(f4)
                .with_field5(f5);

            assert_eq!(bs.field1(), f1);
            assert_eq!(bs.field2(), f2);
            assert_eq!(bs.field3(), f3);
            assert_eq!(bs.field4(), f4);
            assert_eq!(bs.field5(), f5);
            assert_eq!(bs.all(), bs.0);

            let expected =
                (f1 as u32)
                | ((f2 as u32) << 2)
                | ((f3 as u32) << 3)
                | ((f4 as u32) << 10)
                | ((f5 as u32) << 26);

            assert_eq!(bs.0, expected);
        }
    }
}

/// Compile failure tests.
#[test]
fn ui() {
    trybuild::TestCases::new().compile_fail("tests/ui/*.rs");
}
