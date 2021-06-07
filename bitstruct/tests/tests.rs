use bitstruct::bitstruct;

#[test]
fn basic() {
    bitstruct! {
        struct MyReg(pub u32) {
            field1: u8 = 0 .. 4;
            field2: u8 = 4 .. 8;
            field3: u16 = 8 .. 24;
            field4: u8 = 24 .. 32;
        }
    }
    let x = MyReg(0)
        .with_field1(7)
        .with_field2(9)
        .with_field3(106)
        .with_field4(253);
    assert_eq!(x.field1(), 7);
    assert_eq!(x.field2(), 9);
    assert_eq!(x.field3(), 106);
    assert_eq!(x.field4(), 253);
}

proptest::proptest! {
    #[test]
    fn test_props(
        f1 in 0u8 ..= 3,
        f2 in 0u8 ..= 255,
        f3 in 0u16 ..= 65535,
        f4 in 0u8 ..= 63
    ) {
        bitstruct! {
            struct MyReg(u32) {
                field1: u8 = 0 .. 2;
                field2: u8 = 2 .. 10;
                field3: u16 = 10 .. 26;
                field4: u8 = 26 .. 32;
                all: u32 = 0 .. 32;
            }
        }
        let bs = MyReg(0)
            .with_field1(f1)
            .with_field2(f2)
            .with_field3(f3)
            .with_field4(f4);

        assert_eq!(bs.field1(), f1);
        assert_eq!(bs.field2(), f2);
        assert_eq!(bs.field3(), f3);
        assert_eq!(bs.field4(), f4);
        assert_eq!(bs.all(), bs.0);
        assert_eq!(bs.0, f1 as u32 | ((f2 as u32) << 2) | ((f3 as u32) << 10) | ((f4 as u32) << 26));
    }
}

/// Compile failure tests.
#[test]
fn ui() {
    trybuild::TestCases::new().compile_fail("tests/ui/*.rs");
}
