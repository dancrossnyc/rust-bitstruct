use bitstruct::bitstruct;

bitstruct! {
    struct SanityCheck(pub u32) {
        #[inline]
        pub field1: u8 = 0..2;
        field2: u8 = 2..4;
        pub field3: u8 = 4..6;
        pub field5: u8 = 8;
    }
}