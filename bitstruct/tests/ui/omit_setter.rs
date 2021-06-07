use bitstruct::bitstruct;

bitstruct! {
    struct Reg(u32) {
        field1: u8 = 10 .. 18;

        #[bitstruct(omit_setter)]
        field2: u8 = 20 .. 22;
    }
}

fn main() {
    let _ = Reg(0)
        .with_field1(1) // field1 is fine
        .with_field2(2); // fails because omit_setter was specified on field2
}
