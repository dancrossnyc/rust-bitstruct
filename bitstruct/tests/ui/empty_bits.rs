use bitstruct::bitstruct;

bitstruct! {
    struct Reg(u32) {
        field1: u8 = 19 .. 19;
    }
}

fn main() {}

