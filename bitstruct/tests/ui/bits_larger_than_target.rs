use bitstruct::bitstruct;

bitstruct! {
    struct Reg(u32) {
        field1: u8 = 10 .. 19;
    }
}

fn main() {}