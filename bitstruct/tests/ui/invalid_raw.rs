use bitstruct::bitstruct;

bitstruct! {
    struct Reg(i32) {
        field1: u8 = 10 .. 19;
    }
}

fn main() {}
