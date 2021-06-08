use bitstruct::bitstruct;

bitstruct! {
    struct Reg(u32) {
        field1: u64 = 0 .. 33;
    }
}

fn main() {}