use desert::{ToBytesBE,FromBytesBE,CountBytesBE};

fn main() -> Result<(),Error> {
  assert_eq![(5u16,6u16).to_bytes()?, vec![0,5,0,6]];
  Ok(())
}
