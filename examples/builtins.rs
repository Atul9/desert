use desert::{ToBytes,ToBytesBE,ToBytesLE,FromBytesBE,CountBytes};
use failure::Error;

fn main() -> Result<(),Error> {
  // no overhead for tuples and arrays
  assert_eq![(5u16,6u16,7u16).to_bytes_be()?, vec![0,5,0,6,0,7]];
  assert_eq![[5u16,6u16,7u16].to_bytes_be()?, vec![0,5,0,6,0,7]];

  // minimal overhead for slices and vectors using varints
  assert_eq![
    vec![100u16,101u16,102u16].as_slice().to_bytes_be()?,
    vec![6,0,100,0,101,0,102]
  ];
  assert_eq![vec![0u8;500].count_bytes(), 502];

  // without endianness defaults to big-endian
  assert_eq![(5u16,6u16).to_bytes()?, vec![0,5,0,6]];
  assert_eq![(5u16,6u16).to_bytes_be()?, vec![0,5,0,6]];
  assert_eq![(5u16,6u16).to_bytes_le()?, vec![5,0,6,0]];

  // construct an array from bytes and get the size of bytes read
  assert_eq![
    <[u16;2]>::from_bytes_be(&vec![0,5,0,6])?,
    (4,[5u16,6u16])
  ];
  // this way you can load data structures from slices with extra at the end
  assert_eq![
    <[u16;2]>::from_bytes_be(&vec![0,5,0,6,7,8,9,10,11])?,
    (4,[5u16,6u16])
  ];

  // count how many bytes will need to be read for this Vec<u16>
  assert_eq![
    <Vec<u16>>::count_from_bytes(&vec![6,0,100,0,101,0,102,55,44,33,22,11])?,
    7
  ];

  Ok(())
}
