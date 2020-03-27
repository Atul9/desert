//! # desert
//!
//! traits for {de,}serializing compact binary formats
//!
//! * compact representations for the builtin container types (tuples, arrays,
//!   slices, vectors) is provided.
//! * varint length encoding scheme for slices and vectors (1 byte for len < 128)
//! * emphasis on ergonomics of implementing custom binary {de,}serializers
//!
//! This crate does not (presently) provide automatic derivation. Instead, the
//! emphasis is on having a good collection of compact implementations for built-in
//! containers and making it easy to implement your own binary formats manually.
//!
//! # example
//!
//! You can use the methods on built-in types and containers:
//!
//! ```rust
//! use desert::{ToBytes,ToBytesBE,ToBytesLE,FromBytesBE,CountBytes};
//! use failure::Error;
//!
//! fn main() -> Result<(),Error> {
//!   // no overhead for tuples and arrays
//!   assert_eq![(5u16,6u16,7u16).to_bytes_be()?, vec![0,5,0,6,0,7]];
//!   assert_eq![[5u16,6u16,7u16].to_bytes_be()?, vec![0,5,0,6,0,7]];
//!
//!   // minimal overhead for slices and vectors using varints
//!   assert_eq![
//!     vec![100u16,101u16,102u16].as_slice().to_bytes_be()?,
//!     vec![6,0,100,0,101,0,102]
//!   ];
//!   assert_eq![vec![0u8;500].count_bytes(), 502];
//!
//!   // without endianness defaults to big-endian
//!   assert_eq![(5u16,6u16).to_bytes()?, vec![0,5,0,6]];
//!   assert_eq![(5u16,6u16).to_bytes_be()?, vec![0,5,0,6]];
//!   assert_eq![(5u16,6u16).to_bytes_le()?, vec![5,0,6,0]];
//!
//!   // construct an array from bytes and get the size of bytes read
//!   assert_eq![
//!     <[u16;2]>::from_bytes_be(&vec![0,5,0,6])?,
//!     (4,[5u16,6u16])
//!   ];
//!   // this way you can load data structures from slices with extra at the end
//!   assert_eq![
//!     <[u16;2]>::from_bytes_be(&vec![0,5,0,6,7,8,9,10,11])?,
//!     (4,[5u16,6u16])
//!   ];
//!
//!   // count how many bytes will need to be read for this Vec<u16>
//!   assert_eq![
//!     <Vec<u16>>::count_from_bytes(&vec![6,0,100,0,101,0,102,55,44,33,22,11])?,
//!     7
//!   ];
//!
//!   Ok(())
//! }
//! ```
//!
//! And you can define your own types:
//!
//! ```rust
//! use desert::{ToBytes,FromBytes};
//! use failure::Error;
//!
//! #[derive(Debug)]
//! enum Item { A((f32,f32)), B(u32) }
//!
//! #[derive(Debug)]
//! struct Custom { foo: u64, items: Vec<Item> }
//!
//! impl ToBytes for Custom {
//!   fn to_bytes(&self) -> Result<Vec<u8>,Error> {
//!     let mut bytes = vec![];
//!     // Store foo (in big endian).
//!     bytes.extend(&self.foo.to_bytes()?);
//!
//!     // Store the number of items (in big endian).
//!     bytes.extend(&(self.items.len() as u16).to_bytes()?);
//!
//!     // Use a bitfield to more compactly represent
//!     // whether an Item is an A or B.
//!     let mut bitfield = vec![0u8;(self.items.len()+7)/8];
//!     for (i,item) in self.items.iter().enumerate() {
//!       bitfield[i/8] |= match item {
//!         Item::A(_) => 0,
//!         Item::B(_) => 1,
//!       } << (i%8);
//!     }
//!     bytes.extend(bitfield);
//!
//!     // Write out each item serially.
//!     for item in self.items.iter() {
//!       bytes.extend(match item {
//!         Item::A(x) => x.to_bytes()?,
//!         Item::B(x) => x.to_bytes()?
//!       });
//!     }
//!     Ok(bytes)
//!   }
//! }
//!
//! impl FromBytes for Custom {
//!   fn from_bytes(src: &[u8]) -> Result<(usize,Self),Error> {
//!     let mut offset = 0;
//!
//!     // Read foo (in big endian).
//!     let (size,foo) = u64::from_bytes(&src[offset..])?;
//!     offset += size;
//!
//!     // Read the number of items (in big endian).
//!     let (size,item_len) = u16::from_bytes(&src[offset..])?;
//!     offset += size;
//!
//!     // Read the bitfield data but keep it as a u8 slice.
//!     let bitfield_len = ((item_len+7)/8) as usize;
//!     let bitfield = &src[offset..offset+bitfield_len];
//!     offset += bitfield_len;
//!
//!     // Read the items, checking the bitfield to know whether an item
//!     // is an A or a B.
//!     let mut items = vec![];
//!     for i in 0..item_len as usize {
//!       if (bitfield[i/8]>>(i%8))&1 == 0 {
//!         let (size,x) = <(f32,f32)>::from_bytes(&src[offset..])?;
//!         items.push(Item::A(x));
//!         offset += size;
//!       } else {
//!         let (size,x) = u32::from_bytes(&src[offset..])?;
//!         items.push(Item::B(x));
//!         offset += size;
//!       }
//!     }
//!     Ok((offset, Custom { foo, items }))
//!   }
//! }
//!
//! fn main() -> Result<(),Error> {
//!   let bytes = Custom {
//!     foo: 1234567890123456789,
//!     items: vec![
//!       Item::A((3.0,4.2)),
//!       Item::B(1337),
//!       Item::A((5.5,6.6))
//!     ]
//!   }.to_bytes()?;
//!   println!["serialized: {:?}", bytes];
//!
//!   let (size,custom) = Custom::from_bytes(&bytes)?;
//!   println!["deserialized {} bytes: {:?}", size, custom];
//!   Ok(())
//! }
//! ```
//!
//! # rationale
//!
//! Rust core has some useful methods defined on builtin types:
//! `5000u32.to_be_bytes()`, `u32::from_be_bytes([u8;4])`, etc.
//!
//! These methods are certainly useful, but they belong to the builtin types, not
//! traits. This makes it difficult to write a generic interface that accepts
//! anything that can be serialized to bytes.
//!
//! Other options such as serde with bincode let you derive custom implementations
//! of Serialize and Derive, which are very convenient and you can support for many
//! other output formats besides binary. However, if you want implement your own
//! custom serialization and especially deserialization, things get very difficult.
//! For deserialization you need to implement a Visitor and things get very messy
//! quickly.
//!
//! bincode also makes trade-offs that make sense for quickly marshalling data into
//! and out of memory with minimal parsing overhead, but this choice means that
//! things like vectors get `usize` bytes padded to the beginning which is 8 whole
//! bytes on a 64-bit machine and enums under the automatic derivation will always
//! be prefaced with a `u32` even if there are only 2 options to enumerate. These
//! trade-offs are not ideal for situations where you need more fine-grained control
//! over the representation of your structs at a byte-level to keep overhead low or
//! to integrate with an existing externally-defined wire-protocol. But to achieve
//! those custom byte formats with serde and bincode, you would need to implement
//! very generic and difficult serde interfaces when you might only care about bytes
//! over the wire or on disk.
//!
//! Another common issue working with binary data is reading large chunks from the
//! network or from disk in sizes determined by the network transport or physical
//! medium. Those sizes are very unlikely to map nicely to your data structures, so
//! it is very useful to be able to count (without parsing into a new instance) how
//! many bytes can be read from a `[u8]` slice to arrive at the ending byte offset
//! for the particular data structure under consideration which may have a dynamic
//! size. Or it may also be helpful to know when the data structure's representation
//! extends past the end of the buffer slice and the program should fetch more data
//! from the network or from on disk. These concerns are provided by the
//! `CountBytes` traits.

use failure::{Error,bail};

/// Serialize a type into a sequence of bytes with unspecified endianness.
/// The implementations for the built-in types are in big endian for this trait.
pub trait ToBytes {
  /// Serialize into a newly-allocated byte vector.
  fn to_bytes(&self) -> Result<Vec<u8>,Error>;
  /// Serialize into an existing mutable byte slice.
  /// The usize Result contains how many bytes were written to `dst`.
  fn write_bytes(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let bytes = self.to_bytes()?;
    if dst.len() < bytes.len() { bail!["dst buffer too small"] }
    dst[0..bytes.len()].copy_from_slice(&bytes);
    Ok(bytes.len())
  }
}
/// Serialize a type into a sequence of bytes in big endian.
pub trait ToBytesBE {
  /// Serialize into a newly-allocated byte vector in big endian.
  fn to_bytes_be(&self) -> Result<Vec<u8>,Error>;
  /// Serialize into an existing mutable byte slice in big endian.
  /// The usize Result contains how many bytes were written to `dst`.
  fn write_bytes_be(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let bytes = self.to_bytes_be()?;
    if dst.len() < bytes.len() { bail!["dst buffer too small"] }
    dst[0..bytes.len()].copy_from_slice(&bytes);
    Ok(bytes.len())
  }
}
/// Serialize a type into a sequence of bytes in little endian.
pub trait ToBytesLE {
  /// Serialize into a newly-allocated byte vector in little endian.
  fn to_bytes_le(&self) -> Result<Vec<u8>,Error>;
  /// Serialize into an existing mutable byte slice in little endian.
  /// The usize Result contains how many bytes were written to `dst`.
  fn write_bytes_le(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let bytes = self.to_bytes_le()?;
    if dst.len() < bytes.len() { bail!["dst buffer too small"] }
    dst[0..bytes.len()].copy_from_slice(&bytes);
    Ok(bytes.len())
  }
}

/// Deserialize a sequence of bytes into a type.
/// The implementations for the built-in types are in big endian for this trait.
pub trait FromBytes: Sized {
  /// Read data from `src` in order to create an instance `Self`.
  /// The `usize` in the `Result` is the number of bytes read from `src`.
  fn from_bytes(src: &[u8]) -> Result<(usize,Self),Error>;
}
/// Deserialize a sequence of bytes into a type in big endian.
pub trait FromBytesBE: Sized {
  /// Read data from `src` in order to create an instance `Self` in big endian.
  /// The `usize` in the `Result` is the number of bytes read from `src`.
  fn from_bytes_be(src: &[u8]) -> Result<(usize,Self),Error>;
}
/// Deserialize a sequence of bytes into a type in little endian.
pub trait FromBytesLE: Sized {
  /// Read data from `src` in order to create an instance `Self` in little
  /// endian.
  /// The `usize` in the `Result` is the number of bytes read from `src`.
  fn from_bytes_le(src: &[u8]) -> Result<(usize,Self),Error>;
}

/// Count how many bytes to read from a byte slice for a type and calculate how
/// many bytes the serialization would contain.
/// The implementations for the built-in types are in big endian for this trait.
pub trait CountBytes {
  /// Return how many bytes from `buf` would be required to deserialize Self.
  fn count_from_bytes(buf: &[u8]) -> Result<usize,Error>;
  /// Return how many bytes from `buf` would be required to deserialize Self,
  /// where if there are not enough bytes in `buf` to know how many bytes would
  /// be required, you will receive `None` or otherwise `Some(nbytes)`.
  fn count_from_bytes_more(buf: &[u8]) -> Result<Option<usize>,Error> {
    Ok(Some(Self::count_from_bytes(buf)?))
  }
  /// Return the number of bytes that the serialization would require.
  fn count_bytes(&self) -> usize;
}
/// Count how many bytes to read from a byte slice for a type and calculate how
/// many bytes the serialization would contain. In big endian.
pub trait CountBytesBE {
  /// Return how many bytes from `buf` would be required to deserialize Self
  /// in big endian.
  fn count_from_bytes_be(buf: &[u8]) -> Result<usize,Error>;
  /// Return how many bytes from `buf` would be required to deserialize Self
  /// in big endian, where if there are not enough bytes in `buf` to know how
  /// many bytes would be required, you will receive `None` or otherwise
  /// `Some(nbytes)`.
  fn count_from_bytes_be_more(buf: &[u8]) -> Result<Option<usize>,Error> {
    Ok(Some(Self::count_from_bytes_be(buf)?))
  }
  /// Return the number of bytes that the serialization would require.
  fn count_bytes_be(&self) -> usize;
}
/// Count how many bytes to read from a byte slice for a type and calculate how
/// many bytes the serialization would contain. In little endian.
pub trait CountBytesLE {
  /// Return how many bytes from `buf` would be required to deserialize Self
  /// in little endian.
  fn count_from_bytes_le(buf: &[u8]) -> Result<usize,Error>;
  /// Return how many bytes from `buf` would be required to deserialize Self
  /// in little endian, where if there are not enough bytes in `buf` to know how
  /// many bytes would be required, you will receive `None` or otherwise
  /// `Some(nbytes)`.
  fn count_from_bytes_le_more(buf: &[u8]) -> Result<Option<usize>,Error> {
    Ok(Some(Self::count_from_bytes_le(buf)?))
  }
  /// Return the number of bytes that the serialization would require.
  fn count_bytes_le(&self) -> usize;
}

macro_rules! buf_array {
  ($b:tt,1) => {[$b[0]]};
  ($b:tt,2) => {[$b[0],$b[1]]};
  ($b:tt,4) => {[$b[0],$b[1],$b[2],$b[3]]};
  ($b:tt,8) => {[$b[0],$b[1],$b[2],$b[3],$b[4],$b[5],$b[6],$b[7]]};
  ($b:tt,16) => {[$b[0],$b[1],$b[2],$b[3],$b[4],$b[5],$b[6],$b[7],
    $b[8],$b[9],$b[10],$b[11],$b[12],$b[13],$b[14],$b[15]]};
}

macro_rules! define_static_builtins {
  ($(($T:tt,$n:tt)),+) => {$(
    impl CountBytes for $T {
      fn count_from_bytes(_buf: &[u8]) -> Result<usize,Error> {
        Ok($n)
      }
      fn count_bytes(&self) -> usize { $n }
    }
    impl CountBytesBE for $T {
      fn count_from_bytes_be(_buf: &[u8]) -> Result<usize,Error> {
        Ok($n)
      }
      fn count_bytes_be(&self) -> usize { $n }
    }
    impl CountBytesLE for $T {
      fn count_from_bytes_le(_buf: &[u8]) -> Result<usize,Error> {
        Ok($n)
      }
      fn count_bytes_le(&self) -> usize { $n }
    }
    impl ToBytes for $T {
      fn to_bytes(&self) -> Result<Vec<u8>,Error> {
        self.to_bytes_be()
      }
      fn write_bytes(&self, dst: &mut [u8]) -> Result<usize,Error> {
        self.write_bytes_be(dst)
      }
    }
    impl ToBytesBE for $T {
      fn to_bytes_be(&self) -> Result<Vec<u8>,Error> {
        Ok(self.to_be_bytes().to_vec())
      }
      fn write_bytes_be(&self, dst: &mut [u8]) -> Result<usize,Error> {
        let bytes = self.to_be_bytes();
        if dst.len() < bytes.len() { bail!["dst buffer too small"] }
        dst[0..bytes.len()].copy_from_slice(&bytes);
        Ok(bytes.len())
      }
    }
    impl ToBytesLE for $T {
      fn to_bytes_le(&self) -> Result<Vec<u8>,Error> {
        Ok(self.to_le_bytes().to_vec())
      }
      fn write_bytes_le(&self, dst: &mut [u8]) -> Result<usize,Error> {
        let bytes = self.to_le_bytes();
        if dst.len() < bytes.len() { bail!["dst buffer too small"] }
        dst[0..bytes.len()].copy_from_slice(&bytes);
        Ok(bytes.len())
      }
    }
    impl FromBytes for $T {
      fn from_bytes(src: &[u8]) -> Result<(usize,Self),Error> {
        Self::from_bytes_be(src)
      }
    }
    impl FromBytesBE for $T {
      fn from_bytes_be(src: &[u8]) -> Result<(usize,Self),Error> {
        if src.len() < $n {
          bail!["not enough bytes provided to construct type"]
        } else {
          Ok(($n,$T::from_be_bytes(buf_array![src,$n])))
        }
      }
    }
    impl FromBytesLE for $T {
      fn from_bytes_le(src: &[u8]) -> Result<(usize,Self),Error> {
        if src.len() < $n {
          bail!["not enough bytes provided to construct type"]
        } else {
          Ok(($n,$T::from_le_bytes(buf_array![src,$n])))
        }
      }
    }
  )*};
}

define_static_builtins![
  (u8,1),(u16,2),(u32,4),(u64,8),(u128,16),
  (i8,1),(i16,2),(i32,4),(i64,8),(i128,16),
  (f32,4),(f64,8)
];

impl CountBytes for bool {
  fn count_from_bytes(_buf: &[u8]) -> Result<usize,Error> { Ok(1) }
  fn count_bytes(&self) -> usize { 1 }
}
impl CountBytesBE for bool {
  fn count_from_bytes_be(_buf: &[u8]) -> Result<usize,Error> { Ok(1) }
  fn count_bytes_be(&self) -> usize { 1 }
}
impl CountBytesLE for bool {
  fn count_from_bytes_le(_buf: &[u8]) -> Result<usize,Error> { Ok(1) }
  fn count_bytes_le(&self) -> usize { 1 }
}

impl ToBytes for bool {
  fn to_bytes(&self) -> Result<Vec<u8>,Error> {
    Ok(vec![if *self { 1 } else { 0 }])
  }
  fn write_bytes(&self, dst: &mut [u8]) -> Result<usize,Error> {
    if dst.is_empty() { bail!["dst buffer too small"] }
    dst[0] = *self as u8;
    Ok(1)
  }
}
impl ToBytesBE for bool {
  fn to_bytes_be(&self) -> Result<Vec<u8>,Error> {
    self.to_bytes()
  }
  fn write_bytes_be(&self, dst: &mut [u8]) -> Result<usize,Error> {
    self.write_bytes(dst)
  }
}
impl ToBytesLE for bool {
  fn to_bytes_le(&self) -> Result<Vec<u8>,Error> {
    self.to_bytes()
  }
  fn write_bytes_le(&self, dst: &mut [u8]) -> Result<usize,Error> {
    self.write_bytes(dst)
  }
}

impl FromBytes for bool {
  fn from_bytes(src: &[u8]) -> Result<(usize,Self),Error> {
    if src.is_empty() {
      bail!["not enough bytes provided to construct type"]
    } else {
      Ok((1,src[0] != 0))
    }
  }
}
impl FromBytesBE for bool {
  fn from_bytes_be(src: &[u8]) -> Result<(usize,Self),Error> {
    Self::from_bytes(src)
  }
}
impl FromBytesLE for bool {
  fn from_bytes_le(src: &[u8]) -> Result<(usize,Self),Error> {
    Self::from_bytes(src)
  }
}

macro_rules! define_tuple {
  ($(($T:tt,$i:tt)),+) => {
    impl<$($T),+> CountBytes for ($($T),+) where $($T: CountBytes),+ {
      fn count_from_bytes(buf: &[u8]) -> Result<usize,Error> {
        let mut offset = 0;
        $(
          offset += $T::count_from_bytes(&buf[offset..])?;
        )+
        Ok(offset)
      }
      fn count_bytes(&self) -> usize {
        $(self.$i.count_bytes() +)+ 0
      }
    }
    impl<$($T),+> CountBytesBE for ($($T),+) where $($T: CountBytesBE),+ {
      fn count_from_bytes_be(buf: &[u8]) -> Result<usize,Error> {
        let mut offset = 0;
        $(
          offset += $T::count_from_bytes_be(&buf[offset..])?;
        )+
        Ok(offset)
      }
      fn count_bytes_be(&self) -> usize {
        $(self.$i.count_bytes_be() +)+ 0
      }
    }
    impl<$($T),+> CountBytesLE for ($($T),+) where $($T: CountBytesLE),+ {
      fn count_from_bytes_le(buf: &[u8]) -> Result<usize,Error> {
        let mut offset = 0;
        $(
          offset += $T::count_from_bytes_le(&buf[offset..])?;
        )+
        Ok(offset)
      }
      fn count_bytes_le(&self) -> usize {
        $(self.$i.count_bytes_le() +)+ 0
      }
    }

    impl<$($T),+> ToBytes for ($($T),+) where $($T: ToBytes+CountBytes),+ {
      fn to_bytes(&self) -> Result<Vec<u8>,Error> {
        let mut buf = vec![0u8;$(self.$i.count_bytes() +)+ 0];
        self.write_bytes(&mut buf)?;
        Ok(buf)
      }
      fn write_bytes(&self, dst: &mut [u8]) -> Result<usize,Error> {
        let len = $(self.$i.count_bytes() +)+ 0;
        if dst.len() < len { bail!["dst buffer too small"] }
        let mut offset = 0;
        $(
          offset += self.$i.write_bytes(&mut dst[offset..])?;
        )+
        Ok(offset)
      }
    }
    impl<$($T),+> ToBytesBE for ($($T),+) where $($T: ToBytesBE+CountBytesBE),+ {
      fn to_bytes_be(&self) -> Result<Vec<u8>,Error> {
        let mut buf = vec![0u8;$(self.$i.count_bytes_be() +)+ 0];
        self.write_bytes_be(&mut buf)?;
        Ok(buf)
      }
      fn write_bytes_be(&self, dst: &mut [u8]) -> Result<usize,Error> {
        let len = $(self.$i.count_bytes_be() +)+ 0;
        if dst.len() < len { bail!["dst buffer too small"] }
        let mut offset = 0;
        $(
          offset += self.$i.write_bytes_be(&mut dst[offset..])?;
        )+
        Ok(offset)
      }
    }
    impl<$($T),+> ToBytesLE for ($($T),+) where $($T: ToBytesLE+CountBytesLE),+ {
      fn to_bytes_le(&self) -> Result<Vec<u8>,Error> {
        let mut buf = vec![0u8;$(self.$i.count_bytes_le() +)+ 0];
        self.write_bytes_le(&mut buf)?;
        Ok(buf)
      }
      fn write_bytes_le(&self, dst: &mut [u8]) -> Result<usize,Error> {
        let len = $(self.$i.count_bytes_le() +)+ 0;
        if dst.len() < len { bail!["dst buffer too small"] }
        let mut offset = 0;
        $(
          offset += self.$i.write_bytes_le(&mut dst[offset..])?;
        )+
        Ok(offset)
      }
    }

    impl<$($T),+> FromBytes for ($($T),+) where $($T: FromBytes),+ {
      fn from_bytes(src: &[u8]) -> Result<(usize,Self),Error> {
        let mut offset = 0;
        let result = ($({
          let (size,x) = $T::from_bytes(&src[offset..])?;
          offset += size;
          x
        }),+);
        Ok((offset,result))
      }
    }
    impl<$($T),+> FromBytesBE for ($($T),+) where $($T: FromBytesBE),+ {
      fn from_bytes_be(src: &[u8]) -> Result<(usize,Self),Error> {
        let mut offset = 0;
        let result = ($({
          let (size,x) = $T::from_bytes_be(&src[offset..])?;
          offset += size;
          x
        }),+);
        Ok((offset,result))
      }
    }
    impl<$($T),+> FromBytesLE for ($($T),+) where $($T: FromBytesLE),+ {
      fn from_bytes_le(src: &[u8]) -> Result<(usize,Self),Error> {
        let mut offset = 0;
        let result = ($({
          let (size,x) = $T::from_bytes_le(&src[offset..])?;
          offset += size;
          x
        }),+);
        Ok((offset,result))
      }
    }
  }
}

define_tuple![(A,0),(B,1)];
define_tuple![(A,0),(B,1),(C,2)];
define_tuple![(A,0),(B,1),(C,2),(D,3)];
define_tuple![(A,0),(B,1),(C,2),(D,3),(E,4)];
define_tuple![(A,0),(B,1),(C,2),(D,3),(E,4),(F,5)];
define_tuple![(A,0),(B,1),(C,2),(D,3),(E,4),(F,5),(G,6)];
define_tuple![(A,0),(B,1),(C,2),(D,3),(E,4),(F,5),(G,6),(H,7)];
define_tuple![(A,0),(B,1),(C,2),(D,3),(E,4),(F,5),(G,6),(H,7),(I,8)];
define_tuple![(A,0),(B,1),(C,2),(D,3),(E,4),(F,5),(G,6),(H,7),(I,8),(J,9)];
define_tuple![(A,0),(B,1),(C,2),(D,3),(E,4),(F,5),(G,6),(H,7),(I,8),(J,9),(K,10)];
define_tuple![(A,0),(B,1),(C,2),(D,3),(E,4),(F,5),(G,6),(H,7),(I,8),(J,9),(K,10),(L,11)];

macro_rules! define_array {
  ($n:tt) => {
    impl<T> CountBytes for [T;$n] where T: CountBytes {
      fn count_from_bytes(buf: &[u8]) -> Result<usize,Error> {
        let mut offset = 0;
        for _i in 0..$n {
          offset += T::count_from_bytes(&buf[offset..])?;
        }
        Ok(offset)
      }
      fn count_bytes(&self) -> usize {
        let mut size = 0;
        for i in 0..$n {
          size += self[i].count_bytes();
        }
        size
      }
    }
    impl<T> CountBytesBE for [T;$n] where T: CountBytesBE {
      fn count_from_bytes_be(buf: &[u8]) -> Result<usize,Error> {
        let mut offset = 0;
        for _i in 0..$n {
          offset += T::count_from_bytes_be(&buf[offset..])?;
        }
        Ok(offset)
      }
      fn count_bytes_be(&self) -> usize {
        let mut size = 0;
        for i in 0..$n {
          size += self[i].count_bytes_be();
        }
        size
      }
    }
    impl<T> CountBytesLE for [T;$n] where T: CountBytesLE {
      fn count_from_bytes_le(buf: &[u8]) -> Result<usize,Error> {
        let mut offset = 0;
        for _i in 0..$n {
          offset += T::count_from_bytes_le(&buf[offset..])?;
        }
        Ok(offset)
      }
      fn count_bytes_le(&self) -> usize {
        let mut size = 0;
        for i in 0..$n {
          size += self[i].count_bytes_le();
        }
        size
      }
    }

    impl<T> ToBytes for [T;$n] where T: ToBytes+CountBytes {
      fn to_bytes(&self) -> Result<Vec<u8>,Error> {
        let mut buf = vec![0u8;self.count_bytes()];
        self.write_bytes(&mut buf)?;
        Ok(buf)
      }
      fn write_bytes(&self, dst: &mut [u8]) -> Result<usize,Error> {
        let mut len = 0;
        for i in 0..$n {
          len += self[i].count_bytes();
        }
        if dst.len() < len { bail!["dst buffer too small to write array"] }
        let mut offset = 0;
        for i in 0..$n {
          offset += self[i].write_bytes(&mut dst[offset..])?;
        }
        Ok(offset)
      }
    }
    impl<T> ToBytesBE for [T;$n] where T: ToBytesBE+CountBytesBE {
      fn to_bytes_be(&self) -> Result<Vec<u8>,Error> {
        let mut buf = vec![0u8;self.count_bytes_be()];
        self.write_bytes_be(&mut buf)?;
        Ok(buf)
      }
      fn write_bytes_be(&self, dst: &mut [u8]) -> Result<usize,Error> {
        let mut len = 0;
        for i in 0..$n {
          len += self[i].count_bytes_be();
        }
        if dst.len() < len { bail!["dst buffer too small to write array"] }
        let mut offset = 0;
        for i in 0..$n {
          offset += self[i].write_bytes_be(&mut dst[offset..])?;
        }
        Ok(offset)
      }
    }
    impl<T> ToBytesLE for [T;$n] where T: ToBytesLE+CountBytesLE {
      fn to_bytes_le(&self) -> Result<Vec<u8>,Error> {
        let mut buf = vec![0u8;self.count_bytes_le()];
        self.write_bytes_le(&mut buf)?;
        Ok(buf)
      }
      fn write_bytes_le(&self, dst: &mut [u8]) -> Result<usize,Error> {
        let mut len = 0;
        for i in 0..$n {
          len += self[i].count_bytes_le();
        }
        if dst.len() < len { bail!["dst buffer too small to write array"] }
        let mut offset = 0;
        for i in 0..$n {
          offset += self[i].write_bytes_le(&mut dst[offset..])?;
        }
        Ok(offset)
      }
    }

    impl<T> FromBytes for [T;$n] where T: FromBytes+Default+Copy {
      fn from_bytes(src: &[u8]) -> Result<(usize,Self),Error> {
        let mut res = [T::default();$n];
        let mut offset = 0;
        for i in 0..$n {
          let (size,x) = T::from_bytes(&src[offset..])?;
          offset += size;
          res[i] = x;
        }
        Ok((offset,res))
      }
    }
    impl<T> FromBytesBE for [T;$n] where T: FromBytesBE+Default+Copy {
      fn from_bytes_be(src: &[u8]) -> Result<(usize,Self),Error> {
        let mut res = [T::default();$n];
        let mut offset = 0;
        for i in 0..$n {
          let (size,x) = T::from_bytes_be(&src[offset..])?;
          offset += size;
          res[i] = x;
        }
        Ok((offset,res))
      }
    }
    impl<T> FromBytesLE for [T;$n] where T: FromBytesLE+Default+Copy {
      fn from_bytes_le(src: &[u8]) -> Result<(usize,Self),Error> {
        let mut res = [T::default();$n];
        let mut offset = 0;
        for i in 0..$n {
          let (size,x) = T::from_bytes_le(&src[offset..])?;
          offset += size;
          res[i] = x;
        }
        Ok((offset,res))
      }
    }
  }
}

macro_rules! define_arrays {
  ($($n:tt),*) => { $(define_array![$n];)+ };
}
define_arrays![
  1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,
  26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50
];
define_arrays![
  51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,
  76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100
];
define_arrays![128,256,512,1024,2048,4096,8192,16384,32768,65536];

impl<T> ToBytes for [T] where T: ToBytes+CountBytes {
  fn to_bytes(&self) -> Result<Vec<u8>,Error> {
    let mut buf = vec![0u8;self.count_bytes()];
    self.write_bytes(&mut buf)?;
    Ok(buf)
  }
  fn write_bytes(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes();
    }
    let hlen = varint_length(len as u64);
    if dst.len() < len+hlen { bail!["dst buffer too small to write vec"] }
    let mut offset = varint_encode(len as u64, dst)?;
    for x in self.iter() {
      offset += x.write_bytes(&mut dst[offset..])?;
    }
    Ok(offset)
  }
}
impl<T> ToBytesBE for [T] where T: ToBytesBE+CountBytesBE {
  fn to_bytes_be(&self) -> Result<Vec<u8>,Error> {
    let mut buf = vec![0u8;self.count_bytes_be()];
    self.write_bytes_be(&mut buf)?;
    Ok(buf)
  }
  fn write_bytes_be(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes_be();
    }
    let hlen = varint_length(len as u64);
    if dst.len() < len+hlen { bail!["dst buffer too small to write vec"] }
    let mut offset = varint_encode(len as u64, dst)?;
    for x in self.iter() {
      offset += x.write_bytes_be(&mut dst[offset..])?;
    }
    Ok(offset)
  }
}
impl<T> ToBytesLE for [T] where T: ToBytesLE+CountBytesLE {
  fn to_bytes_le(&self) -> Result<Vec<u8>,Error> {
    let mut buf = vec![0u8;self.count_bytes_le()];
    self.write_bytes_le(&mut buf)?;
    Ok(buf)
  }
  fn write_bytes_le(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes_le();
    }
    let hlen = varint_length(len as u64);
    if dst.len() < len+hlen { bail!["dst buffer too small to write vec"] }
    let mut offset = varint_encode(len as u64, dst)?;
    for x in self.iter() {
      offset += x.write_bytes_le(&mut dst[offset..])?;
    }
    Ok(offset)
  }
}

impl<T> CountBytes for [T] where T: CountBytes {
  fn count_from_bytes(buf: &[u8]) -> Result<usize,Error> {
    let (mut offset,len) = varint_decode(buf)?;
    let end = (offset as u64) + len;
    while (offset as u64) < end {
      offset += T::count_from_bytes(&buf[offset..])?;
    }
    Ok(offset)
  }
  fn count_bytes(&self) -> usize {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes();
    }
    return len + varint_length(len as u64);
  }
}
impl<T> CountBytesBE for [T] where T: CountBytesBE {
  fn count_from_bytes_be(buf: &[u8]) -> Result<usize,Error> {
    let (mut offset,len) = varint_decode(buf)?;
    let end = (offset as u64) + len;
    while (offset as u64) < end {
      offset += T::count_from_bytes_be(&buf[offset..])?;
    }
    Ok(offset)
  }
  fn count_bytes_be(&self) -> usize {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes_be();
    }
    return len + varint_length(len as u64);
  }
}
impl<T> CountBytesLE for [T] where T: CountBytesLE {
  fn count_from_bytes_le(buf: &[u8]) -> Result<usize,Error> {
    let (mut offset,len) = varint_decode(buf)?;
    let end = (offset as u64) + len;
    while (offset as u64) < end {
      offset += T::count_from_bytes_le(&buf[offset..])?;
    }
    Ok(offset)
  }
  fn count_bytes_le(&self) -> usize {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes_le();
    }
    return len + varint_length(len as u64);
  }
}

impl<T> ToBytes for Vec<T> where T: ToBytes+CountBytes {
  fn to_bytes(&self) -> Result<Vec<u8>,Error> {
    let mut buf = vec![0u8;self.count_bytes()];
    self.write_bytes(&mut buf)?;
    Ok(buf)
  }
  fn write_bytes(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes();
    }
    let hlen = varint_length(len as u64);
    if dst.len() < len+hlen { bail!["dst buffer too small to write vec"] }
    let mut offset = varint_encode(len as u64, dst)?;
    for x in self.iter() {
      offset += x.write_bytes(&mut dst[offset..])?;
    }
    Ok(offset)
  }
}
impl<T> ToBytesBE for Vec<T> where T: ToBytesBE+CountBytesBE {
  fn to_bytes_be(&self) -> Result<Vec<u8>,Error> {
    let mut buf = vec![0u8;self.count_bytes_be()];
    self.write_bytes_be(&mut buf)?;
    Ok(buf)
  }
  fn write_bytes_be(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes_be();
    }
    let hlen = varint_length(len as u64);
    if dst.len() < len+hlen { bail!["dst buffer too small to write vec"] }
    let mut offset = varint_encode(len as u64, dst)?;
    for x in self.iter() {
      offset += x.write_bytes_be(&mut dst[offset..])?;
    }
    Ok(offset)
  }
}
impl<T> ToBytesLE for Vec<T> where T: ToBytesLE+CountBytesLE {
  fn to_bytes_le(&self) -> Result<Vec<u8>,Error> {
    let mut buf = vec![0u8;self.count_bytes_le()];
    self.write_bytes_le(&mut buf)?;
    Ok(buf)
  }
  fn write_bytes_le(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes_le();
    }
    let hlen = varint_length(len as u64);
    if dst.len() < len+hlen { bail!["dst buffer too small to write vec"] }
    let mut offset = varint_encode(len as u64, dst)?;
    for x in self.iter() {
      offset += x.write_bytes_le(&mut dst[offset..])?;
    }
    Ok(offset)
  }
}

impl<T> FromBytes for Vec<T> where T: FromBytes {
  fn from_bytes(src: &[u8]) -> Result<(usize,Self),Error> {
    let (mut offset,len) = varint_decode(src)?;
    let end = offset + (len as usize);
    let mut v = vec![];
    while offset < end {
      let (size,x) = T::from_bytes(&src[offset..])?;
      v.push(x);
      offset += size;
    }
    Ok((end,v))
  }
}
impl<T> FromBytesBE for Vec<T> where T: FromBytesBE {
  fn from_bytes_be(src: &[u8]) -> Result<(usize,Self),Error> {
    let (mut offset,len) = varint_decode(src)?;
    let end = offset + (len as usize);
    let mut v = vec![];
    while offset < end {
      let (size,x) = T::from_bytes_be(&src[offset..])?;
      v.push(x);
      offset += size;
    }
    Ok((end,v))
  }
}
impl<T> FromBytesLE for Vec<T> where T: FromBytesLE {
  fn from_bytes_le(src: &[u8]) -> Result<(usize,Self),Error> {
    let (mut offset,len) = varint_decode(src)?;
    let end = offset + (len as usize);
    let mut v = vec![];
    while offset < end {
      let (size,x) = T::from_bytes_le(&src[offset..])?;
      v.push(x);
      offset += size;
    }
    Ok((end,v))
  }
}

impl<T> CountBytes for Vec<T> where T: CountBytes {
  fn count_from_bytes(buf: &[u8]) -> Result<usize,Error> {
    let (mut offset,len) = varint_decode(buf)?;
    let end = (offset as u64) + len;
    while (offset as u64) < end {
      offset += T::count_from_bytes(&buf[offset..])?;
    }
    Ok(offset)
  }
  fn count_bytes(&self) -> usize {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes();
    }
    return len + varint_length(len as u64);
  }
}
impl<T> CountBytesBE for Vec<T> where T: CountBytesBE {
  fn count_from_bytes_be(buf: &[u8]) -> Result<usize,Error> {
    let (mut offset,len) = varint_decode(buf)?;
    let end = (offset as u64) + len;
    while (offset as u64) < end {
      offset += T::count_from_bytes_be(&buf[offset..])?;
    }
    Ok(offset)
  }
  fn count_bytes_be(&self) -> usize {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes_be();
    }
    return len + varint_length(len as u64);
  }
}
impl<T> CountBytesLE for Vec<T> where T: CountBytesLE {
  fn count_from_bytes_le(buf: &[u8]) -> Result<usize,Error> {
    let (mut offset,len) = varint_decode(buf)?;
    let end = (offset as u64) + len;
    while (offset as u64) < end {
      offset += T::count_from_bytes_le(&buf[offset..])?;
    }
    Ok(offset)
  }
  fn count_bytes_le(&self) -> usize {
    let mut len = 0;
    for x in self.iter() {
      len += x.count_bytes_le();
    }
    return len + varint_length(len as u64);
  }
}

fn varint_decode(buf: &[u8]) -> Result<(usize,u64),Error> {
  let mut value = 0u64;
  let mut m = 1u64;
  let mut offset = 0usize;
  for _i in 0..8 {
    if offset >= buf.len() {
      bail!["buffer supplied to varint decoding too small"]
    }
    let byte = buf[offset];
    offset += 1;
    value += m * u64::from(byte & 127);
    m *= 128;
    if byte & 128 == 0 { break }
  }
  Ok((offset,value))
}

fn varint_encode(value: u64, buf: &mut [u8]) -> Result<usize,Error> {
  let len = varint_length(value);
  if buf.len() < len { bail!["buffer is too small to write varint"] }
  let mut offset = 0;
  let mut v = value;
  while v > 127 {
    buf[offset] = (v as u8) | 128;
    offset += 1;
    v >>= 7;
  }
  buf[offset] = v as u8;
  Ok(len)
}

fn varint_length(value: u64) -> usize {
  let msb = (63 - value.leading_zeros()) as usize;
  (msb.max(1)+7)/7
}
