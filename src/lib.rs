use failure::{Error,bail};

pub trait ToBytes {
  fn to_bytes(&self) -> Result<Vec<u8>,Error>;
  fn write_bytes(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let bytes = self.to_bytes()?;
    if dst.len() < bytes.len() { bail!["dst buffer too small"] }
    dst[0..bytes.len()].copy_from_slice(&bytes);
    Ok(bytes.len())
  }
}
pub trait ToBytesBE {
  fn to_bytes_be(&self) -> Result<Vec<u8>,Error>;
  fn write_bytes_be(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let bytes = self.to_bytes_be()?;
    if dst.len() < bytes.len() { bail!["dst buffer too small"] }
    dst[0..bytes.len()].copy_from_slice(&bytes);
    Ok(bytes.len())
  }
}
pub trait ToBytesLE {
  fn to_bytes_le(&self) -> Result<Vec<u8>,Error>;
  fn write_bytes_le(&self, dst: &mut [u8]) -> Result<usize,Error> {
    let bytes = self.to_bytes_le()?;
    if dst.len() < bytes.len() { bail!["dst buffer too small"] }
    dst[0..bytes.len()].copy_from_slice(&bytes);
    Ok(bytes.len())
  }
}

pub trait FromBytes: Sized {
  fn from_bytes(src: &[u8]) -> Result<(usize,Self),Error>;
}
pub trait FromBytesBE: Sized {
  fn from_bytes_be(src: &[u8]) -> Result<(usize,Self),Error>;
}
pub trait FromBytesLE: Sized {
  fn from_bytes_le(src: &[u8]) -> Result<(usize,Self),Error>;
}

pub trait CountBytes {
  fn count_from_bytes(buf: &[u8]) -> Result<usize,Error>;
  fn count_from_bytes_more(buf: &[u8]) -> Result<Option<usize>,Error> {
    Ok(Some(Self::count_from_bytes(buf)?))
  }
  fn count_bytes(&self) -> usize;
}
pub trait CountBytesBE {
  fn count_from_bytes_be(buf: &[u8]) -> Result<usize,Error>;
  fn count_from_bytes_be_more(buf: &[u8]) -> Result<Option<usize>,Error> {
    Ok(Some(Self::count_from_bytes_be(buf)?))
  }
  fn count_bytes_be(&self) -> usize;
}
pub trait CountBytesLE {
  fn count_from_bytes_le(buf: &[u8]) -> Result<usize,Error>;
  fn count_from_bytes_le_more(buf: &[u8]) -> Result<Option<usize>,Error> {
    Ok(Some(Self::count_from_bytes_le(buf)?))
  }
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

#[macro_export]
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

#[macro_export]
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
  let msb = (64 - value.leading_zeros()) as usize;
  (msb.max(1)+7)/7
}
