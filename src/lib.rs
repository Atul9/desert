use failure::{Error,bail};

pub trait ToBytes {
  fn to_bytes(&self) -> Result<Vec<u8>,Error>;
  fn write_bytes(&self, buf: &mut [u8]) -> Result<usize,Error>;
  //fn write_bytes_with_len(&self, buf: &mut [u8], len: usize) -> Result<usize,Error>;
}
pub trait FromBytes: Sized {
  fn from_bytes(buf: &[u8]) -> Result<(usize,Self),Error>;
}
pub trait CountBytes {
  fn count_bytes(buf: &[u8]) -> Result<usize,Error>;
  fn byte_len(&self) -> usize;
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
      fn count_bytes(_buf: &[u8]) -> Result<usize,Error> {
        Ok($n)
      }
      fn byte_len(&self) -> usize { $n }
    }
    impl ToBytes for $T {
      fn to_bytes(&self) -> Result<Vec<u8>,Error> {
        Ok(self.to_be_bytes().to_vec())
      }
      fn write_bytes(&self, buf: &mut [u8]) -> Result<usize,Error> {
        let bytes = self.to_be_bytes();
        if buf.len() < bytes.len() { bail!["dst buffer too small"] }
        buf[0..bytes.len()].copy_from_slice(&bytes);
        Ok(bytes.len())
      }
    }
    impl FromBytes for $T {
      fn from_bytes(buf: &[u8]) -> Result<(usize,Self),Error> {
        if buf.len() < $n {
          bail!["not enough bytes provided to construct type"]
        } else {
          Ok(($n,$T::from_be_bytes(buf_array![buf,$n])))
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
  fn count_bytes(_buf: &[u8]) -> Result<usize,Error> { Ok(1) }
  fn byte_len(&self) -> usize { 1 }
}
impl ToBytes for bool {
  fn to_bytes(&self) -> Result<Vec<u8>,Error> {
    Ok(vec![if *self { 1 } else { 0 }])
  }
  fn write_bytes(&self, buf: &mut [u8]) -> Result<usize,Error> {
    if buf.is_empty() { bail!["dst buffer too small"] }
    buf[0] = *self as u8;
    Ok(1)
  }
}
impl FromBytes for bool {
  fn from_bytes(buf: &[u8]) -> Result<(usize,Self),Error> {
    if buf.is_empty() {
      bail!["not enough bytes provided to construct type"]
    } else {
      Ok((1,buf[0] != 0))
    }
  }
}

macro_rules! define_tuple {
  ($(($T:tt,$i:tt)),+) => {
    impl<$($T),+> CountBytes for ($($T),+) where $($T: CountBytes),+ {
      fn count_bytes(buf: &[u8]) -> Result<usize,Error> {
        let mut offset = 0;
        $(
          offset += $T::count_bytes(&buf[offset..])?;
        )+
        Ok(offset)
      }
      fn byte_len(&self) -> usize {
        $(self.$i.byte_len() +)+ 0
      }
    }
    impl<$($T),+> ToBytes for ($($T),+) where $($T: ToBytes+CountBytes),+ {
      fn to_bytes(&self) -> Result<Vec<u8>,Error> {
        let mut buf = vec![0u8;$(self.$i.byte_len() +)+ 0];
        self.write_bytes(&mut buf)?;
        Ok(buf)
      }
      fn write_bytes(&self, buf: &mut [u8]) -> Result<usize,Error> {
        let len = $(self.$i.byte_len() +)+ 0;
        if buf.len() < len { bail!["dst buffer too small"] }
        let mut offset = 0;
        $(
          offset += self.$i.write_bytes(&mut buf[offset..])?;
        )+
        Ok(offset)
      }
    }
    impl<$($T),+> FromBytes for ($($T),+) where $($T: FromBytes),+ {
      fn from_bytes(buf: &[u8]) -> Result<(usize,Self),Error> {
        let mut offset = 0;
        let result = ($({
          let (size,x) = $T::from_bytes(&buf[offset..])?;
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
      fn count_bytes(buf: &[u8]) -> Result<usize,Error> {
        let mut offset = 0;
        for _i in 0..$n {
          offset += T::count_bytes(&buf[offset..])?;
        }
        Ok(offset)
      }
      fn byte_len(&self) -> usize {
        let mut size = 0;
        for i in 0..$n {
          size += self[i].byte_len();
        }
        size
      }
    }
    impl<T> ToBytes for [T;$n] where T: ToBytes+CountBytes {
      fn to_bytes(&self) -> Result<Vec<u8>,Error> {
        let mut buf = vec![0u8;self.byte_len()];
        self.write_bytes(&mut buf)?;
        Ok(buf)
      }
      fn write_bytes(&self, buf: &mut [u8]) -> Result<usize,Error> {
        let mut len = 0;
        for i in 0..$n {
          len += self[i].byte_len();
        }
        if buf.len() < len { bail!["dst buffer too small to write array"] }
        let mut offset = 0;
        for i in 0..$n {
          offset += self[i].write_bytes(&mut buf[offset..])?;
        }
        Ok(offset)
      }
    }
    impl<T> FromBytes for [T;$n] where T: FromBytes+Default+Copy {
      fn from_bytes(buf: &[u8]) -> Result<(usize,Self),Error> {
        let mut res = [T::default();$n];
        let mut offset = 0;
        for i in 0..$n {
          let (size,x) = T::from_bytes(&buf[offset..])?;
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
define_arrays![1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16];

impl<T> ToBytes for [T] where T: ToBytes+CountBytes {
  fn to_bytes(&self) -> Result<Vec<u8>,Error> {
    let mut buf = vec![0u8;self.byte_len()];
    self.write_bytes(&mut buf)?;
    Ok(buf)
  }
  fn write_bytes(&self, buf: &mut [u8]) -> Result<usize,Error> {
    let mut len = 0;
    for x in self.iter() {
      len += x.byte_len();
    }
    let hlen = varint_length(len as u64);
    if buf.len() < len+hlen { bail!["dst buffer too small to write vec"] }
    let mut offset = varint_encode(len as u64, buf)?;
    for x in self.iter() {
      offset += x.write_bytes(&mut buf[offset..])?;
    }
    Ok(offset)
  }
}

impl<T> CountBytes for [T] where T: CountBytes {
  fn count_bytes(buf: &[u8]) -> Result<usize,Error> {
    let (mut offset,len) = varint_decode(buf)?;
    let end = (offset as u64) + len;
    while (offset as u64) < end {
      offset += T::count_bytes(&buf[offset..])?;
    }
    Ok(offset)
  }
  fn byte_len(&self) -> usize {
    let mut len = 0;
    for x in self.iter() {
      len += x.byte_len();
    }
    return len + varint_length(len as u64);
  }
}

impl<T> ToBytes for Vec<T> where T: ToBytes+CountBytes {
  fn to_bytes(&self) -> Result<Vec<u8>,Error> {
    let mut buf = vec![0u8;self.byte_len()];
    self.write_bytes(&mut buf)?;
    Ok(buf)
  }
  fn write_bytes(&self, buf: &mut [u8]) -> Result<usize,Error> {
    let mut len = 0;
    for x in self.iter() {
      len += x.byte_len();
    }
    let hlen = varint_length(len as u64);
    if buf.len() < len+hlen { bail!["dst buffer too small to write vec"] }
    let mut offset = varint_encode(len as u64, buf)?;
    for x in self.iter() {
      offset += x.write_bytes(&mut buf[offset..])?;
    }
    Ok(offset)
  }
}

impl<T> FromBytes for Vec<T> where T: FromBytes {
  fn from_bytes(buf: &[u8]) -> Result<(usize,Self),Error> {
    let (mut offset,len) = varint_decode(buf)?;
    let end = offset + (len as usize);
    let mut v = vec![];
    while offset < end {
      let (size,x) = T::from_bytes(&buf[offset..])?;
      v.push(x);
      offset += size;
    }
    Ok((end,v))
  }
}

impl<T> CountBytes for Vec<T> where T: CountBytes {
  fn count_bytes(buf: &[u8]) -> Result<usize,Error> {
    let (mut offset,len) = varint_decode(buf)?;
    let end = (offset as u64) + len;
    while (offset as u64) < end {
      offset += T::count_bytes(&buf[offset..])?;
    }
    Ok(offset)
  }
  fn byte_len(&self) -> usize {
    let mut len = 0;
    for x in self.iter() {
      len += x.byte_len();
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
