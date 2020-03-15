use failure::Error;
use desert::{ToBytes,FromBytes,CountBytes};

#[test]
fn builtins() -> Result<(),Error> {
  assert_eq![u8::from_bytes(&[5])?, (1,5)];
  assert_eq![u16::from_bytes(&[13,12])?, (2,3340)];
  assert_eq![u32::from_bytes(&[5,6,7,8])?, (4,84281096)];
  assert_eq![5u8.to_bytes()?, vec!(5)];
  assert_eq![3340u16.to_bytes()?, vec!(13,12)];
  assert_eq![84281096u32.to_bytes()?, vec!(5,6,7,8)];
  assert_eq![u8::count_from_bytes(&[5])?, 1];
  assert_eq![u16::count_from_bytes(&[13,12])?, 2];
  assert_eq![u32::count_from_bytes(&[5,6,7,8])?, 4];
  assert_eq![vec![7u8,8u8,9u8].to_bytes()?, vec!(3,7,8,9)];
  assert_eq![vec![7u32,8u32,9u32].to_bytes()?, vec!(12,0,0,0,7,0,0,0,8,0,0,0,9)];
  assert_eq![<Vec<u8>>::count_from_bytes(&[3,7,8,9])?, 4];
  assert_eq![<Vec<u8>>::from_bytes(&[3,7,8,9])?, (4,vec!(7,8,9))];
  assert_eq![
    <Vec<u32>>::from_bytes(&[12,0,0,0,7,0,0,0,8,0,0,0,9])?,
    (13,vec!(7u32,8u32,9u32))
  ];
  assert_eq![vec!(7u32,8u32,9u32).count_bytes(), 13];
  {
    let v: Vec<u16> = (0..500).map(|i| i%5 + (i%3)*500).collect();
    let bytes = v.to_bytes()?;
    let mut with_extra: Vec<u8> = bytes.clone();
    let extra: Vec<u8> = (0..100).map(|i| ((i%6 + (i%9)*300) % 256) as u8).collect();
    with_extra.extend(extra);
    assert_eq![bytes.len(), 1002];
    assert_eq![<Vec<u16>>::from_bytes(&bytes)?, (bytes.len(), v.clone())];
    assert_eq![<Vec<u16>>::count_from_bytes(&bytes)?, bytes.len()];
    assert_eq![<Vec<u16>>::from_bytes(&with_extra[..])?, (bytes.len(), v.clone())];
    assert_eq![<Vec<u16>>::count_from_bytes(&with_extra[..])?, bytes.len()];
  }
  Ok(())
}

#[test]
fn booleans() -> Result<(),Error> {
  assert_eq![true.count_bytes(), 1];
  assert_eq![vec!(true,false).count_bytes(), 3];
  Ok(())
}

#[test]
fn tuples() -> Result<(),Error> {
  assert_eq![(3u8,4u8).count_bytes(),2];
  assert_eq![(6u16,7u16,8u16).count_bytes(),6];
  assert_eq![(3u8,4u8).to_bytes()?,vec!(3,4)];
  assert_eq![(6u16,7u16,8u16).to_bytes()?,vec!(0,6,0,7,0,8)];
  assert_eq![<(u16,u16,u16)>::count_from_bytes(&[0,6,0,7,0,8,200,201,202,203,204])?, 6];
  assert_eq![(6u16,7u8,8u16).to_bytes()?,vec!(0,6,7,0,8)];
  assert_eq![<(u16,u8,u16)>::count_from_bytes(&[0,6,7,0,8,200,201,202,203,204])?, 5];
  Ok(())
}

#[test]
fn arrays() -> Result<(),Error> {
  assert_eq![[3u8,4u8].count_bytes(),2];
  assert_eq![[6u16,7u16,8u16].count_bytes(),6];
  assert_eq![[3u8,4u8].to_bytes()?,vec!(3,4)];
  assert_eq![[6u16,7u16,8u16].to_bytes()?,vec!(0,6,0,7,0,8)];
  assert_eq![<[u16]>::count_from_bytes(&[6,0,6,0,7,0,8,200,201,202,203,204])?, 7];
  assert_eq![<[u16;3]>::count_from_bytes(&[0,6,0,7,0,8,200,201,202,203,204])?, 6];
  Ok(())
}
