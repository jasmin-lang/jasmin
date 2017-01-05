use bigint::{ToBigUint, RandBigInt, BigUint};
use num::{ToPrimitive};
use jasmin::jasmin::*;
use num_traits::{Zero, One};

pub fn p64() -> BigUint {
    (One::one() : BigUint) << 64
}

pub fn p_mod() -> BigUint {
    ((One::one() : BigUint) << 255) - 19.to_biguint().unwrap()
}
    
pub fn bigint_of_ds(ds: [b64; 4]) -> BigUint {
    
    let mut a : BigUint = Zero::zero();
    for i in (0..4).rev() {
        a = a << 64;
        a = a + ds[i].val.to_biguint().unwrap();
    }
    a
}

pub fn ds_of_bigint(mut a: BigUint) -> [b64; 4] {
    let mut r = [ 0.to_jval(); 4];
    for i in 0..4 {
        r[i] = ((a.clone() % &p64()).to_u64().unwrap()).to_jval();
        a = a >> 64
    }
    r
}

pub fn gen_num(rng: &mut ::rand::ThreadRng) -> [b64; 4] {
    let a = rng.gen_biguint(256);
    let ds = ds_of_bigint(a.clone());
    assert_eq!(bigint_of_ds(ds.clone()),a);
    ds
}
