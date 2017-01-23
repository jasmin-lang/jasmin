// ** License
// -----------------------------------------------------------------------
// Copyright 2016--2017 IMDEA Software Institute
// Copyright 2016--2017 Inria
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
// -----------------------------------------------------------------------

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
