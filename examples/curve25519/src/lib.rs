#![feature(const_fn)]
#![feature(type_ascription)]
#![allow(non_upper_case_globals)]

#[macro_use]
extern crate jasmin;
extern crate rand;
extern crate num;
extern crate num_traits;
extern crate num_bigint as bigint;

pub mod scalarmult;
pub mod digits;

#[cfg(test)]
mod tests {
    #![allow(unused_mut)] 
    use jasmin::jasmin::*;
    use scalarmult::*;
    use digits::*;
    use bigint::{ToBigUint};

    #[test]
    fn test_fadd1() {
        let mut x;
        let mut y;
        let mut z;
        code! {
            x = [1,2,3,4];
            y = [1,1,1,1];
            x = fadd(x,y);
            z = [2,3,4,5];
        }
        assert_eq!(x,z)
    }

    #[test]
    fn test_fadd2() {

        let mut rng = ::rand::thread_rng();
        for _ in 0..1000 {
            let a = gen_num(&mut rng);
            let b = gen_num(&mut rng);
            let ab1 = (bigint_of_ds(a) + bigint_of_ds(b)) % p_mod();
            let ab = fadd(a,b);
            let ab2 = bigint_of_ds(ab) % p_mod();
            assert_eq!(ab1,ab2)
        }
    }

    #[test]
    fn test_sub1() {
        let mut x;
        let mut y;
        let mut z;
        
        code! {
            x = [1,2,3,4];
            y = [1,1,1,1];
            x = fsub(x,y);
            z = [0,1,2,3];
        }
        assert_eq!(x,z)
    }

    #[test]
    fn test_fsub2() {

        let mut rng = ::rand::thread_rng();
        for _ in 0..1000 {
            let a = gen_num(&mut rng);
            let b = gen_num(&mut rng);
            let ab1 = ((bigint_of_ds(a) + p_mod())
                       - (bigint_of_ds(b) % p_mod()))
                      % p_mod();
            let ab = fsub(a,b);
            let ab2 = bigint_of_ds(ab) % p_mod();
            assert_eq!(ab1,ab2)
        }
    }

    #[test]
    fn test_mul1() {
        let mut x;
        let mut y;
        let mut z;

        code! {
            x = [1,2,3,4];
            y = [1,0,0,0];
            z = fmul(x,y);
        }
        assert_eq!(z,x)
    }

    #[test]
    fn test_mul2() {
        let mut rng = ::rand::thread_rng();
        for _ in 0..1000 {
            let a = gen_num(&mut rng);
            let b = gen_num(&mut rng);
            let ab1 = (bigint_of_ds(a) * bigint_of_ds(b)) % p_mod();
            let ab = fmul(a,b);
            let ab2 = bigint_of_ds(ab) % p_mod();
            assert_eq!(ab1,ab2)
        }
    }

    #[test]
    fn test_square1() {
        let mut x;
        let mut y;
        let mut z;
        code! {
            x = [1,0,0,0];
            y = [1,0,0,0];
            z = fmul(x,y);
        }
        assert_eq!(z,x)
    }

    #[test]
    fn test_square2() {

        let mut rng = ::rand::thread_rng();
        for _ in 0..1000 {
            let a = gen_num(&mut rng);
            let ab1 = (bigint_of_ds(a) * bigint_of_ds(a)) % p_mod();
            let ab = fmul(a,a);
            let ab2 = bigint_of_ds(ab) % p_mod();
            assert_eq!(ab1,ab2)
        }
    }

    #[test]
    fn test_invert1() {

        let mut rng = ::rand::thread_rng();
        let mut a_inv;
        for _ in 0..1000 {
            let a = gen_num(&mut rng);
            a_inv = finvert(a);
            let res = (bigint_of_ds(a) * bigint_of_ds(a_inv)) % p_mod();
            assert_eq!(1.to_biguint().unwrap(),res)
        }
    }

    #[test]
    fn test_freeze() {
        let mut rng = ::rand::thread_rng();
        for _ in 0..1000 {
            let a = gen_num(&mut rng);
            let a_red = freeze(a.clone());
            let res = bigint_of_ds(a) % p_mod();
            assert_eq!(bigint_of_ds(a_red),res)
        }
    }

    #[test]
    fn test_swap() {
        let mut rng = ::rand::thread_rng();
        for _ in 0..1000 {
            let x2 = gen_num(&mut rng);
            let x3 = gen_num(&mut rng);
            let z2 = gen_num(&mut rng);
            let z3 = gen_num(&mut rng);
            let mut s;
            let mut x2_;
            let mut z2_;
            let mut x3_;
            let mut z3_;
            let mut x2__;
            let mut z2__;
            let mut x3__;
            let mut z3__;
            
            code! {
                s = #0;
                (x2_,z2_,x3_,z3_)     = cswap(x2,z2,x3,z3,s);
                s = #1;
                (x3__,z3__,x2__,z2__) = cswap(x2,z2,x3,z3,s);
            }
            assert_eq!(x2,x2_);
            assert_eq!(x2,x2__);
            assert_eq!(z2,z2_);
            assert_eq!(z2,z2__);
            assert_eq!(x3,x3_);
            assert_eq!(x3,x3__);
            assert_eq!(z3,z3_);
            assert_eq!(z3,z3__);
        }
    }

    #[test]
    fn test_scalarmult() {
        let mut rng = ::rand::thread_rng();
        var! {
            p    : [b64; 4],
            s1   : [b64; 4],
            s2   : [b64; 4],
            p1   : [b64; 4],
            p12  : [b64; 4],
            p2   : [b64; 4],
            p21  : [b64; 4]
        }
        
        for _ in 0..1000 {
            p  = gen_num(&mut rng);
            s1 = gen_num(&mut rng);
            s2 = gen_num(&mut rng);
            p = ds_of_bigint(bigint_of_ds(p) % p_mod());
            code! {
                p1  = scalarmult(s1,p);
                p12 = scalarmult(s2,p1);
                p2  = scalarmult(s2,p);
                p21 = scalarmult(s1,p2);
            }
            assert_eq!(p12,p21);
        }
    }

    #[test]
    fn test_scalarmult_ext() {
        let mut rng = ::rand::thread_rng();
        var! {
            p_p  : b64,
            s_p  : b64,
            r_p  : b64,
            p    : [b64; 4],
            s1   : [b64; 4],
            s2   : [b64; 4],
            p1   : [b64; 4],
            p12  : [b64; 4],
            p2   : [b64; 4],
            p21  : [b64; 4]
        }
        
        for _ in 0..1000 {
            p  = gen_num(&mut rng);
            s1 = gen_num(&mut rng);
            s2 = gen_num(&mut rng);
            p = ds_of_bigint(bigint_of_ds(p) % p_mod());
            code! {
                p1  = [0; 4];
                p12 = [0; 4];
                p2  = [0; 4];
                p21 = [0; 4];
                p_p = #0*4*8;
                s_p = #1*4*8;
                r_p = #2*4*8;

                // s2*(s1*P)
                for i in (0..4) {
                    MEM[s_p + i*8] = s1[i];
                    MEM[p_p + i*8] = p[i];
                }
                scalarmult_ext(r_p,s_p,p_p);
                for i in (0..4) {
                    p1[i] = MEM[r_p + i*8];
                    MEM[s_p + i*8] = s2[i];
                    MEM[p_p + i*8] = p1[i];
                }
                scalarmult_ext(r_p,s_p,p_p);
                for i in (0..4) {
                    p12[i] = MEM[r_p + i*8];
                }
                
                // s1*(s2*P)
                for i in (0..4) {
                    MEM[p_p + i*8] = p[i];
                    MEM[s_p + i*8] = s2[i];
                }
                scalarmult_ext(r_p,s_p,p_p);
                for i in (0..4) {
                    p2[i] = MEM[r_p + i*8];
                    MEM[s_p + i*8] = s1[i];
                    MEM[p_p + i*8] = p2[i];
                }
                scalarmult_ext(r_p,s_p,p_p);
                for i in (0..4) {
                    p21[i] = MEM[r_p + i*8];
                }
            }
            assert_eq!(p12,p21);
        }
    }
}
