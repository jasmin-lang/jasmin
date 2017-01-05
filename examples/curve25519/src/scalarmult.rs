// * Scalar multipiplication for curve25519 with 4 limbs
#![allow(unused_mut)] 

rust! {
  use jasmin::jasmin::*;
  use jasmin::U64::*;
}

const rem_p: b64 = jc!(38);

// ** addition

pub fn fadd(mut x: reg! ([b64; 4]), ya: stack! ([b64; 4]))
  -> reg! ([b64; 4]) {
    var! {
        y:    reg! ([b64; 4]);
        cf:   reg! (b1);
        add0: reg! (b64);
        add1: reg! (b64);
    }

    rust! {
        y = [0.to_jval(); 4];
    }

    code!{
        y[0] = ya[0];
        (cf, x[0]) = add(x[0],y[0]);

        for i in (1..4) {
            y[i] = ya[i];
            (cf, x[i]) = adc(x[i],y[i],cf);
        }

        add0 = jc!(0);
        add1 = rem_p;
        when !cf { add1 = add0 };

        for i in (0..4) {
            if (i == 0) {
                (cf, x[0]) = add(x[0],add1);
            } else {
                (cf, x[i]) = adc(x[i],add0,cf);
            }
        }

        when cf { add0 = add1 };
        x[0] = add_v(x[0],add0);
    }

    return x
}

// ** subtraction

pub fn fsub(mut x: reg! ([b64; 4]), ya: stack! ([b64; 4]))
  -> reg! ([b64; 4]) {

    var! {
        y    : reg! ([b64; 4]);
        sub0 : reg! (b64);
        sub1 : reg! (b64);
        cf   : reg! (b1);
    }

    rust! { y = [0.to_jval(); 4]; }

    code! {
        y[0] = ya[0];
        (cf, x[0]) = sub(x[0],y[0]);
        for i in (1..4) {
            y[i] = ya[i];
            (cf, x[i]) = sbb(x[i],y[i],cf);
        }
        sub0 = jc!(0);
        sub1 = rem_p;
        when !cf { sub1 = sub0 };

        for i in (0..4) {
            if (i == 0) {
                (cf, x[0]) = sub(x[0],sub1);
            } else {
                (cf,x[i]) = sbb(x[i],sub0,cf);
            }
        }

        when cf { sub0 = sub1 };
        x[0] = sub_v(x[0],sub0);
    }

    return x
}

// ** reduction from 8 limbs to 4 limbs

fn freduce(z_in: reg! ([b64; 8])) -> reg! ([b64; 4]) {
    var! {
        crem_p: reg! (b64);
        rax:    reg! (b64);
        l:      reg! (b64);
        h:      reg! (b64);
        hprev:  reg! (b64);
        zero:   reg! (b64);
        z:      reg! ([b64; 8]);
        z_out:  reg! ([b64; 4]);
        cf:     reg! (b1);
    }

    rust! {
        z = [0.to_jval(); 8];
        z_out = [0.to_jval(); 4];
        hprev = 0.to_jval();
    }

    code! {
        // FIXME: check if really required 
        for i in (0..8) { z[i] = z_in[i]; }
    
        crem_p = rem_p;
        for i in (0..4) {
            rax = z[4 + i];
            (h, l) = mul(rax,crem_p);
            (cf, z[i]) = add(z[i],l);
            if (i == 0) {
                hprev = jc!(0);
                hprev = adc_v(hprev,h,cf);
            } else {
                h = adc_v(h,0,cf);
                (cf,z[i]) = add(z[i],hprev);
                hprev = jc!(0);
                hprev = adc_v(hprev,h,cf);
            }
        }
        
        l = imul(hprev,rem_p);
        (cf, z[0]) = add(z[0],l);

        for i in (1..4) {
            (cf, z[i]) = adc(z[i],0,cf);
        }

        zero = jc!(0);
        zero = adc_v(zero,0,cf);

        l = imul(zero,rem_p);
        z[0] = add_v(z[0],l);

        // FIXME: check if really required 
        for i in (0..4) { z_out[i] = z[i]; }
    }
    return z_out
}

// ** multiplication

pub fn fmul(xa: stack! ([b64; 4]), ya: stack! ([b64; 4]))
  -> reg! ([b64; 4]) {

    var! {
        z     : reg! ([b64; 8]);
        r     : reg! ([b64; 4]);
        x     : reg! ([b64; 4]);
        y     : reg! ([b64; 4]);
        h     : reg! (b64);
        l     : reg! (b64);
        hprev : reg! (b64);
        cf    : reg! (b1);
    }

    rust! {
        x = [0.to_jval(); 4];
        y = [0.to_jval(); 4];
        z = [0.to_jval(); 8];
        hprev = 0.to_jval();
    }

    code! {
        x[0] = xa[0];
        for j in (0..4) {
            y[j] = ya[j];
            (h, l) = mul(y[j],x[0]);
        
            if (j == 0) {
                z[0] = l;
                z[1] = h;
            } else {
                (cf, z[j]) = add(z[j],l);
                z[j + 1]   = jc!(0);
                z[j + 1]   = adc_v(z[j + 1],h,cf);
            }
        }
        
        for i in (1..4) {
            x[i] = xa[i];
            for j in (0..4) {
                y[j] = ya[j];
                (h, l) = mul(y[j],x[i]);
                (cf, z[i+j]) = add(z[i+j],l);
                if (j == 0) {
                    hprev = jc!(0);
                    hprev = adc_v(hprev,h,cf);
                } else {
                    h = adc_v(h,0,cf);
                    (cf, z[i+j]) = add(z[i+j],hprev);
                    if (1 <= j && j < 4 - 1) {
                        hprev = jc!(0);
                        hprev = adc_v(hprev,h,cf);
                    } else { /* j = 4 */
                        z[i + j + 1] = jc!(0);
                        z[i + j + 1] = adc_v(z[i + j + 1],h,cf);
                    }
                }
            }
        }
        r = freduce(z);
    }


    return r
}

// ** squaring

pub fn fsquare(xa: stack! ([b64; 4])) -> reg! ([b64; 4]) {
    var! {
        z:   reg! ([b64; 8]);
        r:   reg! ([b64; 4]);
        t:   reg! ([b64; 5]);
        rax: reg! (b64);
        rdx: reg! (b64);
        cf:  reg! (b1);
    }

    rust! {
        z = [0.to_jval(); 8];
        t = [0.to_jval(); 5];
    }

    code! {
        z[7] = jc!(0);

        /*   2*x01 + 2*x02 + 2*x03 + 2*x12 + 2*x13 + 2*x23
             + x00 + x11 + x22 + x33 */

        rax = xa[1];
        (rdx, rax) = mul(rax,xa[0]);
        z[1] = rax;
        z[2] = rdx;
        
        rax = xa[2];
        (rdx, rax) = mul(rax,xa[1]);
        z[3] = rax;
        z[4] = rdx;

        rax = xa[3];
        (rdx, rax) = mul(rax,xa[2]);
        z[5] = rax;
        z[6] = rdx;

        /*   [2*]x01 + 2*x02 + 2*x03 + [2*]x12 + 2*x13 + [2*]x23
             + x00 + x11 + x22 + x33 */

        rax = xa[2];
        (rdx, rax) = mul(rax,xa[0]);
        (cf, z[2]) = add(z[2],rax);
        (cf, z[3]) = adc(z[3],rdx,cf);
        z[4]       = adc_v(z[4],0,cf);

        rax = xa[3];
        (rdx, rax) = mul(rax,xa[1]);
        (cf, z[4]) = add(z[4],rax);
        (cf, z[5]) = adc(z[5],rdx,cf);
             z[6]  = adc_v(z[6],0,cf);

        /*   [2*]x01 + [2*]x02 + 2*x03 + [2*]x12 + [2*]x13 + [2*]x23
             + x00 + x11 + x22 + x33 */

        rax = xa[3];
        (rdx, rax) = mul(rax,xa[0]);
        (cf, z[3]) = add(z[3],rax);
        (cf, z[4]) = adc(z[4],rdx,cf);
        (cf, z[5]) = adc(z[5],0,cf);
             z[6]  = adc_v(z[6],0,cf);

        /*   x01 + x02 + x03 + x12 + x13 + x23
             + x00 + x11 + x22 + x33 */

        /* set z<1..2n+1> = 2*z<1..2n+1> since
           we have summed all x_i*x_j with i<>j
           so far and these occur twice */
        (cf, z[1]) = add(z[1],z[1]);
        (cf, z[2]) = adc(z[2],z[2],cf);
        (cf, z[3]) = adc(z[3],z[3],cf);
        (cf, z[4]) = adc(z[4],z[4],cf);
        (cf, z[5]) = adc(z[5],z[5],cf);
        (cf, z[6]) = adc(z[6],z[6],cf);
             z[7]  = adc_v(z[7],z[7],cf);

        /* x00 + x11 + x22 + x33 */
        
        rax = xa[0];
        (rdx, rax) = mul(rax,xa[0]);
        z[0] = rax;
        t[0] = rdx;

        rax = xa[1];
        (rdx, rax) = mul(rax,xa[1]);
        t[1] = rax;
        t[2] = rdx;

        rax = xa[2];
        (rdx, rax) = mul(rax,xa[2]);
        t[3] = rax;
        t[4] = rdx;

        (cf, z[1]) = add(z[1],t[0]);
        (cf, z[2]) = adc(z[2],t[1],cf);
        (cf, z[3]) = adc(z[3],t[2],cf);
        (cf, z[4]) = adc(z[4],t[3],cf);
        (cf, z[5]) = adc(z[5],t[4],cf);
        (cf, z[6]) = adc(z[6],0,cf);
             z[7]  = adc_v(z[7],0,cf);

        rax = xa[3];
        (rdx, rax) = mul(rax,xa[3]);
        (cf, z[6]) = add(z[6],rax);
             z[7]  = adc_v(z[7],rdx,cf);

        r = freduce(z);
    }

    return r
}

// ** ladderstep

pub fn ladderstep(mut x1p: stack! ([b64; 4]),
                  mut x2p: stack! ([b64; 4]),
                  mut z2p: stack! ([b64; 4]),
                  mut x3p: stack! ([b64; 4]),
                  mut z3p: stack! ([b64; 4]))
    -> (stack! ([b64; 4]), stack! ([b64; 4]),
        stack! ([b64; 4]),stack! ([b64; 4])) {

    var! {
        t1: reg! ([b64; 4]);
        t2: reg! ([b64; 4]);
        t7: reg! ([b64; 4]);
        t6: reg! ([b64; 4]);
        t5: reg! ([b64; 4]);
        t3: reg! ([b64; 4]);
        t4: reg! ([b64; 4]);
        t9: reg! ([b64; 4]);
        t8: reg! ([b64; 4]);

        t1p: stack! ([b64; 4]);
        t2p: stack! ([b64; 4]);
        t7p: stack! ([b64; 4]);
        t6p: stack! ([b64; 4]);
        t5p: stack! ([b64; 4]);
        t3p: stack! ([b64; 4]);
        t4p: stack! ([b64; 4]);
        t9p: stack! ([b64; 4]);

        w1: reg! ([b64; 4]);
        w2: reg! ([b64; 4]);
        w3: reg! ([b64; 4]);
        w4: reg! ([b64; 4]);
        w5: reg! ([b64; 4]);
        w6: reg! ([b64; 4]);
        w7: reg! ([b64; 4]);

        c121666p: stack! ([b64; 4]);
    }

    rust! {
        c121666p = [jc!(0); 4];
    }

    code! {
        //c121666p = [121666, 0, 0, 0];
        c121666p[0] = jc!(121666);
        c121666p[1] = jc!(0);
        c121666p[2] = jc!(0);
        c121666p[3] = jc!(0);

        // workp mapping: 0 -> x1p, 1 -> x2p, 2 -> z2p, 3 -> x3p, 4 -> z3p
        t1  = x2p;
        t2  = t1;
        t1  = fadd(t1,z2p);
        t2  = fsub(t2,z2p);
        t1p = t1;
        t2p = t2;
        t7  = fsquare(t2p);
        t7p = t7;
        t6  = fsquare(t1p);
        t6p = t6;
        t5  = t6;
        t5  = fsub(t5,t7p);
        t5p = t5;
        t3  = x3p;
        t4  = t3;
        t3  = fadd(t3,z3p);
        t4  = fsub(t4,z3p);
        t3p = t3;
        t4p = t4;
        t9  = fmul(t3p,t2p);
        t9p = t9;
        t8  = fmul(t4p,t1p);
        w1  = t8;
        w1  = fadd(w1,t9p);
        
        t8  = fsub(t8,t9p);
        x3p = w1;
        z3p = t8;
        w2  = fsquare(x3p);
        x3p = w2;
        w3  = fsquare(z3p);
        z3p = w3;
        w4  = fmul(z3p,x1p);
        z3p = w4;
        w5  = fmul(t6p,t7p);
        x2p = w5;
        w6  = fmul(t5p,c121666p);
        w6  = fadd(w6,t7p);
        z2p = w6;
        w7  = fmul(z2p,t5p);
        z2p = w7;
    }

    return (x2p, z2p, x3p, z3p)
}

// ** cswap

// FIXME: compare with OpenSSL, this is a translation from C
pub fn cswap(mut x2p: stack! ([b64; 4]),
             mut z2p: stack! ([b64; 4]),
             mut x3p: stack! ([b64; 4]),
             mut z3p: stack! ([b64; 4]),
             swap : reg! (b64))
    -> (stack! ([b64; 4]),stack! ([b64; 4]),stack! ([b64; 4]),stack! ([b64;4])) {

    var! {
        tmp1: reg! (b64);
        tmp2: reg! (b64);
        mask: reg! (b64);
    }

    code! {
        mask = imul(swap,0xffff_ffff_ffff_ffff);

        for i in (0..4) {
            tmp1   = x2p[i];
            tmp1   = xor(tmp1,x3p[i]);
            tmp1   = land(tmp1,mask);
            tmp2   = x2p[i];
            tmp2   = xor(tmp2,tmp1);
            x2p[i] = tmp2;
            tmp2   = x3p[i];
            tmp2   = xor(tmp2,tmp1);
            x3p[i] = tmp2;

            tmp1   = z2p[i];
            tmp1   = xor(tmp1,z3p[i]);
            tmp1   = land(tmp1,mask);
            tmp2   = z2p[i];
            tmp2   = xor(tmp2,tmp1);
            z2p[i] = tmp2;
            tmp2   = z3p[i];
            tmp2   = xor(tmp2,tmp1);
            z3p[i] = tmp2;
        }
    }
    return (x2p, z2p, x3p, z3p)
}

// ** inversion

pub fn squarea(x: stack! ([b64; 4])) -> stack! ([b64;4]) {
    var! {
        r  : reg!   ([b64; 4]);
        ra : stack! ([b64; 4]);
    }
    
    code! {
        r = fsquare(x);
        ra = r;
    }
    return ra
}

pub fn mula(x: stack! ([b64; 4]), y: stack! ([b64; 4])) -> stack! ([b64; 4]) {
    var! {
        r  : reg!   ([b64; 4]);
        ra : stack! ([b64; 4]);
    }
    code! {
        r = fmul(x,y);
        ra = r;
    }
    return ra
}

pub fn finvert(xa: stack! ([b64; 4])) -> stack! ([b64; 4]) {
    var! {
        ra:       stack! ([b64; 4]);
        z2:       stack! ([b64; 4]);
        t:        stack! ([b64; 4]);
        z9:       stack! ([b64; 4]);
        z11:      stack! ([b64; 4]);
        z2_5_0:   stack! ([b64; 4]);
        z2_10_0:  stack! ([b64; 4]);
        z2_20_0:  stack! ([b64; 4]);
        z2_50_0:  stack! ([b64; 4]);
        z2_100_0: stack! ([b64; 4]);
    }
    
    code! {
        z2 = squarea(xa);                      /* 2 */
        t = squarea(z2);                       /* 4 */
        t = squarea(t);                        /* 8 */
        z9 = mula(t,xa);                       /* 9 */
        z11 = mula(z9,z2);                     /* 11 */
        t = squarea(z11);                      /* 22 */
        z2_5_0 = mula(t,z9);                   /* 2^5 - 2^0 = 31 */
        
        t = squarea(z2_5_0);                   /* 2^6 - 2^1 */
        for _i in (1..5) { t = squarea(t); }   /* 2^20 - 2^10 */
        z2_10_0 = mula(t,z2_5_0);              /* 2^10 - 2^0 */
        
        t = squarea(z2_10_0);                  /* 2^11 - 2^1 */
        for _i in (1..10) { t = squarea(t); }  /* 2^20 - 2^10 */
        z2_20_0 = mula(t,z2_10_0);             /* 2^20 - 2^0 */
        
        t = squarea(z2_20_0);                  /* 2^21 - 2^1 */
        for _i in (1..20) { t = squarea(t); }  /* 2^40 - 2^20 */
        t = mula(t,z2_20_0);                   /* 2^40 - 2^0 */
        
        t = squarea(t);                        /* 2^41 - 2^1 */
        for _i in (1..10) { t = squarea(t); }  /* 2^50 - 2^10 */
        z2_50_0 = mula(t,z2_10_0);             /* 2^50 - 2^0 */
        
        t = squarea(z2_50_0);                  /* 2^51 - 2^1 */
        for _i in (1..50) { t = squarea(t); }  /* 2^100 - 2^50 */
        z2_100_0 = mula(t,z2_50_0);            /* 2^100 - 2^0 */
        
        t= squarea(z2_100_0);                  /* 2^101 - 2^1 */
        for _i in (1..100) { t = squarea(t); } /* 2^200 - 2^100 */
        t = mula(t,z2_100_0);                  /* 2^200 - 2^0 */
        
        t = squarea(t);                        /* 2^201 - 2^1 */
        for _i in (1..50) { t = squarea(t); }  /* 2^250 - 2^50 */
        t = mula(t,z2_50_0);                   /* 2^250 - 2^0 */
        
        t = squarea(t);                        /* 2^251 - 2^1 */
        t = squarea(t);                        /* 2^252 - 2^2 */
        t = squarea(t);                        /* 2^253 - 2^3 */
        
        t = squarea(t);                        /* 2^254 - 2^4 */
        
        t = squarea(t);                        /* 2^255 - 2^5 */
        ra = mula(t,z11);                      /* 2^255 - 21 */
    }
    return ra
}

// ** montgomery ladder

pub fn mladder(xr: stack! ([b64; 4]), sp: stack! ([b64; 4]))
  -> (stack! ([b64; 4]), stack! ([b64; 4])) {

    var! {
        s:       stack! (b64);
        tmp1:    reg!   (b64);
        tmp2:    reg!   (b64);
        bit:     reg!   (b64);
        swap:    reg!   (b64);
        prevbit: stack! (b64);
        x1:      stack! ([b64; 4]);
        x2:      stack! ([b64; 4]);
        z2:      stack! ([b64; 4]);
        x3:      stack! ([b64; 4]);
        z3:      stack! ([b64; 4]);
        i:       reg!   (b64);
        j:       reg!   (b64);
        i_s:     stack! (b64);
        j_s:     stack! (b64);
        _a:      stack! ([b64; 4]);
        cf:      reg!   (b1);
    }

    rust! {
        x2 = [jc!(0); 4]; // FIXME
        z2 = [jc!(0); 4]; // FIXME
        z3 = [jc!(0); 4]; // FIXME
    }

    code! {
        prevbit = jc!(0);
        x1 = xr;
        //x2 = [1, 0, 0, 0];
        for i in (0..4) { x2[i] = jc!(0); }

        //z2 = [0, 0, 0, 0];
        for i in (0..4) { z2[i] = jc!(0); }
        x3 = xr;
        //z3 = [1, 0, 0, 0];
        for i in (0..4) { z3[i] = jc!(0); }

        i = jc!(3);
        do {
            tmp1 = sp[i]; // FIXME: better syntax
            i_s = i; // probably need the register
            s = tmp1;
            j = jc!(63);
            do {
                tmp2 = s;
                bit = shr(tmp2,j);
                j_s = j; // probably need the register
                bit = land(bit,1);
                swap = prevbit;
                swap = xor(swap,bit);
                prevbit = bit;
                (x2,z2,x3,z3) = cswap(x2,z2,x3,z3,swap);
                (x2,z2,x3,z3) = ladderstep(x1,x2,z2,x3,z3);
                j = j_s;
                (cf,j) = sub(j,1); // returns cf=1 for input j=0
            } while !cf;
            i = i_s;
            (cf,i) = sub(i,1); // returns cf=1 for input i=0
        } while !cf;

        swap = prevbit;
        (x2,z2,_a,_a) = cswap(x2,z2,x3,z3,swap);
    }

    return (x2, z2)
}

// ** unpack_point

pub fn unpack_point(mut p: reg! ([b64; 4])) -> stack! ([b64; 4]) {
    var! {
        pa : stack! ([b64; 4]);
    }

    code! {
        p[3] = land(p[3],0x7fff_ffff_ffff_ffff);
        pa = p;
    }

    return pa
}

// ** unpack_secret

pub fn unpack_secret(mut s: reg! ([b64; 4])) -> stack! ([b64; 4]) {
    var! {
        sa : stack! ([b64; 4]);
    }

    code! {
        s[0] = land(s[0],0xffff_ffff_ffff_fff8);
        s[3] = land(s[3],0x7fff_ffff_ffff_ffff);
        s[3] = lor(s[3],0x4000_0000_0000_0000);
        sa = s;
    }
    return sa
}

// ** freeze

pub fn freeze(mut xa: reg! ([b64; 4])) -> reg! ([b64; 4]) {
    var! {
        r: reg! ([b64; 4]);
        t: reg! ([b64; 4]);
        two63 : reg! (b64);
        cf    : reg! (b1);
    }

    code! {
        r = xa;
        t = r;
        two63 = jc!(1);
        two63 = shl(two63,63);
        (cf, t[0]) = add(t[0],19);
        (cf, t[1]) = adc(t[1],0,cf);
        (cf, t[2]) = adc(t[2],0,cf);
        (cf, t[3]) = adc(t[3],two63,cf);
        when cf { r[0] = t[0] };
        when cf { r[1] = t[1] };
        when cf { r[2] = t[2] };
        when cf { r[3] = t[3] };
        t[0] = r[0];
        t[1] = r[1];
        t[2] = r[2];
        t[3] = r[3];
        (cf, t[0]) = add(t[0],19);
        (cf, t[1]) = adc(t[1],0,cf);
        (cf, t[2]) = adc(t[2],0,cf);
        (cf, t[3]) = adc(t[3],two63,cf);
        when cf { r[0] = t[0] };
        when cf { r[1] = t[1] };
        when cf { r[2] = t[2] };
        when cf { r[3] = t[3] };
        xa[0] = r[0];
        xa[1] = r[1];
        xa[2] = r[2];
        xa[3] = r[3];
    }
    return xa
}

// ** scalar multiplication

pub fn scalarmult(s : reg! ([b64; 4]), /* secret scalar */
                  p : reg! ([b64; 4])  /* point         */)
  -> reg! ([b64; 4]) {
    var! {
        sa:   stack! ([b64; 4]);
        xa:   stack! ([b64; 4]);
        za:   stack! ([b64; 4]);
        zia:  stack! ([b64; 4]);
        r:    reg!   ([b64; 4]);
    }

    code! {
        sa = unpack_secret(s);
        xa = unpack_point(p);
        (xa, za) = mladder(xa,sa);
        zia = finvert(za);
        r = fmul(xa,zia);
        r = freeze(r);
    }
    return r
}

// ** scalar multiplication

pub fn scalarmult_ext(mut rp : reg! (b64), /* address for result */
                          sp : reg! (b64), /* address of scalar  */
                          pp : reg! (b64)  /* address of point   */) {
    var! {
        p: stack! ([b64; 4]);
        s: stack! ([b64; 4]);
        r: reg!   ([b64; 4]);
    }
    
    rust! {
        s = [0.to_jval(); 4];
        p = [0.to_jval(); 4];
    }

    code! {
        for i in (0..4) { s[i] = MEM[sp + i*8]; }
        for i in (0..4) { p[i] = MEM[pp + i*8]; }
        r = scalarmult(s,p);
        for i in (0..4) { MEM[rp + i*8] = r[i]; }
    }
}
