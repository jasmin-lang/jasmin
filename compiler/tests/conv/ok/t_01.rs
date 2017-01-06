fn test() {
    var! {
        x:  reg!    (b64);
        y:  reg!    (b64);
        z:  reg!    ([b64; 4]);
        cf: reg!    (b1);
        i:  inline! (b64);
    }
    code! {
        // asignments
        y = 1;
        z[1] = 2;
        x = y;
        y = z[1];
        y = z[x];

        // addition variants
        x = add(x,1);
        (cf,x) = add_cf(x,1);
        x = adc(x,1,cf);
        (cf,x) = adc1_cf(x,1,cf);

        // subtraction variants
        x = sub(x,1);
        (cf,x) = sub_cf(x,1);
        x = sbb(x,1,cf);
        (cf,x) = sbb_cf(x,1,cf);

        // conditional move
        when cf { x = y };
        // x = y if !cf; // unsupported at the moment

        // umul
        (x,y) = mul(x,y);

        // imul
        x = imul(x,y);

        // xor
        x = xor(y,z[1]);

        // land
        x = band(y,z[1]);

        // lor
        x = bor(y,z[1]);
  
        // shift-left
        x = shr(y,10);
        // cf,x = y >> 10; // unsupported at the moment

        // shift-right
        x = shl(y,10);
        // cf,x = y << 10; // unsupported at the moment

        // for loops
        for i in (0..10) {
            z[i] = add(z[i],1);
            if (i == 0) {
                z[1] = adc(z[1],1);
            }
        }

        if cf {
            z[1] = add(z[1],1);
        }

        if !cf {
            z[1] = add(z[1],1);
        }

        while cf {
            (cf,x) = add(x,x);
        }
    }
}

/*
START:CMD
#ARG="renumber_fun_unique,save[/tmp/before.mil][fun=test],test_conv[test],save[/tmp/after.mil][fun=test]"
ARG="renumber_fun_unique,test_conv[test]"
END:CMD
*/
