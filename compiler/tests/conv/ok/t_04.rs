fn test() {
    var! {
        x: reg! ([b64; 10]);
        y: reg! ([b64; 10]);
        z: reg! ([b64; 100]);
        i: inline! (b64);
        j: inline! (b64);
    }
    
    code! {
        for i in (0..10) {
            x[i] = i;
            y[i] = imul(i,i);
        }
        
        for i in (0..3) {
            for j in (0..3) {
                z[j*10 + i] = add_v(x[i],y[i]);
            }
        }
    }
}

/*
START:CMD
#ARG="renumber_module_unique,save[/tmp/before.mil][],cert_inline[test],save[/tmp/after.mil][]"
#ARG="renumber_module_unique,cert_unroll[test],typecheck,print[after_unrolling]"
ARG="renumber_module_unique,cert_unroll[test],typecheck"
END:CMD
*/
