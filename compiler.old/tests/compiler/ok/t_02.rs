fn foo(x: stack! (b64),  y: stack! (b64), z: reg! (b1)) -> stack! (b64) {
    var! {
        w : stack! (b64);
    }
    code! {
        w = x;
        w = add(w,x);
        if (w == 5) {
            (z, x) = add(x,w);
            (z, x) = add(x,y);
        }
    }
    return x
}

/*
START:CMD
ARG="renumber_reuse,print[input][types]"
END:CMD
*/
