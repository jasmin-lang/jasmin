fn foo() -> stack! (b64) {
    var! {
        x : stack! (b64);
    }
    code! {
        y = x;
    }
    return x
}

/*
START:CMD
ARG="print[input]"
END:CMD
*/
