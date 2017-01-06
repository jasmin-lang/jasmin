/* function call with wrong argument type */

fn bar(_x: reg! (b64)) {
}

fn foo() {
    var! {
        x: stack! (b64);
    }
    code! {
        x = 42;
        bar(x);
    }
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
