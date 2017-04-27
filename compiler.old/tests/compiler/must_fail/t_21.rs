/* function call with wrong return type */

fn bar() -> reg! (b64) {
    var! {
        x : reg! (b64);
    }
    code! {
        x = b64!(42);
    }
    return x
}

fn foo() {
    var! {
        x: stack! (b64);
    }
    code! {
        x = bar();
    }
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
