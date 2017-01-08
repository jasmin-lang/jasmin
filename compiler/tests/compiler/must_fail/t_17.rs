/* function call with wrong argument arity */

fn bar() {
}

fn foo() {
    var! {
        x: stack! (b64);
    }
    code! {
        x = b64!(42);
        bar(x);
    }
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
