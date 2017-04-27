/* function call with wrong return arity */

fn bar() {
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
