// same function name used twice

decl! { fn foo(x: stack! (b64)); }

decl! { fn foo(x: stack! (b64)); }

/*
START:CMD
ARG="print[input]"
END:CMD
*/
