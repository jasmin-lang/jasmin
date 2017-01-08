// use undeclared parameter

fn test(x: stack! (b64)) -> stack! (b64) {
    code! {
        x = b64!(undef_var_param);
    }
  return x
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
