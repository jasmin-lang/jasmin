// reuse the same number for different names
// FIXME: reactivate when interpreter done (requires this property)

fn test(x.1, y.1 : stack! (b64)) -> stack! (b64) {
    code! {
        x.1 = add(x.1,y.1);
    }
  return x.1
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
