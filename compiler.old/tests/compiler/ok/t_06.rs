// FIXME: parser ignores comments
//        => we inline to test strip_comments

fn bar() {
}

fn foo(x, y : stack u64, z : reg bool) -> stack u64 {
  w : stack u64;
  w = x;
  w += x;
  if (w = 5) {
    z, x += w;
    z, x += y;
  }
  bar();
  return x;
}

/*
START:CMD
ARG="inline[foo],strip_comments[foo],print[input][types,fun=foo]"
END:CMD
*/
