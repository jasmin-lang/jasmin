fn foo1(x: reg! (b64), y : reg! (b64), c : reg! (b1)) -> (reg! (b64),reg! (b1), reg! (b64)) {
  return (x,c,y)
}

fn bar1(x: reg! (b64), y: reg! (b64), c: reg! (b1)) -> (reg! (b64),reg! (b1), reg! (b64)) {
  return (x,c,y)
}

fn test() {
    var! {
        u:   reg! (b64);
        v:   reg! (b64);
        cf:  reg! (b1);
        u_:  reg! (b64);
        v_:  reg! (b64);
        cf_: reg! (b1);
    }

    code! {
        (u_,cf_,v_) = foo1(u,v,cf);
        (u_,cf_,v_) = bar1(u,v,cf);
        (u_,cf_,v_) = bar1(u,v,cf);
        (u_,cf_,v_) = foo1(u,v,cf);
    }
}

/*
START:CMD
#ARG="renumber_fun_unique,save[/tmp/before.mil][fun=test],test_conv[test],save[/tmp/after.mil][fun=test]"
ARG="renumber_fun_unique,test_conv[test]"
END:CMD
*/
