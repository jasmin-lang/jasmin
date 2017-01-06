fn bar1(x: reg! (b64),y: reg! (b64), c: reg! (b1)) -> (reg! (b64), reg! (b1), reg! (b64)) {
    code! {
        x = sub_v(x,y);
    }
    return (x,c,y)
}

fn foo1(x: reg! (b64), y: reg! (b64), c: reg! (b1)) -> (reg! (b64),reg! (b1),reg! (b64)) {
    code! {
        x = add_v(x,y);
        (x,c,y) = inl!{ bar1(x,y,c) };
    }
    return (x,c,y)
}

fn test() {
    var! {
        u:   reg!    (b64);
        v:   reg!    (b64);
        cf:  reg!    (b1);
        u_:  reg!    (b64);
        v_:  reg!    (b64);
        cf_: reg!    (b1);
        i:   inline! (b64);
    }

    code! {
        u = 0;
        v = 0;

        u_,cf_,v_ = inl!{ foo1(u,v,cf) };
        for i in (0..10) {
            while cf {
                if cf {
                    u_,cf_,v_ = inl!{ foo1(u,v,cf) };
                } else {
                    u_,cf_,v_ = inl! { bar1(u,v,cf) };
                }
            }
        }
    }
}

/*
START:CMD
#ARG="renumber_module_unique,save[/tmp/before.mil][],cert_inline[test],save[/tmp/after.mil][]"
ARG="renumber_module_unique,cert_inline[test],print[after_inlining]"
END:CMD
*/
