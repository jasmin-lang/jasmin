#![allow(non_upper_case_globals)] 
#![allow(dead_code)] 
#![allow(unused_imports)] 
#![allow(unused_mut)] 
#![allow(unused_assignments)] 

//#[macro_use] extern crate jasmin;

rust! {
    use jasmin::jasmin::*;
    use jasmin::U64::*;
}

rust! {
    mod test {
        use jasmin::jasmin::*;
        use jasmin::U64::*;

        #[test]
        fn test1() {
            ::foo3(0.to_jval());
        }
    }
}

// UNSUPPORTED FOR NOW:
// const n : b64 = jconst!(10); // constants with default values, can be overriden

// UNSUPPORTED: we can use a variable name that is ignored
// fn foo1(x : stack! (b64)) -> (stack! (b64), reg! (b64), reg! (b1));

// UNSUPPORTED: we can also leave out variable names
// fn foo2(stack u64, stack u64[n], x,x,x : stack u64) -> stack u64[n] =
//   python print_foo;

// nothing
fn foo3(_x: stack! (b64)) {
}


// decl only
pub fn foo4(_x: stack! (b64)) {
    var! {
        _y: stack! (b64); // will not be printed
    }
}

// body only
pub fn foo5(mut x: stack! (b64)) {
    code! {
        x = add_v(x,x);
    }
}


// return only
fn foo6(x: stack! (b64)) -> stack! (b64) {
    return x
}


// deck + body
fn foo7(mut x: stack! (b64)) {
    var! {
        y: stack! (b64);
    }
    
    code! {
        y = jc!(0);
        x = add_v(x,y);
    }
}

// decl + return
fn foo8(x : stack! (b64)) -> (stack! (b64),stack! (b64)) {
    var! {
        _y: stack! (b64);
    }
    return (x,x)
}

// body + return
fn foo9(mut x: stack! (b64)) -> stack! (b64) {
    code! {
        x = add_v(x,x);
    }

    return x
}

// decl + body + return
fn foo10(mut x: stack! (b64), y: stack! (b64), mut z: reg! (b1)) -> stack! (b64) {
    var! {
        w : stack! (b64);
    }
    
    code! {
        w = x;
        x = jc!(5);
        w = add_v(w,x);
        if (w == jc!(5)) {
            (z, x) = add(x,w);
            (z, x) = add(x,y);
        }
        x = adc_v(x,x,z);
    }
    return x
}

/*
START:CMD
ARG="print[input][rust]"
END:CMD
*/
