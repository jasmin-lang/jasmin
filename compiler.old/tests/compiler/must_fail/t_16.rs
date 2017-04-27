// variable z not used

fn foo(_x: stack! (b64)) {
    var! {
        _y: stack! (b64);
        z: stack!  (b64);
    }
}

/*
START:CMD
ARG="print[input]"
END:CMD
*/
