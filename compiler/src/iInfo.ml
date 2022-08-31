type t = Location.i_loc * unit * Syntax.annotations
let dummy = Location.i_dummy, (), []

let mk loc ii a = loc, ii, a
let split x = x
