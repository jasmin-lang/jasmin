(* * License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

open Core.Std
open IL_Lang

let std_lib_file = "lib/std.rs"

let std_protos () =
  let s = In_channel.read_all std_lib_file in
  (* eprintf "Parsing %s as %s\n\n%!" file ftype; *)
  match IL_Parse.modul std_lib_file s with
  | `ParseOk res        -> res.mod_funprotos
  | `ParseError(pinfos) -> P.failloc_c s pinfos
