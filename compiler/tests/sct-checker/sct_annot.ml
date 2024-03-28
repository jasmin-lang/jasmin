open Jasmin
open Utils
open SecurityAnnotations

let roundtrip (pp : 'a pp) (read : 'a Angstrom.t) (x : 'a) =
  let s = Format.asprintf "%a" pp x in
  match Angstrom.parse_string ~consume:All read s with
  | Ok c ->
      let r = Format.asprintf "%a" pp c in
      assert (r = s);
      assert (c = x)
  | Error rule -> failwith (Format.asprintf "%s failed at %s" s rule)

let simple_level () =
  List.iter
    (roundtrip PP.simple_level Parse.simple_level)
    [ Public; Secret; Named "a"; Named "bcd1_2e" ]

let level () =
  List.iter
    (roundtrip PP.level Parse.level)
    [
      (let helo = Named "helo" in
       { normal = helo; speculative = helo });
      { normal = Named "low"; speculative = Named "high" };
      transient;
    ]

let typ () =
  List.iter
    (roundtrip PP.typ Parse.typ)
    [
      Msf;
      Direct public;
      Indirect
        { ptr = secret; value = { normal = Secret; speculative = Named "n" } };
    ]

let signature () =
  List.iter
    (roundtrip PP.signature Parse.signature)
    [
      { arguments = []; results = [] };
      { arguments = [ Direct public ]; results = [] };
      { arguments = []; results = [ Direct secret ] };
      {
        arguments =
          [
            Direct secret;
            Indirect
              {
                ptr = { normal = Named "n"; speculative = Secret };
                value = secret;
              };
          ];
        results = [ Direct public; Direct public ];
      };
    ]

let () =
  simple_level ();
  level ();
  typ ();
  signature ()
