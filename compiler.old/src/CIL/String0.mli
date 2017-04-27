open Ascii

type string =
| EmptyString
| String of ascii * string
