module PU = ParserUtil

let modul =
  PU.wrap_error
    (fun sbuf ->
      try  IL_Parser.modul IL_Lexer.lex sbuf
      with IL_Parser.Error -> raise(PU.ParserError))

let modul_rust =
  PU.wrap_error
    (fun sbuf ->
      try  ILR_Parser.modul ILR_Lexer.lex sbuf
      with ILR_Parser.Error -> raise(PU.ParserError))
