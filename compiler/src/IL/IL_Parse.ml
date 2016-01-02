module PU = ParserUtil

let modul =
  PU.wrap_error
    (fun sbuf ->
      try  IL_Parser.modul IL_Lexer.lex sbuf
      with IL_Parser.Error -> raise PU.ParserError)
