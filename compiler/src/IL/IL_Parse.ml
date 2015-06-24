module PU = ParserUtil

let efuns =
  PU.wrap_error
    (fun sbuf ->
      try  IL_Parser.efuns IL_Lexer.lex sbuf
      with IL_Parser.Error -> raise PU.ParserError)
