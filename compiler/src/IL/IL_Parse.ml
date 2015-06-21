module PU = ParserUtil

let stmt =
  PU.wrap_error
    (fun sbuf ->
      try  IL_Parser.stmt IL_Lexer.lex sbuf
      with IL_Parser.Error -> raise PU.ParserError)
