type token =
  | Id of (string)
  | TRUE
  | FALSE
  | OR
  | AND
  | XOR
  | NEG
  | LPAREN
  | RPAREN
  | EOF

val expr :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> BeAst.bexpr
