{
open MyParser
exception Eof
exception Unexpected_token
}

let whiteSpace = [' ' '\t' '\n']
let end = '.'
let cond = ":-"
let true = "true"
let false = "false"
let append = "|"
let not = "not"
let openPar = "("
let closPar = ")"
let openSq = "["
let closSq = "]"
let comma = ","
let equ = "="
let notEqu = ("\\=" | "\\==")
let var = (['A'-'Z']['a'-'z''A'-'Z''0'-'9''_']*)
let cons = (['a'-'z']['a'-'z''A'-'Z''0'-'9''_']*)
let cut = "!"
let fail = "fail"
let intt = (['0'-'9']['a'-'z''A'-'Z''0'-'9''_']*)


rule token = parse
  | whiteSpace         { token lexbuf } (* skip spaces *)
  | end                { END }
  | cut                { CUT }
  | fail               { FAIL }
  | cond               { COND }
  | true               { TRUE }
  | false              { FALSE }
  | append             { APP }
  | not                { NOT }
  | openPar            { LPAREN }
  | closPar            { RPAREN }
  | openSq             { LSQ }
  | closSq             { RSQ }
  | comma              { COMMA }
  | equ                { EQU }
  | notEqu             { NOTEQ }
  | var as variable    { VAR(variable) }
  | cons as const      { CONS(const) }
  | eof                { EOF }
  | intt as chr        { CONS(chr) }
  | _ as chr           { failwith ("lex error: "^(Char.escaped chr))}
