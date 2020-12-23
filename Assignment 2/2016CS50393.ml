type exp = Tup of exp list | Bool of bool | Const of int | VarI of string | VarB of string | VarT of string | Lst of exp*exp | LstEq of exp*exp | Grt of exp*exp | GrtEq of exp*exp | Equal of exp*exp | Implies of exp*exp | Or of exp*exp | And of exp*exp | Not of exp | Sum of exp*exp | Sub of exp*exp | Div of exp*exp | Mul of exp*exp | Exp of exp*exp | Abs of exp | Mod of exp*exp | Proj of exp*exp;;
type opcode = CONST of int | TUP of opcode list list| VARB of string| VARI of string | VART of string | BOOL of bool | SUM | SUB | MUL | DIV | EXPO | MOD | ABS | LST | LSTEQ | GRT | GRTEQ | EQUAL | AND | OR | NOT | IMPLIES | PROJ;;
exception Undefined;;
type answer = I of int | B of bool | L of answer list;;

let rec map f x = match x with
 			[] -> []
 		|   l::n -> (f l) ::(map f n);;

let rec map2 f (x,y) = match (x,y) with
 			(n,[]) -> n
 		|   (n,a::b) -> map2 f (n@[f ([],a)],b);;

(*Extract functions to extract god value from answer type*)
let extractI x = match x with 
			(I m) -> m
		|   _ -> raise(Undefined);;
let extractB x = match x with 
			(B m) -> m
		|   _ -> raise(Undefined);;
let extractL x = match x with 
			(L m) -> m
		|   _ -> raise(Undefined);;

(*Extract functions to convert answer to exp type*)
let rec convert x = match x with
			I m -> Const m
		|   B m -> Bool m
		|   L m -> Tup (map convert m)
		|   _ -> raise(Undefined);;

(*Integer evaluations*)
let rec evalInt f rho t = match t with
			 Const n -> n
		|    VarI s -> (extractI (rho s))
		|    Sum (a, b) -> (evalInt f rho a) + (evalInt f rho b)
		|    Sub (a, b) -> (evalInt f rho a) - (evalInt f rho b)
		|    Div (a, b) -> (evalInt f rho a) / (evalInt f rho b)
		|    Mul (a, b) -> (evalInt f rho a) * (evalInt f rho b)
		|    Exp (a, b) -> int_of_float((float_of_int(evalInt f rho a)) ** (float_of_int(evalInt f rho b)))
		|    Mod (a, b) -> (evalInt f rho a) mod (evalInt f rho b)
		|    Abs a -> if (evalInt f rho a) > 0 then (evalInt f rho a) else (-1 * (evalInt f rho a))
		|    Proj (Tup x, Const i) -> (extractI (f rho (List.nth x i)))
		|    Proj (VarT x, Const i) -> (extractI (f rho (convert (List.nth (extractL (rho x)) i))))
		|    Proj (Tup x, VarI i) -> (extractI (f rho (List.nth x (extractI (rho i)))))
		|    Proj (VarT x, VarI i) -> (extractI (f rho (convert (List.nth (extractL (rho x)) (extractI (rho i))))))
		|    _ -> raise (Undefined);;

(*Boolean evaluations*)
let rec evalBool f rho  t = match t with
			 Bool n -> n
		|    VarB s -> (extractB (rho s))
		|    Lst (a,b) -> if (evalInt f rho a) < (evalInt f rho b) then true else false
		|    LstEq (a,b) -> if (evalInt f rho a) <= (evalInt f rho b) then true else false
		|    Grt (a,b) -> if (evalInt f rho a) > (evalInt f rho b) then true else false
		|    GrtEq (a,b) -> if (evalInt f rho a) >= (evalInt f rho b) then true else false
		|    Equal (a,b) -> if (evalInt f rho a) = (evalInt f rho b) then true else false
		|    And (a,b) -> (evalBool f rho a)&&(evalBool f rho b)
		|    Or (a,b) -> (evalBool f rho a)||(evalBool f rho b)
		|    Implies (a,b) -> (not (evalBool f rho a))||(evalBool f rho b)
		|    Not a -> not (evalBool f rho a)
		|    Proj (Tup x, Const i) -> (extractB (f rho (List.nth x i)))
		|    Proj (VarT x, Const i) -> (extractB (f rho (convert (List.nth (extractL (rho x)) i))))
		|    Proj (Tup x, VarI i) -> (extractB (f rho (List.nth x (extractI (rho i)))))
		|    Proj (VarT x, VarI i) -> (extractB (f rho (convert (List.nth (extractL (rho x)) (extractI (rho i))))))
		|    _ -> raise (Undefined);;

(*All evaluations*)
let rec eval rho t = match t with
			Const n -> I n
		|   Bool n -> B n
		|   VarB n -> rho n
		|   VarI n -> rho n
		|   VarT n -> rho n
		|   Tup n -> L (map (eval rho) n)
		|	Lst(a,b) -> B(evalBool eval rho t)
		|   LstEq(a,b) -> B(evalBool eval rho t)
		|   Grt(a,b) -> B(evalBool eval rho t)
		|   GrtEq(a,b) -> B(evalBool eval rho t)
		|   Equal(a,b) -> B(evalBool eval rho t)
		|   And(a,b) -> B(evalBool eval rho t)
		|   Or(a,b) -> B(evalBool eval rho t)
		|   Not a -> B(evalBool eval rho t)
		|   Proj (Tup x, Const i) -> (eval rho (List.nth x i))
		|   Proj (VarT x, Const i) -> (eval rho (convert (List.nth (extractL (rho x)) i)))
		|   Proj (Tup x, VarI i) -> (eval rho (List.nth x (extractI (rho i))))
		|   Proj (VarT x, VarI i) -> (eval rho (convert (List.nth (extractL (rho x)) (extractI (rho i)))))
		|    _ -> I(evalInt eval rho t);;

let rec compile e = match e with
			Const n -> [CONST n]
		|   VarB n -> [VARB n]
		|   VarI n -> [VARI n]
		|   VarT n -> [VART n]
		|   Bool n -> [BOOL n]
		|   Tup s -> [TUP (map compile s)]
		|   Sum(a,b) -> (compile a) @ (compile b) @ [SUM]
		|   Sub(a,b) -> (compile a) @ (compile b) @ [SUB]
		|   Mul(a,b) -> (compile a) @ (compile b) @ [MUL]
		|   Div(a,b) -> (compile a) @ (compile b) @ [DIV]
		|   Exp(a,b) -> (compile a) @ (compile b) @ [EXPO]
		|   Mod(a,b) -> (compile a) @ (compile b) @ [MOD]
		|   Abs(a) -> (compile a) @ [ABS]
		|   Lst(a,b) -> (compile a) @ (compile b) @ [LST]
		|   LstEq(a,b) -> (compile a) @ (compile b) @ [LSTEQ]
		|   Grt(a,b) -> (compile a) @ (compile b) @ [GRT]
		|   GrtEq(a,b) -> (compile a) @ (compile b) @ [GRTEQ]
		|   Equal(a,b) -> (compile a) @ (compile b) @ [EQUAL]
		|   And(a,b) -> (compile a) @ (compile b) @ [AND]
		|   Or(a,b) -> (compile a) @ (compile b) @ [OR]
		|   Implies(a,b) -> (compile a) @ (compile b) @ [IMPLIES]
		|   Not(a) -> (compile a) @ [NOT]
		|   Proj(x,Const i) -> (compile x) @ [CONST i] @ [PROJ]
		|   Proj(x,VarI i) -> (compile x) @ [VARI i] @ [PROJ]
		|   _ -> raise(Undefined);;

let rec execute table (s,c) = match (s,c) with
			(s,[]) -> List.hd s
		|   (s,(CONST n)::y) -> execute table (I n::s,y)
		|   (s,(BOOL n)::y) -> execute table (B n::s,y)
		|   (s,(VARB n)::y) -> execute table ((table n)::s,y)
		|   (s,(VARI n)::y) -> execute table ((table n)::s,y)
		|   (s,(VART n)::y) -> execute table ((table n)::s,y)
		|   (s,(TUP n)::y) -> execute table ((L (map2 (execute table) ([], n)))::s,y) (*Evaluate all positions before adding*)
		|   (I b::I a::c,SUM::y) -> execute table (I (a+b)::c,y)
		|   (I b::I a::c,SUB::y) -> execute table (I (a-b)::c,y)
		|   (I b::I a::c,DIV::y) -> execute table (I (a/b)::c,y)
		|   (I b::I a::c,MUL::y) -> execute table (I (a*b)::c,y)
		|   (I b::I a::c,EXPO::y) -> execute table (I (int_of_float((float_of_int(a)) ** (float_of_int(b))))::c,y)
		|   (I b::I a::c,MOD::y) -> execute table (I (a mod b)::c,y)
		|   (I a::c,ABS::y) -> if a < 0 then execute table (I (-1*a)::c,y) else execute table (I a::c,y)
		|   (I b::I a::c,LST::y) -> if a < b then execute table (B (true)::c,y) else execute table (B (false)::c,y)
		|   (I b::I a::c,LSTEQ::y) -> if a <= b then execute table (B (true)::c,y) else execute table (B (false)::c,y)
		|   (I b::I a::c,GRT::y) -> if a > b then execute table (B (true)::c,y) else execute table (B (false)::c,y)
		|   (I b::I a::c,GRTEQ::y) -> if a >= b then execute table (B (true)::c,y) else execute table (B (false)::c,y)
		|   (I b::I a::c,EQUAL::y) -> if a = b then execute table (B (true)::c,y) else execute table (B (false)::c,y) 
		|   (B b::B a::c,AND::y) -> execute table (B (a&&b)::c,y)
		|   (B b::B a::c,OR::y) -> execute table (B (a||b)::c,y)
		|   (B b::B a::c,IMPLIES::y) -> execute table (B ((not a) || b)::c,y)
		|   (B a::c,NOT::y) -> execute table ((B (not a))::c,y)
		|   (I i::L x::c, PROJ::y) -> execute table ((List.nth x i)::c,y)
		|   _ -> raise(Undefined);;

(*Test Cases*)

let table t = match t with
		"t" -> B true
	|   "f" -> B false
	|	"x" -> I 2
	|   "y" -> I 1
	|	"l" -> L [I 2;B false;I 7]
	|   "m" -> L [B true] ;;
let rho t = match t with
		"t" -> B true
	|   "f" -> B false
	|	"x" -> I 2
	|   "y" -> I 1
	|	"l" -> L [I 2;B false;I 7]
	|   "m" -> L [B true] 
	|    _ -> I 0;;

let var1 = Sum (Const 1, Const 2);;
let var2 = And (Bool true, Bool false);;
let var3 = Tup [Const 5; var2; var1; And(var2,var2); Proj(VarT "l",VarI "x")];;
let var4 = Tup [VarI "x"; And(VarB "t",VarB "f");Sum(Exp(VarI "x", Const 2),Const 10); Abs(Const (-3)); Mod(Const 6, Const 4)];;
let var5 = Proj(var4, Const 2);;
let var6 = Proj(var4, VarI "x");;
let var7 = Lst(var1, Proj(var3,Const 4));;
let var8 = Div(Const 6, Const 4);;
let test1 = eval rho var1;;
let test2 = eval rho var2;;
let test3 = eval rho var3;;
let test4 = eval rho var4;;
let test5 = eval rho var5;;
let test6 = eval rho var6;;
let test7 = eval rho var7;;
let test8 = eval rho var8;;
let compile1 = compile var1;;
let compile2 = compile var2;;
let compile3 = compile var3;;
let compile4 = compile var4;;
let compile5 = compile var5;;
let compile6 = compile var6;;
let compile7 = compile var7;;
let compile8 = compile var8;;
let execute1 = execute table ([],compile1);;
let execute2 = execute table ([],compile2);;
let execute3 = execute table ([],compile3);;
let execute4 = execute table ([],compile4);;
let execute5 = execute table ([],compile5);;
let execute6 = execute table ([],compile6);;
let execute7 = execute table ([],compile7);;
let execute8 = execute table ([],compile8);;

