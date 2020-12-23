exception Undefined;;
type variable = V of string;;
type exp = Var of variable | Lambda of variable*exp | Func of exp*exp | Const of int | Plus of exp*exp | Sub of exp*exp | Mul of exp*exp | Div of exp*exp | Bool of bool | And of exp*exp | Or of exp*exp | Not of exp | Implies of exp*exp | Ite of exp*exp*exp | Grt of exp*exp | Lst of exp*exp | LstEq of exp*exp | GrtEq of exp*exp | Equ of exp*exp | LetDef of variable*exp*exp | Tup of exp list | Proj of exp*exp | Mod of exp*exp | Abs of exp | Pow of exp*exp;;
type opcode = PROJ | TUP of opcode list list | APP | RET | CLOS of (opcode)*(opcode list) | VAR of string | PLUS | SUB | MUL | DIV | CONST of int | BOOL of bool | AND | OR | NOT | COND of (opcode list)*(opcode list) | GRT | LST | GRTEQ | LSTEQ | EQU | IMPLIES | BIND of variable | UNBIND of variable | MOD | POW | ABS;;

type vclosureSECD = Close of (table list) * variable *(opcode list) and table = Tab of (variable*stackanswer) and stackanswer = Cl of vclosureSECD | I of int | B of bool | T of stackanswer list;;
type secdPart1 = MySecd of (stackanswer list)*(table list)*(opcode list);;
type secd = SECD of secdPart1 * (secdPart1 list);;

type myopcodes = LAZY | PlusFirst | PlusSecond | SubFirst | SubSecond | DivFirst | DivSecond | MulFirst | MulSecond | AndFirst | AndSecond | OrFirst | OrSecond | NotFirst | ImpliesFirst | ImpliesSecond | GrtFirst | GrtSecond | LstFirst | LstSecond | GrtEqFirst | GrtEqSecond | LstEqFirst | LstEqSecond | EquFirst | EquSecond | CondKriv of exp*exp | TupKriv of exp list | ProjKriv of exp | DefFirst of exp | PowFirst | PowSecond | ModFirst | ModSecond | AbsFirst;;
type closureKRIV = KrivCLos of (tableKriv list)*(exp) and tableKriv = TabK of (variable*closureKRIV);;
type krivstack = OP of closureKRIV | OPC of myopcodes | Exp of exp | Va of variable | Ta of tableKriv list;;
type kriv = KRIV of (closureKRIV)*(krivstack list);;


let rec lookupTable tab vari = match tab with 
		[] -> raise (Undefined)
	|   (Tab((V(s)),b))::xs -> if (s = vari) then b else lookupTable xs vari;;


let rec lookupTableKriv tab vari = match tab with 
		[] -> raise (Undefined)
	|   (TabK(s,b))::xs -> if (s = vari) then b else lookupTableKriv xs vari;;

let rec map f d t = match t with
		[] -> []
	|	a::b -> (f (SECD(MySecd([],d,a),[])))::(map f d b);;  

let rec map2 f d t = match t with
		[] -> []
	|	a::b -> (f (KrivCLos(d,a)))::(map2 f d b);;  

let rec map3 f d t c = match t with
		[] -> []
	|	a::b -> (f (KRIV(KrivCLos(d,a),c)))::(map3 f d b c);;  

let rec remove d x = match d with
		[] -> []
	|   Tab(a,c)::b -> if a = x then b else (Tab(a,c))::(remove b x);; 	

let rec removeKriv d x = match d with
		[] -> []
	|   TabK(a,KrivCLos(z,q))::b -> if a = x then b else (TabK(a,KrivCLos(z,q)))::(removeKriv b x);; 	

let getVar e = match e with
		Var(w) -> w;;

let rec unpack t = match t with
		KrivCLos(a,Const y) -> Const y
	|	KrivCLos(a,Bool y) -> Bool y
	|	KrivCLos(a,Tup z) -> Tup (map2 unpack a z)
	|   KrivCLos(a,Pow(e1,e2))->Pow(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Mod(e1,e2))->Mod(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Plus(e1,e2))->Plus(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Mul(e1,e2)) -> Mul(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Sub(e1,e2)) -> Sub(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Div(e1,e2)) -> Div(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,And(e1,e2)) -> And(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Or(e1,e2)) -> Or(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Implies(e1,e2)) -> Implies(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Not(e1)) -> Not(unpack (KrivCLos(a,e1)))
	|   KrivCLos(a,Abs(e1)) -> Abs(unpack (KrivCLos(a,e1)))
	|   KrivCLos(a,Grt(e1,e2)) -> Grt(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,GrtEq(e1,e2)) -> GrtEq(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Lst(e1,e2)) -> Lst(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,LstEq(e1,e2)) -> LstEq(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Equ(e1,e2)) -> Equ(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Func(e1,e2)) -> Func(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))
	|   KrivCLos(a,Lambda(e1,e2)) -> Lambda(getVar (unpack (KrivCLos(removeKriv a e1, Var e1))), unpack (KrivCLos(removeKriv a e1,e2)))
	|   KrivCLos(a,Ite(e1,e2,e3)) -> Ite(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)), unpack (KrivCLos(a,e3)))
	|   KrivCLos(a,LetDef(e1,e2,e3)) -> LetDef(getVar (unpack (KrivCLos(a,Var e1))), unpack (KrivCLos(a,e2)), unpack (KrivCLos(a,e3)))
	|   KrivCLos(a,Proj(e1,e2)) -> Proj(unpack (KrivCLos(a,e1)), unpack (KrivCLos(a,e2)))   
	|   KrivCLos(a,Var z) -> try unpack (lookupTableKriv a z) with Undefined -> (Var z);;

let rec compile e = match e with 
		Const a -> [CONST a]
	|	Bool a -> [BOOL a]
	|	LetDef(a,b,c) -> (compile b)@[BIND(a)]@(compile c)@[UNBIND(a)]
	|	Ite(a,b,c) -> (compile a)@[COND((compile b),(compile c))]
	|	Mod(a,b) -> (compile a)@(compile b)@[MOD]
	|	Pow(a,b) -> (compile a)@(compile b)@[POW]
	|	And(a,b) -> (compile a)@(compile b)@[AND]
	|	Implies(a,b) -> (compile a)@(compile b)@[IMPLIES]
	|	Grt(a,b) -> (compile a)@(compile b)@[GRT]
	|	Lst(a,b) -> (compile a)@(compile b)@[LST]
	|	GrtEq(a,b) -> (compile a)@(compile b)@[GRTEQ]
	|	LstEq(a,b) -> (compile a)@(compile b)@[LSTEQ]
	|	Equ(a,b) -> (compile a)@(compile b)@[EQU]
	|	Or(a,b) -> (compile a)@(compile b)@[OR]
	|	Not(a) -> (compile a)@[NOT]
	|	Abs(a) -> (compile a)@[ABS]
	|	Plus(a,b) -> (compile a)@(compile b)@[PLUS]
	|	Mul(a,b) -> (compile a)@(compile b)@[MUL]
	|	Div(a,b) -> (compile a)@(compile b)@[DIV]
	|	Sub(a,b) -> (compile a)@(compile b)@[SUB]
	|   Tup s -> [TUP (List.map compile s)]
	|   Proj(x,y) -> (compile x) @ (compile y) @ [PROJ]
	|	Func(a,b) -> (compile a)@(compile b)@[APP]
	|   Lambda ((V a),b)-> [CLOS(VAR a,((compile b)@[RET]))]
	|   Var (V a) -> [VAR a];;

let rec secdMachine e = match e with 
		SECD(a,b) -> match a with 
				MySecd([],c,[]) -> raise (Undefined)
			|	MySecd([I z],c,[]) -> I z	
			|	MySecd([B z],c,[]) -> B z	
			|	MySecd(c,d,(CONST z)::f) -> secdMachine (SECD(MySecd((I z)::c,d,f),b))
			|	MySecd(c,d,(BOOL z)::f) -> secdMachine (SECD(MySecd((B z)::c,d,f),b))
			|	MySecd(c,d,(VAR z)::f) -> secdMachine (SECD(MySecd(((lookupTable d z))::c,d,f),b))				
			|	MySecd((B ff)::c,d,(COND(q,w))::f) -> if (ff = true) then secdMachine (SECD(MySecd(c,d,q@f),b)) else secdMachine (SECD(MySecd(c,d,w@f),b))
			|	MySecd((I ff)::(I g)::c,d,(GRT)::f) -> if (g>ff) then  secdMachine (SECD(MySecd((B true)::c,d,f),b)) else secdMachine (SECD(MySecd((B false)::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(LST)::f) -> if (g<ff) then  secdMachine (SECD(MySecd((B true)::c,d,f),b)) else secdMachine (SECD(MySecd((B false)::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(GRTEQ)::f) -> if (g>=ff) then  secdMachine (SECD(MySecd((B true)::c,d,f),b)) else secdMachine (SECD(MySecd((B false)::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(LSTEQ)::f) -> if (g<=ff) then  secdMachine (SECD(MySecd((B true)::c,d,f),b)) else secdMachine (SECD(MySecd((B false)::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(EQU)::f) -> if (g=ff) then  secdMachine (SECD(MySecd((B true)::c,d,f),b)) else secdMachine (SECD(MySecd((B false)::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(POW)::f) -> secdMachine (SECD(MySecd(I (int_of_float(float_of_int(g) ** float_of_int(ff)))::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(MOD)::f) -> secdMachine (SECD(MySecd((I (g mod ff))::c,d,f),b))
			|	MySecd((B ff)::(B g)::c,d,(AND)::f) -> secdMachine (SECD(MySecd((B (ff&&g))::c,d,f),b))
			|	MySecd((B ff)::(B g)::c,d,(IMPLIES)::f) -> secdMachine (SECD(MySecd((B ((not g)||ff))::c,d,f),b))
			|	MySecd((B ff)::(B g)::c,d,(OR)::f) -> secdMachine (SECD(MySecd((B (ff||g))::c,d,f),b))
			|	MySecd((B ff)::c,d,(NOT)::f) -> secdMachine (SECD(MySecd((B (not ff))::c,d,f),b))
			|	MySecd((I ff)::c,d,(ABS)::f) -> secdMachine (SECD(MySecd((I (abs ff))::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(PLUS)::f) -> secdMachine (SECD(MySecd((I (ff+g))::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(SUB)::f) -> secdMachine (SECD(MySecd((I (g-ff))::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(MUL)::f) -> secdMachine (SECD(MySecd((I (ff*g))::c,d,f),b))
			|	MySecd((I ff)::(I g)::c,d,(DIV)::f) -> secdMachine (SECD(MySecd((I (g/ff))::c,d,f),b))
			|	MySecd(ff::c,d,(BIND(x))::f) -> secdMachine (SECD(MySecd(c,Tab(x,ff)::d,f),b))
			|	MySecd(c,d,(UNBIND(x))::f) -> secdMachine (SECD(MySecd(c,(remove d x),f),b))
			|   MySecd(c,d,(TUP(aa))::f) -> secdMachine (SECD(MySecd(T(map secdMachine d aa)::c,d,f),b))
			|   MySecd(I(z)::T(aa)::c,d,PROJ::f) -> secdMachine (SECD(MySecd((List.nth aa z)::c,d,f),b))
			|	MySecd(c,d,((CLOS(VAR z,w))::x)) -> secdMachine (SECD(MySecd((Cl(Close(d,V z,w)))::c,d,x),b))
			| 	MySecd((p::(Cl(Close(y,u,i)))::r),d,((APP)::x)) -> secdMachine (SECD(MySecd([],(Tab(u,p)::y),i),(MySecd(r,d,x))::b))
			|   MySecd((p::r),d,((RET)::x)) -> match b with 
					MySecd(i,o,q)::z -> secdMachine (SECD(MySecd((p::i),o,q),z));;

let rec krivineMachine e = match e with 
		KRIV(a,b) -> match (a,b) with 
				((KrivCLos(x,Const(z))),[]) -> unpack (KrivCLos(x,Const(z)))
			|	((KrivCLos(x,Bool(z))),[]) -> unpack (KrivCLos(x,Bool(z)))
			|   ((KrivCLos(x,Var(z))),[]) -> unpack (lookupTableKriv x z)	
			|	((KrivCLos(x,Bool(u))),(OPC LAZY)::(Exp(Var z))::(Exp(Var q))::w) -> krivineMachine (KRIV((KrivCLos(TabK(q,KrivCLos([],Bool(u)))::x,Var z)),w))
			|	((KrivCLos(x,Const(u))),(OPC LAZY)::(Exp(Var z))::(Exp(Var q))::w) -> krivineMachine (KRIV((KrivCLos(TabK(q,KrivCLos([],Const(u)))::x,Var z)),w))
			|   ((KrivCLos(x,Var(z))),w) -> krivineMachine (KRIV((lookupTableKriv x z),w))	
			|   ((KrivCLos(x,Tup(z))),w) -> unpack (KrivCLos(x, Tup(map3 krivineMachine x z w)))

			|   ((KrivCLos(x,Ite(q,y,z))),w) -> krivineMachine (KRIV((KrivCLos(x,q)),(OPC (CondKriv(y,z)))::w)) 
			|   ((KrivCLos(x,Bool(z))),(OPC CondKriv(y,q))::w) -> if z = true then krivineMachine (KRIV((KrivCLos(x,y)),w)) else krivineMachine (KRIV((KrivCLos(x,q)),w))
			
			
			|   ((KrivCLos(x,Pow(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC PowSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC PowSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC PowFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC PowFirst)::(Exp (Const y))::w) ->krivineMachine (KRIV((KrivCLos(x,(Const (int_of_float(float_of_int(y)**float_of_int(z)))))),w))

			|   ((KrivCLos(x,Mod(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC ModSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC ModSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC ModFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC ModFirst)::(Exp (Const y))::w) ->krivineMachine (KRIV((KrivCLos(x,(Const(y mod z)))),w))

			|   ((KrivCLos(x,Plus(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC PlusSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC PlusSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC PlusFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC PlusFirst)::(Exp (Const y))::w) ->krivineMachine (KRIV((KrivCLos(x,(Const(z+y)))),w))

			|   ((KrivCLos(x,Mul(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC MulSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC MulSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC MulFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC MulFirst)::(Exp (Const y))::w) ->krivineMachine (KRIV((KrivCLos(x,(Const(z*y)))),w))
			
			|   ((KrivCLos(x,Sub(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC SubSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC SubSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC SubFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC SubFirst)::(Exp (Const y))::w) ->krivineMachine (KRIV((KrivCLos(x,(Const(y-z)))),w))
			
			|   ((KrivCLos(x,Div(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC DivSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC DivSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC DivFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC DivFirst)::(Exp (Const y))::w) ->krivineMachine (KRIV((KrivCLos(x,(Const(y/z)))),w))

			|   ((KrivCLos(x,And(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC AndSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Bool(z))),(OPC AndSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC AndFirst)::(Exp (Bool z))::w))
			|   ((KrivCLos(x,Bool(z))),(OPC AndFirst)::(Exp (Bool y))::w) ->krivineMachine (KRIV((KrivCLos(x,(Bool(z&&y)))),w))

			|   ((KrivCLos(x,Or(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC OrSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Bool(z))),(OPC OrSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC OrFirst)::(Exp (Bool z))::w))
			|   ((KrivCLos(x,Bool(z))),(OPC OrFirst)::(Exp (Bool y))::w) ->krivineMachine (KRIV((KrivCLos(x,(Bool(z||y)))),w))

			|   ((KrivCLos(x,Implies(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC ImpliesSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Bool(z))),(OPC ImpliesSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC ImpliesFirst)::(Exp (Bool z))::w))
			|   ((KrivCLos(x,Bool(z))),(OPC ImpliesFirst)::(Exp (Bool y))::w) ->krivineMachine (KRIV((KrivCLos(x,(Bool((not y)||z)))),w))

			|   ((KrivCLos(x,Not(y))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),OPC NotFirst::w)) 
			|   ((KrivCLos(x,Bool(y))),OPC NotFirst::w) ->krivineMachine (KRIV((KrivCLos(x,Bool(not y))),w)) 

			|   ((KrivCLos(x,Abs(y))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),OPC AbsFirst::w)) 
			|   ((KrivCLos(x,Const(y))),OPC AbsFirst::w) ->krivineMachine (KRIV((KrivCLos(x,Const(abs y))),w)) 

			|   ((KrivCLos(x,Grt(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC GrtSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC GrtSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC GrtFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC GrtFirst)::(Exp (Const y))::w) -> if y > z then krivineMachine (KRIV((KrivCLos(x,(Bool(true)))),w)) else krivineMachine (KRIV((KrivCLos(x,(Bool(false)))),w))

			|   ((KrivCLos(x,GrtEq(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC GrtEqSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC GrtEqSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC GrtEqFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC GrtEqFirst)::(Exp (Const y))::w) -> if y >= z then krivineMachine (KRIV((KrivCLos(x,(Bool(true)))),w)) else krivineMachine (KRIV((KrivCLos(x,(Bool(false)))),w))

			|   ((KrivCLos(x,Lst(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC LstSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC LstSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC LstFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC LstFirst)::(Exp (Const y))::w) -> if y < z then krivineMachine (KRIV((KrivCLos(x,(Bool(true)))),w)) else krivineMachine (KRIV((KrivCLos(x,(Bool(false)))),w))

			|   ((KrivCLos(x,LstEq(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC LstEqSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC LstEqSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC LstEqFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC LstEqFirst)::(Exp (Const y))::w) -> if y <= z then krivineMachine (KRIV((KrivCLos(x,(Bool(true)))),w)) else krivineMachine (KRIV((KrivCLos(x,(Bool(false)))),w))

			|   ((KrivCLos(x,Equ(y,z))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC EquSecond)::(Exp z)::w)) 
			|   ((KrivCLos(x,Const(z))),(OPC EquSecond)::(Exp y)::w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC EquFirst)::(Exp (Const z))::w))
			|   ((KrivCLos(x,Const(z))),(OPC EquFirst)::(Exp (Const y))::w) -> if y = z then krivineMachine (KRIV((KrivCLos(x,(Bool(true)))),w)) else krivineMachine (KRIV((KrivCLos(x,(Bool(false)))),w))

			|   ((KrivCLos(x,LetDef(q,z,y))),w) ->krivineMachine (KRIV((KrivCLos(x,z)),(OPC (DefFirst(y)))::Exp((Var q))::w))
			|   ((KrivCLos(x,a)),(OPC (DefFirst(y)))::Exp((Var q))::w) ->krivineMachine (KRIV((KrivCLos(TabK(q,KrivCLos(x,a))::x,y)),w))
			
			|   ((KrivCLos(x,Proj(z,y))),w) ->krivineMachine (KRIV((KrivCLos(x,y)),(OPC (ProjKriv(z)))::w))
			|   ((KrivCLos(x,Const(z))),(OPC (ProjKriv((Tup(y)))))::w) ->krivineMachine (KRIV((KrivCLos(x,(List.nth y z))),w))
			
			(* |   ((KrivCLos(x,Tup(z::zs))),w) ->krivineMachine (KRIV((KrivCLos(x,z)),(OPC TupKriv(zs))::(Exp (Const 0))::w)) *)
			(* |   ((KrivCLos(x,Const(q))),(OPC TupKriv(zs))::(Const z)::w) -> if z = (List.length zs)then krivineMachine (KRIV((KrivCLos(x,Tup(zs))),w)) else krivineMachine (KRIV((KrivCLos(x,List.nth zs z)),(OPC TupKriv(zs))::(Exp (Const (z+1)))::w)) *)

			(* |   ((KrivCLos(x,Const(q))),(OPC TupKriv(zs))::(Const z)::w) -> if z = (List.length zs)then krivineMachine (KRIV((KrivCLos(x,Tup(zs))),w)) else krivineMachine (KRIV((KrivCLos(x,List.nth zs z)),(OPC TupKriv(zs))::(Exp (Const (z+1)))::w)) *)

			|	((KrivCLos(x,Func(z,y))),w) -> krivineMachine (KRIV((KrivCLos(x,z)),(OP (KrivCLos(x,y)))::w))
			|   ((KrivCLos(x,Lambda(z,y))),(OP d)::w) -> krivineMachine (KRIV((KrivCLos(((TabK(z,d))::x),y)),w));;

			(* |   ((KrivCLos((TabK(z,d))::x,Var(z))),[]) -> krivineMachine KRIV(((KrivCLos((TabK(z,d)))::x,Var(z))),[])	 *)
			(* |   ((KrivCLos((TabK(q,KrivCLos(r,t)))::x,Var(z))),w) -> krivineMachine (KRIV(KrivCLos(r,t),(OPC LAZY)::(Exp(Var z))::(Exp(Var q))::(Ta x)::w))			 *)

let convertSecd tab com = (SECD(MySecd([],tab,com),[]));;
let convertKriv tab com = (KRIV(KrivCLos(tab,com),[]));;
(* Test Cases *)
let test1 = Plus(Const 3, Const 5);;
let executeKrivTest1 = krivineMachine (convertKriv [] test1);;
let compileTest1 = compile test1;;
let executeTest1 = secdMachine (convertSecd [] compileTest1);;

let test2 = Plus(Var (V "x"), Const 5);;
let executeKrivTest2 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 3))] test2);;
let compileTest2 = compile test2;;
let executeTest2 = secdMachine (convertSecd [Tab((V "x"),I 3)] compileTest2);;

let test3 = Implies(Bool true, Bool false);;
let compileTest3 = compile test3;;
let executeTest3 = secdMachine (convertSecd [] compileTest3);;
let executeKrivTest3 = krivineMachine (convertKriv [] test3);;

let test4 = Ite(test3, (Plus(Const 5, Const 5)), test2);;
let compileTest4 = compile test4;;
let executeTest4 = secdMachine (convertSecd [Tab((V "x"),I 3)] compileTest4);;
let executeKrivTest4 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 3))] test4);;

let test5 = Sub(Var (V "x"), Const 5);;
let compileTest5 = compile test5;;
let executeTest5 = secdMachine (convertSecd [Tab((V "x"),I 3)] compileTest5);;
let executeKrivTest5 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 3))] test5);;

let test6 = Lst(Var (V "x"), Const 5);;
let compileTest6 = compile test6;;
let executeTest6 = secdMachine (convertSecd [Tab((V "x"),I 3)] compileTest6);;
let executeKrivTest6 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 3))] test6);;

let test7 = Func(Lambda(V "x",Plus(Var(V "x"),Const(5))), Const 5);;
let compileTest7 = compile test7;;
let executeTest7 = secdMachine (convertSecd [] compileTest7);;
let executeKrivTest7 = krivineMachine (convertKriv [] test7);;

let test8 = Mul(Var (V "x"), Const 5);;
let executeKrivTest8 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 3))] test8);;
let compileTest8 = compile test8;;
let executeTest8 = secdMachine (convertSecd [Tab((V "x"),I 3)] compileTest8);;

let test9 = Not(Bool(true));;
let executeKrivTest9 = krivineMachine (convertKriv [] test9);;
let compileTest9 = compile test9;;
let executeTest9 = secdMachine (convertSecd [] compileTest9);;

let test10 = Div(Var (V "x"), Const 5);;
let executeKrivTest10 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 20))] test10);;
let compileTest10 = compile test10;;
let executeTest10 = secdMachine (convertSecd [Tab((V "x"),I 20)] compileTest10);;

let test11 = GrtEq(Var (V "x"), Const 5);;
let executeKrivTest11 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 5))] test11);;
let compileTest11 = compile test11;;
let executeTest11 = secdMachine (convertSecd [Tab((V "x"),I 5)] compileTest11);;

let test12 = Equ(Var (V "x"), Const 5);;
let executeKrivTest12 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 5))] test12);;
let compileTest12 = compile test12;;
let executeTest12 = secdMachine (convertSecd [Tab((V "x"),I 5)] compileTest12);;

let test13 = LstEq(Var (V "x"), Const 5);;
let executeKrivTest13 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 10))] test13);;
let compileTest13 = compile test13;;
let executeTest13 = secdMachine (convertSecd [Tab((V "x"),I 10)] compileTest13);;

let test14 = Proj(Tup[test11;test12;test13], Const 2);;
let executeKrivTest14 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 10))] test14);;
let compileTest14 = compile test14;;
let executeTest14 = secdMachine (convertSecd [Tab((V "x"),I 10)] compileTest14);;

let test15 = LetDef(V("x"),Const(5),test8);;
let compileTest15 = compile test15;;
let executeTest15 = secdMachine (convertSecd [Tab((V "x"),I 10)] compileTest15);;
let executeKrivTest15 = krivineMachine (convertKriv [TabK((V "x"),KrivCLos([], Const 10))] test15);;
