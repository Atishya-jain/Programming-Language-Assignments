type variable = Var of string
type term = V of variable | Node of string * (term list) | CUT | FAIL;;
type head = Head of term;;
type body = Body of term;;
type rule = Rule of head * (body list);;
type fact = Fact of head;; 
type clause = Clf of fact | Clr of rule;;
type goal = Goal of term;;
type program = Prog of clause;;

type table = Subs of (term*term) | CutDone;;
type executable = AST of goal list;;
type mybool = A of bool;;
type answer = B of mybool | C of (table list);;

exception NotPresent;;
exception Wrong_term;;
exception NON_UNIFIABLE;;

type main = program list;;


let rec failPresent li = match li with
			(FAIL)::(xs) -> true
		|   [] -> false
		|   (_::xs) -> failPresent xs;;


let rec cutPresent li = match li with
			(CUT)::(xs) -> true
		|   [] -> false
		|   (_::xs) -> cutPresent xs;;

let rec cutDonePresent li = match li with
			(C [CutDone])::(xs) -> true
		|   [] -> false
		|   (_::xs) -> cutDonePresent xs;;

let rec getTab li = match li with
			[] -> []
		|	[C x] -> x
		|   (C x) :: xs -> x @ (getTab xs);;

let rec varPresent li = match li with
			[] -> false	
		|	V(z)::xs -> true
		|	Node(a,b)::xs -> if (varPresent b) then true else (varPresent xs) (* ------------------------------------------------------------------------------------ *)
		|	CUT::xs -> varPresent xs
		|	FAIL::xs -> varPresent xs;;

let rec find_Var var li = match li with
			[] -> false	
		|	V(z)::xs -> if (var = V(z)) then true else find_Var var xs;;

let rec find_var_sig var li = match li with
			[] -> raise(Wrong_term)	
		|	Subs(V(z),b)::xs -> if (var = V(z)) then b else find_var_sig var xs
		|   CutDone::xs -> find_var_sig var xs;;

let rec vars1 l term = match term with
			V(z) -> if (List.mem (V(z)) l) then l else l@[V(z)]
		|   Node(x,y) -> List.fold_left vars1 l y;;
let vars term = vars1 [] term;;

let rec subst s term = match term with
			FAIL -> FAIL
		|	CUT -> CUT
		|   Node(q,[]) -> Node(q,[])
		|   Node(q,x) -> Node(q,(List.map (subst s) x))
		|	V(z) -> try find_var_sig (V(z)) s with Wrong_term -> V(z);; 

let rec composition1 l s1 s2 = match s1 with
			[] -> l@s2
		|   (Subs(a,b))::xs -> let v1 = (subst s2 b) in if (v1 = a) then composition1 l xs s2 else composition1 (l@[Subs(a,v1)]) xs s2
		|   (CutDone::xs) -> composition1 l xs s2;;
let composition s1 s2 = composition1 [] s1 s2;; 

(* MyMap applies updated subst to future terms and goes on like this *)
let rec myMap f e l1 l2 = match (l1,l2) with
			([],[]) -> e
		|   (x::xs,y::ys) -> myMap f (composition e (f [] (subst e x) (subst e y))) xs ys;;

let rec mgu1 l t1 t2 = match (t1,t2) with
		    (V(z), V(y)) -> if (z <> y) then l@[Subs(V(z),V(y))] else l
	    |   (Node(a,b), V(z)) -> if (b = []) then l@[Subs(V(z),Node(a,b))] 
								   else if ((find_Var (V(z)) (vars(Node(a,b)))) = false) then l@[Subs(V(z),Node(a,b))] 
								   		else raise (NON_UNIFIABLE)
	    |   (V(z), Node(a,b)) -> if (b = []) then l@[Subs(V(z),Node(a,b))]
								   else if ((find_Var (V(z)) (vars(Node(a,b)))) = false) then l@[Subs(V(z),Node(a,b))] 
								   		else raise (NON_UNIFIABLE)	     
		|   (Node(a,b), Node(c,d)) -> if (b = []) then 
										if (d = []) then 
										  if (a = c) then l else raise (NON_UNIFIABLE)
										else raise(NON_UNIFIABLE)
									  else if (d = []) then raise(NON_UNIFIABLE) 
									  else if (a = c) then myMap mgu1 l b d else raise(NON_UNIFIABLE)
		|   (CUT, _) -> raise(NON_UNIFIABLE)
		|   (_, CUT) -> raise(NON_UNIFIABLE)
		|   (FAIL, _) -> raise(NON_UNIFIABLE)
		|   (_, FAIL) -> raise(NON_UNIFIABLE);;
let mgu t1 t2 = mgu1 [] t1 t2;;

let rec bodyOut (Body(z)) = z;;
let rec goalOut (Goal(z)) = z;;
let rec aout (A(z)) = z;;

let rec executeBody origProg tab prog sym = match (prog,sym) with
			([],Node(d,f)::xs) -> A false
		|   ((Prog(Clf(Fact(Head(x)))) :: xs), [CUT]) -> A true
		|   ((Prog(Clf(Fact(Head(x)))) :: xs), CUT::ys)	-> executeBody origProg tab prog ys	
		
		|   ((Prog(Clr(Rule(Head(x),y))) :: xs), [CUT]) -> A true
		|   ((Prog(Clr(Rule(Head(x),y))) :: xs), CUT::ys) -> executeBody origProg tab prog ys
		
		|   ((Prog(Clf(Fact(Head(x)))) :: xs), [y]) ->   (try 
															let newTab = mgu x y in 
															A true
							    						 with 
														 	NON_UNIFIABLE -> executeBody origProg tab xs sym)
		|   ((Prog(Clf(Fact(Head(x)))) :: xs), y::ys) -> (try 
															let newTab = mgu x y in 
															let newBody = (List.map (subst newTab) ys) in	 
																if (cutPresent ys) then 
																	(executeBody origProg newTab origProg newBody)
																else if (aout (executeBody origProg newTab origProg newBody)) then A true else (executeBody origProg newTab xs (y::ys))
							    						 with 
														 	NON_UNIFIABLE -> executeBody origProg tab xs sym)
		|   ((Prog(Clr(Rule(Head(x),z))) :: xs), [y]) ->    (try 
																let newTab = mgu x y in 
																let newBody = List.map (subst newTab) (List.map bodyOut z) in	 
																	executeBody origProg newTab origProg newBody
															with 
														 		NON_UNIFIABLE -> executeBody origProg tab xs sym)
		|   ((Prog(Clr(Rule(Head(x),z))) :: xs), y::ys) ->   (try 
																let newTab = mgu x y in 
																let newBody = (List.map (subst newTab) (List.map bodyOut z)) in	 
																let myNewBody = (List.map (subst newTab) ys) in
																
																if (aout (executeBody origProg newTab origProg newBody)) then 
																	if(cutPresent ys) then
																		(executeBody origProg tab origProg myNewBody)
																	else			
																		if (aout (executeBody origProg tab origProg myNewBody)) then
																			A true
																		else
																			(executeBody origProg newTab xs (y::ys))		
																else 		
															 		(executeBody origProg newTab xs (y::ys))
							    							 with 
															 	NON_UNIFIABLE -> executeBody origProg tab xs sym);;
 
let rec execute origProg tab prog sym = match (prog, sym) with
			([],Node(d,f)) -> B (A false)
		|	((Prog(Clf(Fact(Head(x)))) :: xs), y) -> (try 
														let newTab = mgu x y in 
														B (A true)
						    						 with 
													 	NON_UNIFIABLE -> execute origProg tab xs sym)
		|	((Prog(Clr(Rule(Head(x),y))) :: xs), z) -> 	 (try 
															let newTab = mgu x z in 
															let newBody = List.map (subst newTab) (List.map bodyOut y) in	 
																if (failPresent newBody) then 
																	execute origProg tab xs sym 
																else 
																	if (aout (executeBody origProg newTab origProg newBody)) then B (A true) else execute origProg tab xs sym 
							    						 with 
														 	NON_UNIFIABLE -> execute origProg tab xs sym);;

let rec executeBodyVar origProg tab prog sym = match (prog,sym) with
		    ((Prog(Clf(Fact(Head(x)))) :: xs), [CUT]) -> [C [CutDone]]@[(C (tab))]
		|   ((Prog(Clf(Fact(Head(x)))) :: xs), CUT::ys)	-> [C [CutDone]]@(executeBodyVar origProg tab prog ys)	

		|   ((Prog(Clr(Rule(Head(x),y))) :: xs), [CUT]) -> [C [CutDone]]@[(C (tab))]
		|   ((Prog(Clr(Rule(Head(x),y))) :: xs), CUT::ys) -> [C [CutDone]]@(executeBodyVar origProg tab prog ys)

		|   ([Prog(Clf(Fact(Head(x))))], [y]) -> (try 
													let newTab = mgu x y in 
													[C (tab@newTab)]
					    						 with 
												 	NON_UNIFIABLE -> [])
		|   ((Prog(Clf(Fact(Head(x)))) :: xs), [y]) ->   (try 
															let newTab = mgu x y in 
															[C(tab@newTab)]@(executeBodyVar origProg tab xs sym)
							    						 with 
														 	NON_UNIFIABLE -> executeBodyVar origProg tab xs sym)

		|   ([Prog(Clf(Fact(Head(x))))], y::ys) ->  (try 
														let newTab = mgu x y in 
														let newBody = (List.map (subst newTab) ys) in	 
															(executeBodyVar origProg (tab@newTab) origProg newBody)
						    						 with 
													 	NON_UNIFIABLE -> [])
		|   ((Prog(Clf(Fact(Head(x)))) :: xs), y::ys) -> (try 
															let newTab = mgu x y in 
															let newBody = (List.map (subst newTab) ys) in	 
															let v = (executeBodyVar origProg (tab@newTab) origProg newBody) in
																if (cutDonePresent v) then v else v@(executeBodyVar origProg tab xs (y::ys))
							    						 with 
														 	NON_UNIFIABLE -> executeBodyVar origProg tab xs sym)

		|   ([Prog(Clr(Rule(Head(x),z)))], [y]) ->  (try 
														let newTab = mgu x y in 
														let newBody = List.map (subst newTab) (List.map bodyOut z) in	 
															executeBodyVar origProg (tab@newTab) origProg newBody
													with 
												 		NON_UNIFIABLE -> [])
		|   ((Prog(Clr(Rule(Head(x),z))) :: xs), [y]) ->    (try 
																let newTab = mgu x y in 
																let newBody = List.map (subst newTab) (List.map bodyOut z) in	 
																	(executeBodyVar origProg (tab@newTab) origProg newBody) @ (executeBodyVar origProg tab xs sym)
															with 
														 		NON_UNIFIABLE -> executeBodyVar origProg tab xs sym)

		|   ([Prog(Clr(Rule(Head(x),z)))], y::ys) -> (try 
														let newTab = mgu x y in 
														let newBody = (List.map (subst newTab) (List.map bodyOut z)) in	 
														let myNewBody = (List.map (subst newTab) ys) in
														let myNewTabel = getTab (executeBodyVar origProg (tab@newTab) origProg newBody) in
														(executeBodyVar origProg (myNewTabel) origProg myNewBody)
					    							 with 
													 	NON_UNIFIABLE -> [])
		|   ((Prog(Clr(Rule(Head(x),z))) :: xs), y::ys) ->   (try 
																let newTab = mgu x y in 
																let newBody = (List.map (subst newTab) (List.map bodyOut z)) in	 
																let myNewTabel = getTab (executeBodyVar origProg (tab@newTab) origProg newBody) in
																let myNewBody = (List.map (subst (newTab@myNewTabel)) ys) in
																let v = (executeBodyVar origProg myNewTabel origProg myNewBody) in
																	if (cutDonePresent v) then v else v@(executeBodyVar origProg tab xs (y::ys))

																	(* if (cutPresent ys) then (executeBodyVar origProg myNewTabel origProg myNewBody) else (executeBodyVar origProg myNewTabel origProg myNewBody) @ (executeBodyVar origProg tab xs (y::ys)) *)
							    							 with 
															 	NON_UNIFIABLE -> executeBodyVar origProg tab xs sym);;

let rec executeVar origProg tab prog sym = match (prog, sym) with 
			([Prog(Clf(Fact(Head(x))))], y) ->  (try
													let newTab = mgu x y in
													[C newTab]
												with
													NON_UNIFIABLE -> [])
		|	((Prog(Clf(Fact(Head(x)))) :: xs), y) -> (try
														let newTab = mgu x y in
														(C newTab)::(executeVar origProg tab xs sym)
													with
														NON_UNIFIABLE -> executeVar origProg tab xs sym)			
		|	([Prog(Clr(Rule(Head(x),y)))], z) -> (try 
													let newTab = mgu x z in 
													let newBody = List.map (subst newTab) (List.map bodyOut y) in	 
														if ((failPresent newBody) = false) then (executeBodyVar origProg newTab origProg newBody) else []  
					    						 with 
												 	NON_UNIFIABLE -> [])
		|	((Prog(Clr(Rule(Head(x),y))) :: xs), z) -> 	 (try 
															let newTab = mgu x z in 
															let newBody = List.map (subst newTab) (List.map bodyOut y) in	 
																if ((failPresent newBody) = false) then (executeBodyVar origProg newTab origProg newBody)@(executeVar origProg tab xs sym) 
																else (executeVar origProg tab xs sym)
							    						 with 
														 	NON_UNIFIABLE -> executeVar origProg tab xs sym);;
let rec find_Var_list var l = match l with
			[] -> false
		|	Node(a,b)::xs -> if (find_Var_list var b) then true else find_Var_list var xs
		|	V(a)::xs -> if (V(a) = var) then true else find_Var_list var xs
		|   CUT::xs -> find_Var_list var xs
		|   FAIL::xs -> find_Var_list var xs;;

let rec filterC tab l = match l with
		[] -> []
	|	(Subs(V(a),V(b))::xs) -> if ((find_Var_list (V(a)) tab) && (find_Var_list (V(b)) tab)) then (Subs(V(a),V(b))::(filterC tab xs)) else filterC tab xs
	|   (Subs(V(c),Node(a,b))::xs) -> if (find_Var_list (V(c)) tab) then  (Subs(V(c),Node(a,b))::(filterC tab xs)) else (filterC tab xs)
	|   (Subs(Node(a,b), V(c))::xs) -> if  (find_Var_list (V(c)) tab) then  (Subs(V(c),Node(a,b))::(filterC tab xs)) else (filterC tab xs)
	|   (Subs(Node(a,b), Node(c,d))::xs) -> (Subs(Node(a,b),Node(c,d))::(filterC tab xs))
	|   (CutDone::xs) -> filterC tab xs;;

let rec filter tab l = match l with
			[(C [CutDone])::xs] -> (filter tab [xs])
		|	[(C x)::xs] -> [C(filterC tab x)] :: (filter tab [xs])
		|   _ -> [];;

(* let rec calculate tab prog e = match e with 
			AST([Goal(Node(a,x))]) -> if (varPresent x) then filter x [(executeVar prog tab prog (Node(a,x)))] else [[(execute prog tab prog (Node(a,x)))]]
		|   AST(((Goal(Node(a,x)))::xs)) -> if (varPresent x) then filter x ((executeVar prog tab prog (Node(a,x))) :: (calculate tab prog (AST(xs)))) 
														else [execute prog tab prog (Node(a,x))] :: (calculate tab prog (AST(xs)));;
 *)
(* 
let rec recurSubsOnGoalsVar tab gl = match (tab,gl) with
			([],[x]) -> calculate (AST([x]))
		|   ([C x]::xs, Goal(y)::ys) -> let calc = calculate (AST([Goal(subst x y)])) in
											if (calc = [[B true]]) then recurSubsOnGoalsVar tab ys
											else if (calc = [[B false]]) then [[B false]]
											else if (calc = [[C q]::zs]) then 
												recurSubsOnGoalsVar ()
												let justSub = subst x y in 
													if (varPresentDeep justSub) then 
													else if ((calculate (AST([Goal(justSub)]))) = [[B true]]) then recurSubsOnGoalsVar tab ys
														 else [[B false]] 
 *)

let rec calculate tab prog e = match e with 
			AST([Goal(FAIL)]) -> [[B (A false)]]
		|	AST([Goal(CUT)]) -> [[B (A true)]]
		|	AST([Goal(Node(a,x))]) -> if (varPresent x) then filter x [(executeVar prog tab prog (Node(a,x)))] else [[(execute prog tab prog (Node(a,x)))]]
		|   AST(((Goal(Node(a,x)))::xs)) -> if (varPresent x) then filter (List.map goalOut ((Goal(Node(a,x)))::xs)) [(executeBodyVar prog tab prog (List.map goalOut ((Goal(Node(a,x)))::xs)))]
											else if ((calculate tab prog (AST([Goal(Node(a,x))]))) = [[B(A true)]]) then calculate tab prog (AST(xs))
											else [[B (A false)]]
		|   AST(((Goal(CUT))::xs))	-> calculate tab prog (AST(xs))
		|   AST(((Goal(FAIL))::xs))	-> [[B (A false)]];; 


(* 
											recurSubsOnGoalsVar (filter x (executeVar prog tab prog (Node(a,x)))) xs
											else if (execute prog tab prog (Node(a,x))) then (calculate tab prog (AST(xs)))
												 else [[B false]];; *)

(* let fact11 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("2",[])]))));;
let fact12 = Clf(Fact(Head(Node("edge",[Node("2",[]);Node("3",[])]))));;
let fact13 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("3",[])]))));;
let fact14 = Clf(Fact(Head(Node("path",[V(Var("x"));V(Var("x"))]))));;
let rule11 = Clr(Rule(Head(Node("path",[V(Var("x"));V(Var("y"))])), [Body(Node("edge",[V(Var("x"));V(Var("z"))]));Body(Node("path",[V(Var("z"));V(Var("y"))]))]));;

let prog1 = [Prog(fact11);Prog(fact12);Prog(fact13); Prog(fact14);Prog(rule11)];;
let goal11 = [Goal(Node("edge",[Node("1",[]);Node("2",[])]))];;
let goal12 = [Goal(Node("path",[Node("1",[]);Node("3",[])]))];;
let goal13 = [Goal(Node("edge",[Node("1",[]);V(Var("x"))]))];;
let goal14 = [Goal(Node("path",[V(Var("q"));V(Var("m"))]))];;
let result11 = calculate [] prog1 (AST(goal11));;
let result12 = calculate [] prog1 (AST(goal12));;
let result13 = calculate [] prog1 (AST(goal13));;
let result14 = calculate [] prog1 (AST(goal14));;

let fact21 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("2",[])]))));;
let fact22 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("3",[])]))));;
let fact23 = Clf(Fact(Head(Node("edge",[Node("2",[]);Node("4",[])]))));;
let fact24 = Clf(Fact(Head(Node("path",[V(Var("x"));V(Var("x"))]))));;
let rule21 = Clr(Rule(Head(Node("path",[V(Var("x"));V(Var("y"))])), [Body(Node("edge",[V(Var("x"));V(Var("z"))]));Body(Node("path",[V(Var("z"));V(Var("y"))]))]));;

let prog2 = [Prog(fact21);Prog(fact22);Prog(fact23); Prog(fact24);Prog(rule21)];;
let goal21 = [Goal(Node("edge",[Node("1",[]);Node("2",[])]))];;
let goal22 = [Goal(Node("path",[Node("1",[]);Node("4",[])]))];;
let goal23 = [Goal(Node("path",[V(Var("q"));Node("4",[])]))];;
let goal24 = [Goal(Node("path",[V(Var("q"));V(Var("m"))]))];;
let result21 = calculate [] prog2 (AST(goal21));;
let result22 = calculate [] prog2 (AST(goal22));;
let result23 = calculate [] prog2 (AST(goal23));;
let result24 = calculate [] prog2 (AST(goal24));;

let fact31 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("2",[])]))));;
let fact32 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("3",[])]))));;
let fact33 = Clf(Fact(Head(Node("edge",[Node("3",[]);Node("4",[])]))));;
let fact34 = Clf(Fact(Head(Node("edge",[Node("3",[]);Node("5",[])]))));;
let fact35 = Clf(Fact(Head(Node("edge",[Node("4",[]);Node("6",[])]))));;
let fact36 = Clf(Fact(Head(Node("edge",[Node("4",[]);Node("7",[])]))));;
let fact37 = Clf(Fact(Head(Node("path",[V(Var("x"));V(Var("x"))]))));;
let rule31 = Clr(Rule(Head(Node("path",[V(Var("x"));V(Var("y"))])), [Body(Node("edge",[V(Var("x"));V(Var("z"))]));Body(Node("path",[V(Var("z"));V(Var("y"))]))]));;

let prog3 = [Prog(fact31);Prog(fact32);Prog(fact33); Prog(fact34); Prog(fact35); Prog(fact36); Prog(fact37); Prog(rule21)];;
let goal31 = [Goal(Node("edge",[Node("1",[]);Node("4",[])]))];;
let goal32 = [Goal(Node("path",[Node("1",[]);Node("7",[])]))];;
let goal33 = [Goal(Node("path",[Node("1",[]);Node("5",[])]))];;
let goal34 = [Goal(Node("path",[V(Var("q"));Node("7",[])]))];;
let goal35 = [Goal(Node("path",[V(Var("q"));V(Var("m"))]))];;
let result31 = calculate [] prog3 (AST(goal31));;
let result32 = calculate [] prog3 (AST(goal32));;
let result33 = calculate [] prog3 (AST(goal33));;
let result34 = calculate [] prog3 (AST(goal34));;
let result35 = calculate [] prog3 (AST(goal35));;

let fact41 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("2",[])]))));;
let fact42 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("3",[])]))));;
let fact43 = Clf(Fact(Head(Node("edge",[Node("2",[]);Node("4",[])]))));;
let fact44 = Clf(Fact(Head(Node("path",[V(Var("x"));V(Var("x"))]))));;
let rule41 = Clr(Rule(Head(Node("path",[V(Var("x"));V(Var("y"))])), [Body(Node("edge",[V(Var("x"));V(Var("z"))])); Body(Node("path",[V(Var("z"));V(Var("y"))]))]));;

let prog4 = [Prog(fact41);Prog(fact42);Prog(fact43); Prog(fact44);Prog(rule41)];;
let goal41 = [Goal(Node("edge",[Node("1",[]);Node("2",[])]))];;
let goal42 = [Goal(Node("path",[Node("1",[]);Node("4",[])]))];;
let goal43 = [Goal(Node("path",[V(Var("q"));Node("4",[])]))];;
let goal44 = [Goal(Node("path",[V(Var("q"));V(Var("m"))]))];;
let result41 = calculate [] prog4 (AST(goal41));;
let result42 = calculate [] prog4 (AST(goal42));;
let result43 = calculate [] prog4 (AST(goal43));;
let result44 = calculate [] prog4 (AST(goal44));;


let fact51 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("2",[])]))));;
let fact52 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("3",[])]))));;
let fact53 = Clf(Fact(Head(Node("edge",[Node("2",[]);Node("4",[])]))));;
let fact54 = Clf(Fact(Head(Node("path",[V(Var("x"));V(Var("x"))]))));;
let rule51 = Clr(Rule(Head(Node("path",[V(Var("x"));V(Var("y"))])), [Body(Node("edge",[V(Var("x"));V(Var("z"))])); Body(CUT); Body(Node("path",[V(Var("z"));V(Var("y"))]))]));;

let prog5 = [Prog(fact51);Prog(fact52);Prog(fact53); Prog(fact54);Prog(rule51)];;
let goal51 = [Goal(Node("edge",[Node("1",[]);Node("2",[])]))];;
let goal52 = [Goal(Node("path",[Node("1",[]);Node("4",[])]))];;
let goal53 = [Goal(Node("path",[V(Var("q"));Node("5",[])]))];;
let goal54 = [Goal(Node("path",[V(Var("q"));V(Var("m"))]))];;
let result51 = calculate [] prog5 (AST(goal51));;
let result52 = calculate [] prog5 (AST(goal52));;
let result53 = calculate [] prog5 (AST(goal53));;
let result54 = calculate [] prog5 (AST(goal54));;

(* mgu (Node("1",[Node("4",[]); V(Var("m"))])) (Node("1",[V(Var("x")); V(Var("x"))]));; *)

let fact61 = Clf(Fact(Head(Node("g",[Node("1",[])]))));;
let fact62 = Clf(Fact(Head(Node("g",[Node("2",[])]))));;
let rule61 = Clr(Rule(Head(Node("f",[V(Var("x"))])), [Body(Node("g",[V(Var("x"))])); Body(CUT)]));;

let prog6 = [Prog(rule61);Prog(fact61);Prog(fact62)];;
let goal61 = [Goal(Node("f",[Node("2",[])]))];;
let goal62 = [Goal(Node("f",[V(Var("q"))]))];;
let result61 = calculate [] prog6 (AST(goal61));;
let result62 = calculate [] prog6 (AST(goal62));;


let fact71 = Clf(Fact(Head(Node("g",[Node("1",[])]))));;
let fact72 = Clf(Fact(Head(Node("g",[Node("2",[])]))));;
let rule71 = Clr(Rule(Head(Node("f",[V(Var("x"))])), [Body(Node("g",[V(Var("x"))])); Body(FAIL)]));;

let prog7 = [Prog(rule71);Prog(fact71);Prog(fact72)];;
let goal71 = [Goal(Node("f",[Node("2",[])]))];;
let goal72 = [Goal(Node("f",[V(Var("q"))]))];;
let goal73 = [Goal(Node("g",[V(Var("q"))]))];;
let goal74 = [Goal(Node("g",[Node("32",[])]))];;
let result71 = calculate [] prog7 (AST(goal71));;
let result72 = calculate [] prog7 (AST(goal72));;
let result73 = calculate [] prog7 (AST(goal73));;
let result74 = calculate [] prog7 (AST(goal74));;


let fact81 = Clf(Fact(Head(Node("g",[Node("1",[])]))));;
let fact82 = Clf(Fact(Head(Node("g",[Node("2",[])]))));;
let rule81 = Clr(Rule(Head(Node("f",[V(Var("x"))])), [Body(Node("g",[V(Var("x"))])); Body(CUT)]));;

let prog8 = [Prog(rule81);Prog(fact81);Prog(fact82)];;
let goal81 = [Goal(Node("f",[V(Var("q"))])); Goal(Node("g",[V(Var("q"))]))];;
let goal82 = [Goal(Node("g",[V(Var("q"))])); Goal(Node("f",[V(Var("q"))])); Goal(CUT)];;
let result81 = calculate [] prog8 (AST(goal81));;
let result82 = calculate [] prog8 (AST(goal82));;


let fact91 = Clf(Fact(Head(Node("teaches",[Node("drFred",[]);Node("History",[])]))));;
let fact92 = Clf(Fact(Head(Node("teaches",[Node("drFred",[]);Node("English",[])]))));;
let fact93 = Clf(Fact(Head(Node("teaches",[Node("drFred",[]);Node("Drama",[])]))));;
let fact94 = Clf(Fact(Head(Node("teaches",[Node("drFiona",[]);Node("Physics",[])]))));;
let fact95 = Clf(Fact(Head(Node("studies",[Node("alice",[]);Node("English",[])]))));;
let fact96 = Clf(Fact(Head(Node("studies",[Node("angus",[]);Node("English",[])]))));;
let fact97 = Clf(Fact(Head(Node("studies",[Node("amelia",[]);Node("Drama",[])]))));;
let fact98 = Clf(Fact(Head(Node("studies",[Node("alex",[]);Node("Physics",[])]))));;

let prog9 = [Prog(fact91);Prog(fact92);Prog(fact93);Prog(fact94);Prog(fact95);Prog(fact96);Prog(fact97);Prog(fact98)];;
let goal91 = [Goal(Node("teaches",[Node("drFred",[]); V(Var("Course"))])); Goal(Node("studies",[V(Var("Student"));V(Var("Course"))]))];;
let goal92 = [Goal(Node("teaches",[Node("drFred",[]); V(Var("Course"))])); Goal(CUT); Goal(Node("studies",[V(Var("Student"));V(Var("Course"))]))];;
let goal93 = [Goal(Node("teaches",[Node("drFred",[]); V(Var("Course"))])); Goal(Node("studies",[V(Var("Student"));V(Var("Course"))])); Goal(CUT)];;
let goal94 = [Goal(CUT); Goal(Node("teaches",[Node("drFred",[]); V(Var("Course"))])); Goal(Node("studies",[V(Var("Student"));V(Var("Course"))]))];;
let goal95 = [Goal(Node("teaches",[Node("drFred",[]); Node("English",[])])); Goal(Node("studies",[Node("alice",[]);Node("English",[])])); Goal(CUT)];;
let result91 = calculate [] prog9 (AST(goal91));;
let result92 = calculate [] prog9 (AST(goal92));;
let result93 = calculate [] prog9 (AST(goal93));;
let result94 = calculate [] prog9 (AST(goal94));;
let result95 = calculate [] prog9 (AST(goal95));;


let fact101 = Clf(Fact(Head(Node("edge",[Node("a",[]);Node("b",[])]))));;
let fact102 = Clf(Fact(Head(Node("edge",[Node("a",[]);Node("c",[])]))));;
let fact104 = Clf(Fact(Head(Node("edge",[Node("b",[]);Node("d",[])]))));;
let fact105 = Clf(Fact(Head(Node("edge",[Node("b",[]);Node("e",[])]))));;
let fact106 = Clf(Fact(Head(Node("edge",[Node("c",[]);Node("e",[])]))));;
let fact107 = Clf(Fact(Head(Node("edge",[Node("c",[]);Node("f",[])]))));;
let fact108 = Clf(Fact(Head(Node("edge",[Node("e",[]);Node("g",[])]))));;
let fact109 = Clf(Fact(Head(Node("edge",[Node("f",[]);Node("h",[])]))));;
let fact1010 = Clf(Fact(Head(Node("edge",[Node("i",[]);Node("c",[])]))));;
let fact1011 = Clf(Fact(Head(Node("path",[V(Var("x"));V(Var("x"))]))));;
let rule101 = Clr(Rule(Head(Node("path",[V(Var("x"));V(Var("y"))])), [Body(Node("path",[V(Var("x"));V(Var("z"))])); Body(Node("edge",[V(Var("z"));V(Var("y"))]))]));;

let prog10 = [Prog(fact101);Prog(fact102); Prog(fact104) ; Prog(fact105) ; Prog(fact106); Prog(fact107); Prog(fact108); Prog(fact109); Prog(fact1010); Prog(fact1011);Prog(rule101)];;
let goal101 = [Goal(Node("path",[Node("a",[]);Node("a",[])]))];;
let goal102 = [Goal(Node("path",[Node("a",[]);Node("b",[])]))];;
let goal103 = [Goal(Node("path",[Node("a",[]);Node("e",[])]))];;
(* let goal104 = [Goal(Node("path",[V(Var("a"));V(Var("e"))]))];; *)
let result101 = calculate [] prog10 (AST(goal101));;
let result102 = calculate [] prog10 (AST(goal102));;
let result103 = calculate [] prog10 (AST(goal103));;
(* let result104 = calculate [] prog10 (AST(goal104));; *)

let rule111 = Clr(Rule(Head(Node("h",[Node("a",[])])), [Body(Node("a",[Node("b",[])])); Body(Node("c",[Node("d",[])]))]));;
let fact111 = Clf(Fact(Head(Node("h",[Node("b",[])]))));;
let rule112 = Clr(Rule(Head(Node("a",[Node("b",[])])), [Body(CUT)]));;
let fact112 = Clf(Fact(Head(Node("c",[Node("d",[])]))));;

let prog11 = [Prog(rule111);Prog(fact111); Prog(rule112); Prog(fact112)];;
let goal111 = [Goal(Node("h",[V(Var("q"))]))];;
let result111 = calculate [] prog11 (AST(goal111));;

let fact121 = Clf(Fact(Head(Node("id",[V(Var("x"));V(Var("x"))]))));;
let prog12 = [Prog(fact121)];;
let goal121 = [Goal(Node("id",[V(Var("y"));V(Var("y"))]))];;
let result121 = calculate [] prog12 (AST(goal121));;


let fact131 = Clf(Fact(Head(Node("edge",[Node("1",[]);Node("2",[])]))));;
let fact132 = Clf(Fact(Head(Node("edge",[Node("2",[]);Node("3",[])]))));;
let fact133 = Clf(Fact(Head(Node("edge",[Node("3",[]);Node("4",[])]))));;
let fact134 = Clf(Fact(Head(Node("edge",[Node("3",[]);Node("5",[])]))));;
let fact135 = Clf(Fact(Head(Node("path",[V(Var("x"));V(Var("x"))]))));;
let rule131 = Clr(Rule(Head(Node("path",[V(Var("x"));V(Var("y"))])), [Body(Node("edge",[V(Var("x"));V(Var("z"))]));Body(Node("path",[V(Var("z"));V(Var("y"))])); Body(CUT)]));;

let prog13 = [Prog(fact131); Prog(fact132); Prog(fact133); Prog(fact134); Prog(fact135); Prog(rule131)];;
let goal131 = [Goal(Node("edge",[Node("1",[]);Node("2",[])]))];;
let goal132 = [Goal(Node("path",[Node("1",[]);Node("3",[])]))];;
let goal133 = [Goal(Node("path",[Node("1",[]);V(Var("q"))]))];;
let goal134 = [Goal(Node("path",[V(Var("q"));V(Var("m"))]))];;
let result131 = calculate [] prog13 (AST(goal131));;
let result132 = calculate [] prog13 (AST(goal132));;
let result133 = calculate [] prog13 (AST(goal133));;
let result134 = calculate [] prog13 (AST(goal134));;

(* 
composition [Subs(V(Var("x")), V(Var("y")))] [Subs(V(Var("y")), Node("1",[]))];;
subst [Subs(V(Var("x")), V(Var("y")));Subs(V(Var("y")), Node("1",[]))] (V(Var("y")));;
subst [Subs(V(Var("x")), V(Var("y")));Subs(V(Var("y")), Node("1",[]))] (V(Var("x")));; *) *)