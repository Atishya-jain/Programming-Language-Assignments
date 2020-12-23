type myChar = A | X of char;;		(*Defined for first and last*)
type ediString = O | NIL | C of char | S of ediString*ediString;;		(*A\**)
type kstring = K of myChar*myChar*ediString*int;;		(*Single string type*)
exception Empty of kstring;;
exception AtLast of kstring;;
exception AtFirst of kstring;;
exception TooShort of kstring;;
exception Error of kstring;;	(*General error type*)

(*Input is kstring output is int*)	(*O(n)*)
let rec lgh x = match x with		
	    K(a,b,c,d) -> match c with O -> 0
				  	|   NIL -> 0
				  	|   C t -> 1 
				  	|   S(m,n) -> lgh(K(a,b,m,d)) + lgh(K(a,b,n,d));;
(*Input is kstring output is bool*)(*O(n)*)
let nonempty x = match lgh x with		
  		0 -> false
  	|	y -> true;;
(*Input is kstring output is mychar*)		(*O(1)*)  	
let rec first x = match x with		
		K(a,b,O,d) -> raise(Empty x)
	| 	K(a,b,NIL,d) -> raise(Empty x)
	| 	K(a,b,c,d) -> if a = A then raise(Empty x) else a;;
(*Input is kstring output is mychar*)	(*O(1)*)
(*This returns letter and not string*)
let rec last x = match x with			
		K(a,b,O,d) -> raise(Empty x)
	| 	K(a,b,NIL,d) -> raise(Empty x)
	| 	K(a,b,c,d) -> if b = A then raise(Empty x) else b;;					
let rec createString x = match (String.length x) with
		0 -> NIL
	|	y -> S(C(String.get x 0),createString(String.sub x 1 ((String.length x) -1)));;
(*Input is Ocaml string output is Kstring*)
let create x = if x = "" then K(A,A,S(O,NIL),0) else K(X(String.get x 0),X(String.get x ((String.length x) -1)), createString x,0);;

(*Input is kstring output is kstring with incremented string*)(*O(1)*)
let forward x = match x with		
	   K(m,n,S(a,S(z,y)),k) -> K(m,n,S(S(a,z),y),k+1)
	|	_ -> raise(AtLast x);;	
(*Input is kstring output is kstring*)(*O(1)*)
let back x = match x with		
	   K(m,n,S(S(b,c),a),k) -> K(m,n,S(b,S(c,a)),k-1)	
	|	_ -> raise(AtFirst x);;	
(*Input is kstring output is kstring*)(*O(n)*)
let rec moveTo n x = match x with		
			K(a,b,c,d) -> if n = d then x 
							else if n > d then try moveTo n (forward x) 
											with AtLast x -> raise(TooShort x)
							else try moveTo n (back x) 
											with AtFirst x -> raise(TooShort x);; 
(*Input is kstring and char output is Kstring replaced*)(*O(1)*)
let replace x w = match x with		
		K(a,b,c,d) -> match c with
			    C z -> K(a,b,C w,d)
			|   O -> raise(Empty x) 
			|   NIL -> raise(Empty x)
			|	S(m,n) -> if d = 0 then if (lgh x) = 0 then K(X w,X w,S(C w,n),d) else if d = ((lgh x)-1) then K(X w,X w,S(C w,n),d) else K(X w,b,S(C w,n),d) else match m with
								S(q,e) -> if d = ((lgh x)-1) then K(a,X w,S(S(q,C w),n),d) else K(a,b,S(S(q,C w),n),d)
							|	_ -> raise(Error x);; 
	
let concat (s1,s2) = if ((lgh s1) = 0) then (moveTo 0 s2) else if ((lgh s2) = 0) then (moveTo 0 s1) else match ((moveTo ((lgh s1)-1) s1),(moveTo 0 s2)) with
				(K(a,b,S(m,NIL),d),K(x,y,w,z)) -> (moveTo 0 (K(a,y,S(m,w),d)))
			|   (K(a,b,_,d),K(x,y,w,z)) -> raise(Error s1);;
(*Input is kstring*kstring and output is Kstring concatenated and marker at 0*)
(*O(n)*)
let rec myReverse x = match x with
  		S(S(m,n),c) -> myReverse (S(n,(myReverse (S(m,c)))))
  	|	S(C t1, c) -> S(C t1, c)
  	|	S(O, c) -> S(O, c)
  	|   S(NIL,c) -> S(NIL, c)  	
  	|	O -> O
  	|   NIL -> NIL
  	|   C t1 -> C t1;; 	
(*Input is kstring output is kstring*)
(*O(n)*)
let reverse x = if ((lgh x) = 0) then x else match (moveTo ((lgh x)-1) x) with
		K(a,b,c,d) -> K(b,a,((myReverse c)),0);;

(*
proof 1) -> (lgh(concat s1 s2) = lgh(s1) + lgh(s2))
	Here we basically perform concatenation as concat m n = S(m,n) which means that
	if lgh(S(m,n)) = lgh(m) + lgh(n) By def. of lgh. So lgh(concat s1 s2) = lgh(s1)+lgh(s2)
proof 2) -> lgh(reverse s) = lgh(s)
	case 1) - lgh(S(S(m,n),c)) = lgh(S(m,n)) + lgh(c) = lgh(m) + lgh(n) + lgh(c) = lgh(n) + lgh(S(m,c)) = lgh(S(n,S(m,c)))
	case 2) - All other cases returns the same value as before so no change in length
	Thus, we can say that in any of the case length of the string doesn't change so the final length of string after n steps is also same.
proof 3) -> lgh(replace w s) = lgh s
	Let the tree be of kind S(C t1,n) or S(S(m,n),p) whose length is x.
	We changed it to S(s w,n) or S(S(m,C w),n).
	We knew that lgh(S(C t1,n)) = lgh(C t1) + lgh(n) = 1 + lgh(n) = lgh(C w) + lgh(n) = lgh(S(C w,n))
	Similarly, lgh(S(S(m,C t1),p)) = lgh(m) + lgh(C t1) + lgh(p) = lgh(m) + lgh(C w) + lgh(p) = lgh(S(S(m,C w),p))

Signatures -
val lgh : kstring -> int = <fun>
val nonempty : kstring -> bool = <fun>
val first : kstring -> myChar = <fun>
val last : kstring -> myChar = <fun>
val createString : string -> ediString = <fun>
val create : string -> kstring = <fun>
val forward : kstring -> kstring = <fun>
val back : kstring -> kstring = <fun>
val moveTo : int -> kstring -> kstring = <fun>
val replace : kstring -> char -> kstring = <fun>
val concat : kstring * kstring -> kstring = <fun>
val myReverse : ediString -> ediString = <fun>
val reverse : kstring -> kstring = <fun>
*)