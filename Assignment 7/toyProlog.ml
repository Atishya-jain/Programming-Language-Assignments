open MyParser;;
open MyOcaml;;
open Printf;;


let rec convertPrint lis = match lis with
		[] -> ""
	|	[Subs(V(Var(x)), V(Var(y)))] -> String.concat "=" [x;y]
	|	[Subs(V(Var(x)), Node(y,b))] -> String.concat "=" [x;y]
	|	(Subs(V(Var(x)), Node(y,b))) :: xs -> String.concat "," [(String.concat "=" [x;y]);"\n";(convertPrint xs)] 
	|	(Subs(V(Var(x)), V(Var(y)))) :: xs -> String.concat "," [(String.concat "=" [x;y]);"\n";(convertPrint xs)]
;;

let rec printInStyle lis = match lis with
		[] -> Printf.printf "\nDone\n"
	|	(C x)::xs -> let p = print_string (convertPrint x) in
						let () = flush stdout in
							let cin = stdin in 
								try
									let inp = Printexc.print input_line cin in
										if (inp = ";") then
											Printexc.print printInStyle xs
										else
											Printf.printf "Aborting print\n"
								with
									_ -> Printf.printf "You entered some wrong character\n"
;;


let rec filter2 l = match l with
		[] -> []	
	|	[l1]::ls -> l1 :: (filter2 ls);;

let rec print x = match x with
		[] -> ()
	|  [l1]::ls -> printInStyle (filter2 x);;
						
let rec inputQuery prog input=
	if prog = [] then
		Printf.printf ("File Not parsed. Please input file again\n")
	else	
		let lexbuf = Lexing.from_string input in 
			(* Printf.printf ("chk1\n"); *)
		let goals = MyParser.goal MyLex.token lexbuf in
			(* Printf.printf ("chk2\n"); *)
		let finalOut = (calculate [] prog goals) in
			(* Printf.printf ("chk3\n"); *)
			match finalOut with
				[[B (A x)]] -> Printf.printf "%B\n" (x)
			|   _ -> print finalOut
;;
let rec inputProg file= 
	let ic = open_in file in
    let lexbuf = Lexing.from_channel ic in 
    let prog = MyParser.main MyLex.token lexbuf in
    prog
;;


let rec main prog = 
	Printf.printf "?-";
	let input = try read_line() with End_of_file -> Printf.printf "\nExiting\n" ;exit 0 in
	let () = flush stdout in
		let length = String.length input in
			if (length = 0) then
				let () = Printf.printf("Please provide a valid goal.\n") in
					main prog
			else		
				if (String.get input (length-1) <> '.') then
					let () = Printf.printf(". is missing at the end of your clause\n") in
						main prog
				else if (length = 1) then
					let () = Printf.printf("Please provide a valid goal.\n") in
						main prog
				else
					if ((String.sub input 0 2 = "[\"") && (String.sub input (length-3) 2 = "\"]")) then 
						(try 
							(* let newProg = Printexc.print inputProg (String.sub input 2 (length - 5)) in 	 *)
							let newProg = inputProg (String.sub input 2 (length - 5)) in 	
								let () = Printf.printf("Program loaded.\n") in
									main newProg
						with
							Parsing.Parse_error -> let () = Printf.printf("Parse Error in file given.\n") in main prog
						|	_ -> let () = Printf.printf("Error in file given.\n") in main prog) 			
					else
						(try
							let () = inputQuery prog input in
								main prog
						with
							Parsing.Parse_error -> let () = Printf.printf("Error in input given.\n") in main prog);;

if !Sys.interactive then () else main [];;   