type peano = Z | S of peano;; (* типы необходимо копировать в реализацию *)
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

let rec peano_of_int x = match x with
	0 -> Z
  |	x -> S (peano_of_int (x - 1));;

let rec int_of_peano p = match p with
    Z -> 0
  | S x -> 1 + int_of_peano x;;

let inc x = S x;;

let rec add x y = match y with
	Z -> x
  | S yy -> inc (add x yy);;
  
let dec x = match x with
    Z -> Z
  | S xx -> xx;;
  
let rec sub x y = match y with 
	Z -> x
  | S yy -> dec (sub x yy);;

let rec mul x y = match y with 
	Z -> Z
  |	S yy -> add (mul x yy) x;;

let rec power x y = match y with
	Z -> S Z
  |	S yy -> mul (power x yy) x;;
                     
(*-----  LIST  -----*)

let rec append x y = match x with
	[] -> y;
  |	head :: tail -> head :: (append tail y);;
                     
let rec rev x = match x with
	[] -> []
  |	head :: tail -> append (rev tail) (head :: []);;
  
let rec size x = match x with
	[] -> 0
  |	head :: tail -> 1 + (size tail);;
  
let rec take_N n x = 
	if n = 0 then [] else
	match x with
		[] -> []
	  |	head :: tail -> head :: take_N (n - 1) tail;;
	
let rec remove_N n x = 
	if n = 0 then x else
	match x with
		[] -> []
	  | head :: tail -> remove_N (n - 1) tail;;
			
let rec merge_sort x = match x with
	[] -> []
  | [xx] -> [xx]
  | _ ->
		let left = take_N ((size x) / 2) x in
		let right = remove_N ((size x) / 2) x in
		let rec merge x y = match x, y with
			[], [] -> []
		  | [], y -> y
		  | x, [] -> x
		  | head_x :: tail_x, head_y :: tail_y -> 
				if head_x < head_y then
					head_x :: merge tail_x (head_y :: tail_y)
				else
					head_y :: merge (head_x :: tail_x) tail_y
		in
		merge (merge_sort left)	(merge_sort right);;
                     
let rec string_of_lambda x = match x with
	Var x -> x
  | App (a, b) -> "(" ^ string_of_lambda a ^ " " ^ string_of_lambda b ^ ")"
  | Abs (a, b) -> "(\\" ^ a ^ "." ^ string_of_lambda b ^ ")";;
	
let lambda_of_string x =
	let x = x ^ ";" in
	let pos = ref 0 in
	let is_var a = (('a' <= a) && (a <= 'z')) || (('0' <= a) && (a <= '9')) || (a = '\'') in
	let parse_var () = 
		let rec get_var ans = match x.[!pos] with
			a when is_var a       -> pos := !pos + 1;	get_var (ans ^ (String.make 1 a))
		  | '.' | ' ' | ')' | ';' -> ans
		  | _                     -> failwith "Unexpected symbol" in get_var "" 
	in
	let rec 
	parse_expr flag = match x.[!pos] with
		'\\' -> pos := !pos + 1; let a = parse_var () in Abs (a, parse_expr true)
	  | '.'  -> pos := !pos + 1; parse_expr true
	  | '('  -> pos := !pos + 1; let a = parse_expr true in
									if x.[!pos] <> ')' then failwith "Missing \")\""
									else (
										pos := !pos + 1; 
										if flag then parse_app a else a
									)
	  | ';'  -> failwith "Expression ended unexpectedly"
	  | _    -> let a = parse_var () in if flag then parse_app (Var a) else Var a
	and
	parse_app ans = match x.[!pos] with
		' ' -> pos := !pos + 1; let a = parse_expr false in parse_app (App (ans, a))
	  | _   -> ans
	in 
	parse_expr true;;