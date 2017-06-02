type algebraic_term = Var of string | Fun of string * (algebraic_term list)

(* string -> algebraic_term -> int *)
let rec contains str term = match term with
		(Var a) -> if a = str then 1 else 0
	  | (Fun (f, lst)) -> (contains_lst str lst) lor (if f = str then 2 else 0)
	and contains_lst str lst = match lst with
		[] -> 0
	  | (head :: tail) -> (contains str head) lor (contains_lst str tail);; 

let rec get_new_var x = 
	let cnt = ref 0 in
	(* string -> (algebraic_term * algebraic_term) list -> bool *)
	let rec system_contains str x = match x with 
		[] -> false
	  | ((left, right) :: tail) -> (contains str left <> 0) || (contains str right <> 0) || (system_contains str tail) in
	
	while (system_contains ("new_var_" ^ string_of_int !cnt) x) 
	do cnt := !cnt + 1 
	done;
	("new_var_" ^ string_of_int !cnt);;

(* По списку уравнений вернуть одно уравнение *)
(* (algebraic_term * algebraic_term) list -> (algebraic_term * algebraic_term) *)
let system_to_equation system = 
	let rec impl system left right = match system with
		[] -> left, right
	  | (head_left, head_right) :: tail -> impl tail (head_left :: left) (head_right :: right) in
	let new_var = get_new_var system in
		let ans_left, ans_right = impl system [] [] in
			(Fun(new_var, ans_left), Fun(new_var, ans_right));;

			
module String_map = Map.Make (String);;

(* Применить подстановку к терму *)
(* (string * algebraic_term) list -> algebraic_term -> algebraic_term *)
let apply_substitution subst term = 
	let rec init subst map = match subst with 
        [] -> map
	  | (k, v) :: tail -> init tail (String_map.add k v map) in
	let map = init subst String_map.empty in

	let rec impl_term term = match term with
		Var a -> if String_map.mem a map then String_map.find a map else (Var a)
	  | Fun(f, lst) -> Fun(f, impl_list lst)

	and impl_list lst = 
		let rec impl lst ans = match lst with 
			[] -> ans 
		  | head :: tail -> impl tail ((impl_term head) :: ans) in
	
	impl lst [] in
	impl_term term;;


(* Применить подстановку к системе *)
(* (string * algebraic_term) list -> (algebraic_term * algebraic_term) list -> (algebraic_term * algebraic_term) list *)
let apply_substitution_to_system subst system = 
	let rec impl system ans = match system with
		[] -> ans
	  | (left, right) :: tail -> impl tail (((apply_substitution subst left), (apply_substitution subst right)) :: ans)
	  
	in impl system [];; 
	
let rec equal_terms term1 term2 = match (term1, term2) with
		(Var a, Var b) -> a = b
	  | (Fun(f, list1), Fun(g, list2)) -> f = g && equal_lists list1 list2 
	  | _ -> false

	and equal_lists list1 list2 = match (list1, list2) with
		([], []) -> true
	  | (head1 :: tail1), (head2 :: tail2) -> (equal_terms head1 head2) && (equal_lists tail1 tail2) 
	  | _ -> false;;

(* Проверить решение *)
(* (string * algebraic_term) list -> (algebraic_term * algebraic_term) list -> bool *)
let rec check_solution subst system = 
	let equation_after_subst equat = match equat with
		(left, right) -> equal_terms (apply_substitution subst left) (apply_substitution subst right) in
	match system with
		[] -> true
	  | head :: tail -> (equation_after_subst head) && (check_solution subst tail);;


exception No_solution of string;;
module String_set = Set.Make (String);;

let rec to_string_system system = match system with
		[] -> ""
	  | head :: tail -> (to_string_equation head) ^ "\n" ^ (to_string_system tail)
	and to_string_equation (left, right) = (to_string_term left) ^ " = " ^ (to_string_term right)
	and to_string_term term = match term with
		Var a -> a
	  | Fun(f, lst) -> f ^ "(" ^ (to_string_list lst) ^ ")"
	and to_string_list lst = match lst with
		[] -> ""
	  | (head :: []) -> (to_string_term head)
	  | (head :: tail) -> (to_string_term head) ^ " " ^ (to_string_list tail);;
	  	
	
(* Решить систему; если решения нет -- вернуть None *)
(* (algebraic_term * algebraic_term) list -> (string * algebraic_term) list option *)
let solve_system system = 
	let third_rule list1 list2 = 
		let rec third_rule_impl list1 list2 new_syst = match (list1, list2) with
			([], []) -> new_syst
		  | (head1 :: tail1, head2 :: tail2) -> third_rule_impl tail1 tail2 ((head1, head2) :: new_syst) 
		  | _ -> raise (No_solution "Error with Fun's arguments. How can we get there?")  in
		third_rule_impl list1 list2 [] in
	
	let rec robinson system answer = 
		if String_set.cardinal answer = List.length system
		then system
		else match system with
			[] -> raise (No_solution "How can we get there?")
		  | (left, right) :: tail -> 
				if equal_terms left right
				then robinson tail answer
				else match (left, right) with
					(Var a, right) -> 
							if  contains a right land 1 <> 0 
							then raise (No_solution "\"x\" both in lhs and rhs")
							else let answer = String_set.add a answer in
								robinson (List.append (apply_substitution_to_system [a, right] tail) [(left, right)]) answer
				  | (left, Var a) -> robinson (List.append tail [(right, left)]) answer
				  | Fun(f, list1), Fun(g, list2) -> 
							if f <> g || List.length list1 <> List.length list2
							then raise (No_solution "Different Fun's or arguments mismatch")
							else robinson (List.append tail (third_rule list1 list2)) answer in
							
		let rec get_answer answer new_ans = match answer with
			[] -> new_ans
		  | ((Var a, right) :: tail) -> get_answer tail ((a, right) :: new_ans) 
		  | _ -> failwith "How can we get there?" in
		
		try 
			let ans = robinson system String_set.empty in
			print_string (to_string_system ans);
			(Some (get_answer (ans) []))
		with (No_solution error) -> print_string (error ^ "\n");None;;
		

(* TESTS *)
(*
print_string "Test 0:\n";;
let sys0 = [(Var "a", Var "b"); (Var "x", Var "y")];;
print_string (to_string_system sys0);;
print_string "Answer:\n";;
let a = solve_system sys0;;
print_string "======================\nTest 1:\n";;


let sys1 = [(Fun("f",[Var "a"]), Fun("f",[Fun("g",[Fun("h",[Var "b"])])])); (Var "a", Var "b")];;
print_string (to_string_system sys1);;
print_string "Answer:\n";;
let b = solve_system sys1;;
print_string "======================\nTest 2:\n";;


let sys2 = [(Fun("f",[Var "a"]), Var "b")];;
print_string (to_string_system sys2);;
print_string "Answer:\n";;
let c = solve_system sys2;;
print_string "======================\nTest 3:\n";;

let sys3 = [Fun("f",[Var "a"; Var "b"]), Fun("f",[Var "x"; Var "y"])];;
print_string (to_string_system sys3);;
print_string "Answer:\n";;
let d = solve_system sys3;;
print_string "======================\nTest 4:\n";;


let sys4 = [Fun("f",[Var "a"; Var "b"]), Fun("g",[Var "x"; Var "y"])];;
print_string (to_string_system sys4);;
print_string "Answer:\n";;
let e = solve_system sys4;;
print_string "======================\nTest 5:\n";;

let sys5 = [Fun("f",[Var "a"; Var "b"]), Fun("f",[Var "x"; Var "y"; Var "z"])];;
print_string (to_string_system sys5);;
print_string "Answer:\n";;
let d = solve_system sys5;;
print_string "======================\nTest 6:\n";;


let sys6 = [(Var "a", Fun("f", [Var "a"]))];;
print_string (to_string_system sys6);;
print_string "Answer:\n";;
let f = solve_system sys6;;
print_string "======================\nTest 7:\n";;

let sys7 = [(Var "a", Var "a")];;
print_string (to_string_system sys7);;
print_string "Answer:\n";;
let g = solve_system sys7;;
print_string "======================\n";;
*)