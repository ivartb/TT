 open Hw1
(* Вернуть список имён свободных переменных *)
(* lambda -> string list *)
let free_vars lam = 
	let rec free_blocked lam lst = match lam with
		Var a -> if List.mem a lst
				 then []
				 else (a :: [])
	  | App(a, b) -> List.append (free_blocked a lst) (free_blocked b lst)
	  | Abs(a, b) -> free_blocked b (a :: lst)
	in free_blocked lam [];;

(* Проверить свободу для подстановки. Параметры:
   что подставляем, где подставляем, вместо чего подставляем *)
(* lambda -> lambda -> string -> bool *)
(* lam[x:=theta] ? *)
let free_to_subst theta lam x =
	let free = free_vars theta in
	let rec free_blocked x lam lst = match lam with
		Var a -> if a = x
				 then if (List.exists (fun (a) -> List.mem a lst) free) then false else true
				 else true
	  | App(a, b) -> (free_blocked x a lst) && (free_blocked x b lst)
	  | Abs(a, b) -> if a = x
					 then true
					 else free_blocked x b (a :: lst)
	in free_blocked x lam [];;

(* Проверить, находится ли лямбда-выражение в нормальной форме *)
(* lambda -> bool *)
let rec is_normal_form lam = match lam with
	Var a -> true
  | App(Abs(a, b), c) -> false
  | App(a,b) -> (is_normal_form a) && (is_normal_form b)
  | Abs(a,b) -> is_normal_form b;;
  
let rec make_subst theta lam x = match lam with
		Var a -> if a = x
				 then theta
				 else lam
	  | App(a, b) -> App(make_subst theta a x, make_subst theta b x)
	  | Abs(a, b) -> if a = x
					 then lam
					 else Abs(a, make_subst theta b x);;

(* Проверить, альфа-эквивалентны ли лямбда-выражения *)
(* lambda -> lambda -> bool *)
let rec is_alpha_equivalent lam1 lam2 = 
	let cntr = ref 0 in
	
	let get_new_var () = 
		cntr := !cntr + 1;
		("var_" ^ string_of_int !cntr) in
	
	match (lam1, lam2) with
		(Var a, Var b) -> a = b
	  | (App(a1, b1), App(a2, b2)) -> (is_alpha_equivalent a1 a2) && (is_alpha_equivalent b1 b2)
	  | (Abs(a1, b1), Abs(a2, b2)) -> let new_var = Var (get_new_var ()) in
									  is_alpha_equivalent (make_subst new_var b1 a1) (make_subst new_var b2 a2)
	  | _ -> false;;
			

module String_map = Map.Make(String)
let subs = ref [] ;;

let cnt = ref 0;;
	
let rec eqvy lam map = 
	let get_new_var () = 
		cnt := !cnt + 1;
		("new_var_" ^ string_of_int !cnt) in
		
	match lam with
		Var a -> if String_map.mem a map
				 then Var (String_map.find a map) 
				 else lam
	  | App(a, b) -> App(eqvy a map, eqvy b map)
	  | Abs(a, b) -> let new_var = get_new_var () in
					 Abs(new_var, eqvy b (String_map.add a new_var map));;
		

(* Выполнить один шаг бета-редукции, используя нормальный порядок *)
(* lambda -> lambda *)
let normal_beta_reduction lam =
	let rec impl lam = match lam with
		Var a -> (false, lam)
	  | App(Abs(a, b), c) -> let neww = make_subst c b a in
							 subs := (App(Abs(a, b), c), neww) :: !subs;
							 (true, neww)
	  | App(a,b) -> let (yes, new_a) = impl a in
					if yes 
					then (subs := (App(a, b), App(new_a, b)) :: !subs;
						 (yes, App(new_a, b)))
					else
						let (yes, new_b) = impl b in
						if yes
						then subs := (App(a, b), App(a, new_b)) :: !subs;
						(yes, App(a, new_b))
	  | Abs(a,b) -> let (yes, new_b) = impl b in
					if yes
					then subs := (Abs(a, b), Abs(a, new_b)) :: !subs;	
					(yes, Abs(a, new_b))
	in
	let (yes, ans) = impl (eqvy lam String_map.empty) in
	if yes
	then subs := (lam, ans) :: !subs;					 
	ans;;
	
(* Свести выражение к нормальной форме с использованием нормального
   порядка редукции; реализация должна быть эффективной: использовать 
   мемоизацию *)
(* lambda -> lambda *)
let rec reduce_to_normal_form lam = 
	print_string ((string_of_bool (is_normal_form lam)) ^ ":	" ^ (string_of_lambda lam) ^ "\n");
	if is_normal_form lam
	then lam
	else
		match lam with
			App(a, b) -> if List.exists (fun (x, y) -> is_alpha_equivalent x a) !subs
						 then
							let (x1, y1) = List.find (fun (x, y) -> is_alpha_equivalent x a) !subs in
							if List.exists (fun (x, y) -> is_alpha_equivalent x b) !subs
							then 
								let (x2, y2) = List.find (fun (x, y) -> is_alpha_equivalent x b) !subs in
								reduce_to_normal_form (normal_beta_reduction
													(App(eqvy y1 String_map.empty, eqvy y2 String_map.empty)))
							else
							reduce_to_normal_form (normal_beta_reduction(App(eqvy y1 String_map.empty, b)))
						 else
							if List.exists (fun (x, y) -> is_alpha_equivalent x b) !subs
							then 
								let (x, y) = List.find (fun (x, y) -> is_alpha_equivalent x b) !subs in
								reduce_to_normal_form (normal_beta_reduction(App(a, eqvy y String_map.empty)))
							else reduce_to_normal_form (normal_beta_reduction lam)
		  | Abs(a, b) -> if List.exists (fun (x, y) -> is_alpha_equivalent x b) !subs
						 then 
							let (x, y) = List.find (fun (x, y) -> is_alpha_equivalent x b) !subs in
							reduce_to_normal_form (normal_beta_reduction(Abs(a, eqvy y String_map.empty)))
						 else reduce_to_normal_form (normal_beta_reduction lam)				
		  | _ -> if List.exists (fun (x, y) -> is_alpha_equivalent x lam) !subs
				 then 
					let (x, y) = List.find (fun (x, y) -> is_alpha_equivalent x lam) !subs in
					reduce_to_normal_form (normal_beta_reduction(eqvy y String_map.empty))
				 else reduce_to_normal_form (normal_beta_reduction lam);;

	
(*let a = App(App(Var ("x"), Abs("y", Var ("6"))), Abs("x", Var ("d")));;
print_string (string_of_lambda a);;
if is_normal_form a
then print_string "ok"
else print_string "bad";;*)

(*let a = App(App(Var ("x"), Abs("y", Var ("y"))), Abs("x", Var ("d")));;
let b = App(App(Var ("x"), Abs("z", Var ("z"))), Abs("kkk", Var ("d")));;
print_string ((string_of_lambda a) ^ " = " ^ (string_of_lambda b) ^ "\n");;
if (is_alpha_equivalent a b)
then print_string "ok"
else print_string "bad";;
*)

(*let a = App(App(Abs("y", App(Var ("x"), Var ("y"))), App(Var ("5"), Var("6"))), Var ("d"));;
print_string ((string_of_lambda a) ^ "\n");;
print_string ((string_of_lambda (normal_beta_reduction a)) ^ "\n");;
*)
(*
let t = App(App(Abs("x", Abs("y", Var ("x"))), Abs("x", Var ("x"))), App(Abs("x", App(Var ("x"), Var ("x"))), Abs("x", App(Var ("x"), Var ("x")))));;
let f = App(Abs("x", App(Var ("x"), Var ("x"))), Abs("x", App(Var ("x"), Var ("x"))));;

reduce_to_normal_form t;;
*)
(*
let t0 = "(\\x.x x x) ((\\x.x) (\\x.x))";;
reduce_to_normal_form (lambda_of_string t0);;
*)




