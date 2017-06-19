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
	let cnt = ref 0 in
	
	let get_new_var () = 
		cnt := !cnt + 1;
		("var_" ^ string_of_int !cnt) in
	
	match (lam1, lam2) with
		(Var a, Var b) -> a = b
	  | (App(a1, b1), App(a2, b2)) -> (is_alpha_equivalent a1 a2) && (is_alpha_equivalent b1 b2)
	  | (Abs(a1, b1), Abs(a2, b2)) -> let new_var = Var (get_new_var ()) in
									  is_alpha_equivalent (make_subst new_var b1 a1) (make_subst new_var b2 a2)
	  | _ -> false;;

	  
module String_map = Map.Make(String)
		
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
	  | App(Abs(a, b), c) -> (true, make_subst c b a)
	  | App(a,b) -> let (yes, new_a) = impl a in
					if yes 
					then (yes, App(new_a, b))
					else
						let (yes, new_b) = impl b in
						(yes, App(a, new_b))
	  | Abs(a,b) -> let (yes, new_b) = impl b in
					(yes, Abs(a, new_b))
	in
	let (yes, ans) = impl (eqvy lam String_map.empty) in
	ans;;
	

type lambda_ref = Varref of string ref | Absref of (string * lambda_ref) ref | Appref of (lambda_ref * lambda_ref) ref;;
	
let rec lambda_to_lambda_ref lam = match lam with
	Var a -> Varref (ref a)
  | App(a, b) -> Appref (ref (lambda_to_lambda_ref a, lambda_to_lambda_ref b))
  | Abs(a, b) -> Absref (ref (a, lambda_to_lambda_ref b));;
  
let rec lambda_ref_to_lambda lamref = match lamref with
	Varref a -> Var !a
  | Appref a -> let (x, y) = !a in
				App (lambda_ref_to_lambda x, lambda_ref_to_lambda y)
  | Absref a -> let (x, y) = !a in
				Abs (x, lambda_ref_to_lambda y);;
				
(* lamref[z:=thetaref] *)
let rec subst_ref thetaref lamref z = match lamref with
	Varref a -> if !a = z
			  then thetaref
			  else lamref
  | Appref a -> let (x, y) = !a in 
				Appref (ref (subst_ref thetaref x z, subst_ref thetaref y z))
  | Absref a -> let (x, y) = !a in 
				if x = z
				then lamref
				else Absref (ref (x, subst_ref thetaref y z));;
	
(* Свести выражение к нормальной форме с использованием нормального
   порядка редукции; реализация должна быть эффективной: использовать 
   мемоизацию *)
(* lambda -> lambda *)
let rec reduce_to_normal_form lam = 
	let lamref = lambda_to_lambda_ref (eqvy lam String_map.empty) in
	let rec reduce lamref = match lamref with
		Varref a -> lamref
	  | Appref a -> let lam = !a in 
					(match lam with					
						(Absref a, b) -> let (x, y) = !a in
										 reduce (subst_ref b y x)
					  | _ -> let (x, y) = lam in 
							 let new_x = reduce x in
							 (match new_x with							 
								Absref new_a -> let (i, j) = !new_a in
												reduce (subst_ref y j i)
							  | _ -> a := (new_x, reduce y); lamref
							 )
					)
	  | Absref a -> let (x, y) = !a in
					a := (x, reduce y); lamref
						
	in lambda_ref_to_lambda (reduce lamref);;
