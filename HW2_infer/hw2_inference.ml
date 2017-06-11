open Hw1
open Hw1_reduction
open Hw2_unify

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type

module String_map = Map.Make(String)
(* lambda -> ((string * simp_type) list * simp_type) option *)
let infer_simp_type lam =
	let cnt = ref 0 in
	
	let get_new_type () = 
		cnt := !cnt + 1;
		"new_type_" ^ string_of_int !cnt in
		
	let rec to_system lam types = match lam with
		Hw1.Var a -> ([], String_map.find a types)
	  | Hw1.App(a, b) -> let (sys1, type1) = to_system a types in
					 let (sys2, type2) = to_system b types in
					 let new_type = S_Elem(get_new_type ()) in
					 (List.append sys1 (List.append sys2 ((type1, S_Arrow(type2, new_type)) :: [])), new_type)
	  | Hw1.Abs(a, b) -> let add_types = String_map.add a (S_Elem (get_new_type ())) types in
					 let sys1, type1 = to_system b add_types in
					 (sys1, S_Arrow(String_map.find a add_types, type1)) in
					 
	let rec typed_vars lst map = match lst with
		[] -> map
	  | (head :: tail) -> typed_vars tail (String_map.add head (S_Elem(get_new_type ())) map) in
	  
	let rec simp_type_to_term stype = match stype with
		S_Elem a -> Hw2_unify.Var a
	  | S_Arrow(a, b) -> Hw2_unify.Fun("->", (simp_type_to_term a) :: (simp_type_to_term b) :: []) in

	let rec term_to_simp_type term = match term with
		Hw2_unify.Var a -> S_Elem a
	  | Hw2_unify.Fun(name, left::right::[]) -> S_Arrow (term_to_simp_type left, term_to_simp_type right)
	  | _ -> failwith "How can we get there?" in
	
	let sys, typ = to_system lam (typed_vars (free_vars lam) String_map.empty) in
	match solve_system (List.map (fun (a, b) -> (simp_type_to_term a, simp_type_to_term b)) sys) with
		None -> None
	  | Some solution -> Some (List.map (fun (a, b) -> (a, term_to_simp_type b)) solution, 
							   term_to_simp_type (apply_substitution solution (simp_type_to_term typ))
							  );;


type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

module String_set = Set.Make(String) 
exception Inference_except of string;; 
(* hm_lambda -> ((string * hm_type) list * hm_type) option *)
let algorithm_w hm_lam = 
	let cnt = ref 0 in
	let get_new_name () = 
		cnt := !cnt + 1;
		"new_name_" ^ string_of_int !cnt in
		
	let free_types hmtype = 
		let rec free_blocked hmtype set = match hmtype with
			HM_Elem a -> if String_set.mem a set
						 then String_set.empty
						 else String_set.singleton a
		  | HM_Arrow(a, b) -> String_set.union (free_blocked a set) (free_blocked b set)
		  | HM_ForAll(a, b) -> free_blocked b (String_set.add a set)
	in free_blocked hmtype String_set.empty in
	
	let free_vars hmlambda = 
		let rec free_blocked hmlambda set = match hmlambda with
			HM_Var a -> if String_set.mem a set
						 then String_set.empty
						 else String_set.singleton a
		  | HM_App(a, b) -> String_set.union (free_blocked a set) (free_blocked b set)
		  | HM_Abs(a, b) -> free_blocked b (String_set.add a set)
		  | HM_Let(a, b, c) -> String_set.union (free_blocked b set) (free_blocked c (String_set.add a set))
	in free_blocked hmlambda String_set.empty in
	
	let forAll_add hmtype types = 
		let known_types = String_map.fold (fun a b set -> String_set.union (free_types b) set) types String_set.empty in
		String_set.fold (fun a b -> HM_ForAll(a, b)) 
						(String_set.fold (fun a b -> if String_set.mem a known_types 
													 then b 
													 else String_set.add a b)
										 (free_types hmtype) 
										 String_set.empty
						) 
						hmtype in
	
	let rec make_subst subst hmtype set = match hmtype with
		HM_Elem a -> if String_set.mem a set
					 then hmtype
					 else
						if String_map.mem a subst
						then String_map.find a subst
						else hmtype
	  | HM_Arrow(a, b) -> HM_Arrow(make_subst subst a set, make_subst subst b set)
	  | HM_ForAll(a, b) -> HM_ForAll(a, make_subst subst b (String_set.add a set)) in
	  
	let make_subst_types subst types = 
		String_map.fold (fun a b map -> String_map.add a (make_subst subst b String_set.empty) map)
						types String_map.empty in
		
	let rec hmtype_to_term hmtype = match hmtype with
		HM_Elem a -> Hw2_unify.Var a
	  | HM_Arrow(a, b) -> Hw2_unify.Fun("->", (hmtype_to_term a) :: (hmtype_to_term b) :: [])
	  | _ -> failwith "Quantifier ForAll cannot be converted to algebraic_term" in
	 
	let rec term_to_hmtype term = match term with
		Hw2_unify.Var a -> HM_Elem a
	  | Hw2_unify.Fun(name, left::right::[]) -> HM_Arrow (term_to_hmtype left, term_to_hmtype right)
	  | _ -> failwith "How can we get there?" in
	
	let subst_to_subst subst1 subst2 = 
		String_map.fold 
			(fun a b map -> if String_map.mem a map then map else String_map.add a b map)
			subst2
			(String_map.fold (fun a b map -> String_map.add a (make_subst subst2 b String_set.empty) map)
							  subst1 String_map.empty) in
		
	let rec forAll_delete hmtype = match hmtype with
		HM_ForAll(a, b) -> make_subst (String_map.add a (HM_Elem(get_new_name ())) String_map.empty)
									  (forAll_delete b) String_set.empty
	  | _ -> hmtype in
		
	let rec w hmlambda types = match hmlambda with
		HM_Var a -> if String_map.mem a types
					then (forAll_delete (String_map.find a types), String_map.empty)
					else raise (Inference_except "Free var found. Any type is infered.")
	  | HM_App(a, b) ->
		( 	let (hmt1, types1) = w a types in
			let (hmt2, types2) = w b (make_subst_types types1 types) in
			let new_type = HM_Elem (get_new_name ()) in
			match solve_system (((hmtype_to_term (make_subst types2 hmt1 String_set.empty)),
							(hmtype_to_term (HM_Arrow(hmt2, new_type)))) :: []) with
			None -> raise (Inference_except "Cannot solve system")
		  | Some ans -> let ans_types = 
							subst_to_subst 
								(List.fold_left (fun map (str, term) -> String_map.add str (term_to_hmtype term) map)
												String_map.empty ans) 
								(subst_to_subst types2 types1) in
						(make_subst ans_types new_type String_set.empty, ans_types)
		)
	  | HM_Abs(a, b) -> let new_type = HM_Elem (get_new_name ()) in
						let (hmt1, types1) = w b (String_map.add a new_type (String_map.remove a types)) in
						(HM_Arrow(make_subst types1 new_type String_set.empty, hmt1), types1)
	  | HM_Let(a, b, c) -> let (hmt1, types1) = w b types in
						   let new_types = make_subst_types types1 types in
						   let (hmt2, types2) = w c (String_map.add a (forAll_add hmt1 new_types) 
																	(String_map.remove a new_types)) in
						   (hmt2, subst_to_subst types2 types1)
						
		in
		
	let types = String_set.fold (fun a map -> String_map.add a (HM_Elem (get_new_name ())) map)
								(free_vars hm_lam) (String_map.empty) in
	try
		let (typ, map) = w hm_lam types in
		Some (String_map.bindings map, typ)
	with (Inference_except e) -> None;;