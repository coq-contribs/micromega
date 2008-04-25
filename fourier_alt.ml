(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
(* Implements the Fourier method to optimize linear systems *)
(* 
   This is probably similar to the existing fourier contrib. 
   Differences: 
   use of  the Num library
   try to get (small) integer solutions

   Caveats: I have just learned that Fourier elimination exhibits an exponential worst case 

   (Scales better by taking equations)
*)

open Num

let debug = false

module Interval = 
struct

  type bound = MinusInfty | PlusInfty | Bd of num 
  
  type intrvl = Empty | Itv  of bound * bound


  let string_of_bound = function
    | MinusInfty -> "MinusInfty"
    | PlusInfty -> "PlusInfty"
    | Bd(num) -> Printf.sprintf "Bd(%s)"  (string_of_num num)

  let string_of_intrvl = function
    | Empty -> "Empty"
    | Itv(bd1,bd2) -> Printf.sprintf "Itv(%s,%s)" (string_of_bound bd1) (string_of_bound bd2)
    
  let pick_closed_to_zero = function
    | Empty -> None
    | Itv(MinusInfty,PlusInfty) -> Some (Int 0)
    | Itv(MinusInfty,Bd i) -> Some (min_num (Int 0) (floor_num  i))
    | Itv(Bd i,PlusInfty) -> Some (max_num (Int 0) (ceiling_num i))
    | Itv(Bd i,Bd j) -> 
	(let i1 = ceiling_num i in
	let i2 = floor_num j in
	match compare_num i1 i2 with
	  | 0 -> Some i1
	  | -1 -> 
	      let ai1 = abs_num i1 and ai2 = abs_num i2 in
	      let choose = min_num ai1 ai2 in
	      if compare_num  choose ai1 = 0
	      then Some i1
	      else Some i2
	  | 1 -> if debug then Printf.printf "Unlucky";
	      Some i
	  |  _ -> failwith "compare_error")
    | Itv(PlusInfty,_) -> failwith "not normalised"
    | Itv(_,MinusInfty) -> failwith "not normalised"

  type status = O | Z | Q 
	
  let interval_kind = function
    | Empty -> O
    | Itv(MinusInfty,PlusInfty) -> Z
    | Itv(MinusInfty,Bd i) -> Z
    | Itv(Bd i,PlusInfty) -> Z
    | Itv(Bd i,Bd j) -> 
	(let i1 = ceiling_num i in
	 let i2 = floor_num j in
	   match compare_num i1 i2 with
	     | 1 -> Q
	     | _ -> Z)
    | Itv(PlusInfty,_) -> failwith "not normalised"
    | Itv(_,MinusInfty) -> failwith "not normalised"




  let pick_closed_to_zero x =
    match pick_closed_to_zero x with
      | None -> 
	  if debug then Printf.printf "pick_closed_to_zero:%s" (string_of_intrvl x); None
      | Some i -> Some i  


  let normalise b1 b2 =
    match b1 , b2 with
      | Bd i , Bd j -> 
	  (match compare_num i j with
	    | 1 -> Empty
	    | _ -> Itv(b1,b2)
	  )
      | PlusInfty , _ -> Empty
      | _  ,  MinusInfty -> Empty
      |  _ -> Itv(b1,b2)

  let normalise b1 b2 = 
    let res = normalise b1 b2 in
    if res = Empty then if debug then Printf.printf "normalise %s Empty\n" (string_of_intrvl (Itv(b1,b2)));
    res


  let min x y = 
    match x , y with
      | MinusInfty , _ -> MinusInfty
      | PlusInfty  , y   -> y
      | _ , MinusInfty -> MinusInfty
      |   y , PlusInfty -> y
      | Bd i , Bd j -> 
	  match compare_num i j with
	    | 0  -> Bd i
	    | -1 -> Bd i
	    |  1 -> Bd j
	    |  _ -> failwith "min"
	
  let max x y = 
    match x , y with
      | MinusInfty , y -> y
      | PlusInfty  , _   -> PlusInfty
      | x , MinusInfty -> x
      |   _ , PlusInfty -> PlusInfty
      | Bd i , Bd j ->
	  match compare_num i j with
	    | 0  -> Bd i
	    | -1 -> Bd j
	    |  1 -> Bd i
	    |  _ -> failwith "max"

  let inter i1 i2 = 
    match i1,i2 with
      | Empty , _ -> Empty
      |  _   , Empty -> Empty
      | Itv (min1,max1) , Itv (min2,max2) -> 
	  let bmin = max min1 min2
	  and bmax = min max1 max2 in
	  normalise bmin bmax

(*  let inter i1 i2 = 
    let res = inter i1 i2 in
    if debug then Printf.printf "inter %s %s = %s\n" (string_of_intrvl i1) (string_of_intrvl i2) (string_of_intrvl res);
    res
*)

end
open Interval



module SysSet(V:Vector.S) : Vector.SystemS with module Vect = V = 
struct

  module Vect = V

  module Cstr = Vector.Cstr(V)
  open Cstr



  module CSet = Set.Make(Cstr)

  module CstrBag = 
  struct 
    type t = CSet.t
	
				exception Contradiction

    let empty = CSet.empty
    let is_empty = CSet.is_empty

    let add cstr b= 
						if Vect.is_null cstr.coeffs
						then 
								(* This is either a contradiction or a tautology *)
								if (cstr.op = Ge && cstr.cst <=/ Int 0) || (cstr.op = Eq && cstr.cst =/ Int 0)
								then b else (raise Contradiction)
						else CSet.add cstr b


				exception Found of cstr

				let find p s = 
						try 
								CSet.fold (fun e () -> if p e then raise (Found e) else ()) s () ;
							None
						with Found c -> Some c


    let fold  = CSet.fold

    let remove l _ = failwith "Not implemented"

    module Map = Map.Make(struct type t = int let compare : int -> int -> int = Pervasives.compare end)

    let split f t =
      let res = fold (fun e m -> let i = f e in
                        Map.add i (add e (try Map.find i m with Not_found -> empty)) m) t Map.empty in
        (fun i -> try Map.find i res with Not_found -> CSet.empty)

	type map = (int list * int list) Map.t


    let status (b:t) = 
      let _ , map = fold (fun c ( (idx:int),(res: map)) ->
                           ( idx + 1,
                             List.fold_left (fun (res:map) (pos,s) -> 
                                              let (lp,ln) = 
												try  Map.find pos res with Not_found -> ([],[]) in
												match s with
                                                  | Vect.Pos -> Map.add pos (idx::lp,ln) res
                                                  | Vect.Neg -> Map.add pos (lp, idx::ln) res) res (Vect.status c.coeffs))) b (0,Map.empty) in
        Map.fold (fun k e res -> (k,e)::res)  map []
		

    type it = CSet.t

    let iterator x = x

    let element it = 
      try 
								let x = CSet.choose it in
										Some(x,CSet.remove x it)
      with
										Not_found -> None

  end
end


(*
module BasicFourier(Vect : Vector.S) (Sys : Vector.SystemS with module Vect = Vect) =
struct
  module Vect = Vect
  module Cstr = Sys.Cstr
  module Bag = Sys.CstrBag

  open Cstr
  open Sys



  let debug = false

  let print_bag msg b =
	print_endline msg;
	CstrBag.fold (fun e () -> print_endline (Cstr.string_of_cstr e)) b () 


  (* a.x >= b*)
  let bound_of_constraint (a,b) =
    match compare_num a (Int 0) with
      | 0 -> 
	 if compare_num b (Int 0) = 1
	 then Empty
	else Itv (MinusInfty,PlusInfty)
      | 1 -> Itv (Bd (div_num  b a),PlusInfty)
      | -1 -> Itv (MinusInfty, Bd (div_num  b a))
      |   _ -> failwith "bound_of_constraint"
	   
	   
(*  let bound_of_constraint (a,b) = 
    let res =  bound_of_constraint (a,b) in
      if debug then Printf.printf "bound_of_constraint %s %s = %s\n" (string_of_num a) (string_of_num b) (string_of_intrvl res) ;
      res
*)
(* A system with only inequations --
*)
  exception Contradiction

  let partition i m =
    let splitter cstr =  compare_num (Vect.get i cstr.coeffs ) (Int 0) in
    let split = CstrBag.split splitter m in
      (split (-1) , split 0, split 1)

(* Should be generalised to Eq and Ge !
   For the moment, op = Ge
*)

  let lin_comb n1 c1 n2 c2 =
    { coeffs = Vect.lin_comb n1 c1.coeffs n2 c2.coeffs ; op = Ge ; cst = (n1 */ c1.cst) +/ (n2 */ c2.cst)}

(* TODO: normalise with Gcd *)
  let combine_project i c1 c2 =
    let p = Vect.get  i c1.coeffs  
    and n = Vect.get i c2.coeffs  in 
      assert (n </ Int 0 && p >/ Int 0) ;
    let nopp = minus_num n in 
    let c =lin_comb nopp c1 p c2  in
      {coeffs = Vect.update  i (fun _ -> Int 0) c.coeffs ; op = c.op ; cst= c.cst}


  let project i m =
    let (neg,zero,pos) = partition i m in
      
    let project1 cpos acc = 
      CstrBag.fold (fun cneg res -> CstrBag.add (combine_project i cpos cneg) res) neg acc in

      (CstrBag.fold project1 pos zero)


(*  let project i m =
	if debug then print_bag (Printf.sprintf "project %i" i) m ;
	let res = project i m in
	  if debug then print_bag "project res" res ;
	  res
*)
       (* Given a vector [x1 -> v1; ... ; xn -> vn]
	  and a constraint {x1 ; .... xn >= c }
       *)
  let evaluate_constraint i map cstr =
    let {coeffs = _coeffs ; op = _op ; cst = _cst} = cstr in
    let vi = Vect.get  i _coeffs  in
    let v = Vect.update i (fun _ -> Int 0) _coeffs in
      (vi, _cst -/ Vect.dotp map v)


  let rec bounds m itv =
    match m with
      | [] -> itv
      | e::m -> bounds m (inter itv (bound_of_constraint e))

  (* m does not contain equalities 
     returns a mapping which verifies the constraints
  *)

  let filter_constraints  m =
    CstrBag.fold (fun cstr b -> 
		   if Vect.is_null cstr.coeffs
		   then 
							(* This is either a contradiction or a tautology *)
		     if (cstr.op = Ge && cstr.cst <=/ Int 0) || (cstr.op = Eq && cstr.cst =/ Int 0)
		     then b else raise Contradiction
		   else CstrBag.add cstr b
		 ) m CstrBag.empty



  let optimise_ge m = 
    let rec xoptimise i m =
	  if debug then print_bag (Printf.sprintf "xoptimise %i" i) m ;
      if CstrBag.is_empty m
      then Some Vect.null
      else 
        (* There is at least one non-trivial constraint *)
		let proj = filter_constraints (project i m) in
          match xoptimise (i+1) proj with
            | None -> None
            | Some mapping -> 
               (* find a value for x0 *)
               let (it:intrvl) = CstrBag.fold (fun cstr itv -> Interval.inter 
												(bound_of_constraint (evaluate_constraint i mapping cstr)) itv) m (Itv (MinusInfty, PlusInfty)) in
                 match pick_closed_to_zero it with
                   | None -> None
                   | Some v -> let res =  (Vect.update i (fun _ -> v) mapping) in
					   if debug then Printf.printf "xoptimise res %i %s" i (Vect.string res) ;
					   Some res in
      try 
        xoptimise 0 m
      with Contradiction -> None




  let optimise_ge m = 
	if debug then print_bag "optimise_ge" m ;
	optimise_ge m



  let normalise cstr = 
    match cstr.op with
      | Ge -> [cstr]
      | Eq -> [{cstr with op = Ge}; 
	       {coeffs = Vect.mul (Int (-1)) cstr.coeffs ; op = Ge ; cst = minus_num cstr.cst}]


  let optimise_eq m =
    optimise_ge (CstrBag.fold (fun c bg -> List.fold_right CstrBag.add (normalise c) bg)  m CstrBag.empty)


  let optimise_eq m = 
	if debug then print_bag "optimise_eq" m ;
	optimise_eq m


  let optimise m = optimise_eq m

end
*)

module Fourier(Vect : Vector.S) (Sys : Vector.SystemS with module Vect = Vect) =
struct
  module Vect = Vect
  module Cstr = Sys.Cstr
  module Bag = Sys.CstrBag

  open Cstr
  open Sys



  let debug = false

  let print_bag msg b =
	print_endline msg;
	CstrBag.fold (fun e () -> print_endline (Cstr.string_of_cstr e)) b () 

  let print_bag_file file msg b =
				let f = open_out file in
						output_string f msg;
						CstrBag.fold (fun e () -> Printf.fprintf f "%s\n" (Cstr.string_of_cstr e)) b () 



  (* a.x >= b*)
  let bound_of_constraint (a,b) =
    match compare_num a (Int 0) with
      | 0 -> 
	 if compare_num b (Int 0) = 1
	 then Empty
	else Itv (MinusInfty,PlusInfty)
      | 1 -> Itv (Bd (div_num  b a),PlusInfty)
      | -1 -> Itv (MinusInfty, Bd (div_num  b a))
      |   _ -> failwith "bound_of_constraint"
	   
	   
(*  let bound_of_constraint (a,b) = 
    let res =  bound_of_constraint (a,b) in
      if debug then Printf.printf "bound_of_constraint %s %s = %s\n" (string_of_num a) (string_of_num b) (string_of_intrvl res) ;
      res
*)
(* A system with only inequations --
*)
  let partition i m =
    let splitter cstr =  compare_num (Vect.get i cstr.coeffs ) (Int 0) in
    let split = CstrBag.split splitter m in
      (split (-1) , split 0, split 1)


(* op of the result is arbitrary Ge *) 
  let lin_comb n1 c1 n2 c2 =
    { coeffs = Vect.lin_comb n1 c1.coeffs n2 c2.coeffs ; op = Ge ; cst = (n1 */ c1.cst) +/ (n2 */ c2.cst)}

(* BUG? : operator of the result ? *)

  let combine_project i c1 c2 =
    let p = Vect.get  i c1.coeffs  
    and n = Vect.get i c2.coeffs  in 
      assert (n </ Int 0 && p >/ Int 0) ;
    let nopp = minus_num n in 
    let c =lin_comb nopp c1 p c2  in
				let gcd = Utils.gcd_list [Big_int (Vect.gcd c.coeffs) ; c.cst] in
				let gcd_1 = (div_num (Int 1) (Big_int gcd)) in
				let op = if c1.op = Ge ||  c2.op = Ge then Ge else Eq in
      {coeffs = Vect.set  i (Int 0) ( Vect.mul gcd_1 c.coeffs) ; op = op ; cst= c.cst */ gcd_1 }


  let project i m =
    let (neg,zero,pos) = partition i m in
						let project1 cpos acc = 
								CstrBag.fold (fun cneg res -> CstrBag.add (combine_project i cpos cneg) res) neg acc in
      (CstrBag.fold project1 pos zero)



(*  let project i m =
	if debug then print_bag (Printf.sprintf "project %i" i) m ;
	let res = project i m in
	  if debug then print_bag "project res" res ;
	  res
*)
       (* Given a vector [x1 -> v1; ... ; xn -> vn]
	  and a constraint {x1 ; .... xn >= c }
       *)
  let evaluate_constraint i map cstr =
    let {coeffs = _coeffs ; op = _op ; cst = _cst} = cstr in
    let vi = Vect.get  i _coeffs  in
    let v = Vect.set i (Int 0) _coeffs in
      (vi, _cst -/ Vect.dotp map v)


  let rec bounds m itv =
    match m with
      | [] -> itv
      | e::m -> bounds m (inter itv (bound_of_constraint e))

  (* m does not contain equalities 
     returns a mapping which verifies the constraints
  *)

  let filter_constraints  m = m (* CstrBag.add does this filtering *)

  let compare_status (i,(lp,ln)) (i',(lp',ln')) = 
				let cmp = Pervasives.compare ((List.length lp) * (List.length ln))  ((List.length lp') * (List.length ln')) in
						if cmp = 0
						then Pervasives.compare i i'
						else cmp

		let cardinal m = CstrBag.fold (fun _ x -> x + 1) m 0

  let optimise_ge m = 
				let bound = let c = cardinal m in c * c in
    let rec xoptimise  m =
						Printf.printf "x" ; flush stdout;
						let c = cardinal m in
						if c > bound then (Printf.printf "xoptimise %i\n" c);
						let m = filter_constraints m in 
								match List.sort compare_status (CstrBag.status m) with
										| [] -> assert (CstrBag.is_empty m) ; Some Vect.null 
										| (i,(lp,ln))::_ -> 
													(* There is at least one non-trivial constraint *)
													let proj =  (project i m) in
															match xoptimise  proj with
																	| None -> None
																	| Some mapping -> 
																				(* find a value for x0 *)
																				let (it:intrvl) = CstrBag.fold (fun cstr itv -> Interval.inter 
																																																					(bound_of_constraint (evaluate_constraint i mapping cstr)) itv) m (Itv (MinusInfty, PlusInfty)) in
																						match pick_closed_to_zero it with
																								| None -> None
																								| Some v -> let res =  (Vect.set i v mapping) in
																												if debug then Printf.printf "xoptimise res %i %s" i (Vect.string res) ;
																												Some res in
      try 
        xoptimise  m
      with CstrBag.Contradiction -> None


		let lightest_projection  l c m  =
				let bound = c in 
(*						Printf.printf "l%i" bound; flush stdout ; *)
				let rec xlight best l =
						match l with
								| [] -> best
								| i::l -> 
											let proj = filter_constraints (project i m) in
											let cproj = cardinal proj in
													(*Printf.printf " p %i " cproj; flush stdout;*)
													match best with
															| None -> if cproj < bound then Some(cproj,proj,i) else xlight (Some(cproj,proj,i)) l
															| Some (cbest,_,_) -> 		
																		if cproj < cbest 
																		then 
																				if cproj < bound then Some(cproj,proj,i)
																				else xlight (Some(cproj,proj,i)) l 
																		else xlight best l in
						xlight None l
											


		exception Equality of cstr

		let find_equality m =
				try
						CstrBag.fold (fun c () -> 
																					let negc = {coeffs = Vect.mul (Int (-1)) c.coeffs ; op = c.op ; cst = c.cst} in
																							match CstrBag.find (fun x -> Cstr.compare negc x = 0) m with
																									| None -> ()
																									| Some _ -> raise (Equality c)) m () ; None
				with
								Equality c -> Some {c with op = Eq}
(*									Printf.printf "%s" (Cstr.string_of_cstr c) ; flush stdout ;*)


		let pivot (n,v) eq ge =
				assert (eq.op = Eq) ;
				let res = 
						match compare_num v (Int 0), compare_num (Vect.get n ge.coeffs) (Int 0)with
								| 0 , _ -> failwith "Buggy"
      | _ ,0  -> ge
      | 1 , -1 -> combine_project n eq ge
      | -1 , 1 -> combine_project n ge eq
      | 1  , 1 -> combine_project n ge {coeffs = Vect.mul (Int (-1)) eq.coeffs; op = eq.op ; cst = minus_num eq.cst}
      | -1 , -1 -> combine_project n {coeffs = Vect.mul (Int (-1)) eq.coeffs; op = eq.op ; cst = minus_num eq.cst} ge
      | _ -> failwith "pivot" in
						if debug then Printf.printf "pivot %i %s %s %s = %s\n" n (string_of_num v) (Cstr.string_of_cstr eq) (Cstr.string_of_cstr ge) (Cstr.string_of_cstr res);
						res


(* Would be nicer to have a mutual recusion between optimise_ge && optimise_eq *)
  let optimise_ge m = 
				let c = cardinal m in
				let bound =  2 * c  in
						(*Printf.printf "optimise_ge: %i\n" c; flush stdout;*)

						let rec xoptimise  m =
								match find_equality m with
										| None -> 
													begin
													let c = cardinal m in
															let l = List.map fst (List.sort compare_status (CstrBag.status m)) in
															let proj = 
																	if c > bound 
																	then lightest_projection  l c m
																	else match l with
																			| [] -> None
																			| i::_ -> Some(0,filter_constraints (project i m),i) in
																	match proj with
																			| None -> assert (CstrBag.is_empty m) ; Some Vect.null 
																			| Some(_,proj,i) -> (* It might be empty *)
																						match xoptimise  proj with
																								| None -> None
																								| Some mapping -> 
																											(* find a value for x0 *)
																											let (it:intrvl) = CstrBag.fold (fun cstr itv -> Interval.inter 
																																																												(bound_of_constraint (evaluate_constraint i mapping cstr)) itv) m (Itv (MinusInfty, PlusInfty)) in
																													match pick_closed_to_zero it with
																															| None -> None
																															| Some v -> let res =  (Vect.set i v mapping) in
																																			if debug then Printf.printf "xoptimise res %i %s" i (Vect.string res) ;
																																			Some res 
													end
										| Some eq -> 									
													match Vect.status eq.coeffs with
															| [] -> assert false
															| (i,_)::_ -> 
																		let p  = (i,Vect.get i eq.coeffs) in
																		let m' = CstrBag.fold (fun ge res -> CstrBag.add (pivot p eq ge) res) m CstrBag.empty in
																				match xoptimise (filter_constraints m') with
																						| None -> None
																						| Some mapp -> 
																									let (a,b) = evaluate_constraint i mapp eq in
																											Some (Vect.set i (div_num b a) mapp) in
								try 
										let res = xoptimise  (filter_constraints m)  in
												(*print_endline "\noptimise_ge: some" ;*) res
								with CstrBag.Contradiction -> (*print_endline "\noptimise_ge: none" ;*)  None



  let optimise_ge m = 
				if debug then print_bag "optimise_ge" m ;
				optimise_ge m



  let normalise cstr = 
    match cstr.op with
      | Ge -> [cstr]
      | Eq -> [{cstr with op = Ge}; 
	       {coeffs = Vect.mul (Int (-1)) cstr.coeffs ; op = Ge ; cst = minus_num cstr.cst}]


  let optimise_eq m =
    optimise_ge (CstrBag.fold (fun c bg -> List.fold_right CstrBag.add (normalise c) bg)  m CstrBag.empty)




		let optimise_eq m =
				let m = filter_constraints m in
						match CstrBag.find (fun c -> c.op = Eq) m with
						| None -> optimise_ge m
						| Some eq -> 
									match Vect.status eq.coeffs with
											| [] -> assert false
											| (i,_)::_ -> 
														let p  = (i,Vect.get i eq.coeffs) in
														let m' = CstrBag.fold (fun ge res -> CstrBag.add (pivot p eq ge) res) m CstrBag.empty in
																match optimise_eq m' with
																		| None -> None
																		| Some mapp -> 
																					let (a,b) = evaluate_constraint i mapp eq in
																							Some (Vect.set i (div_num b a) mapp)
																
  let optimise m = 
				try 
						optimise_eq m
				with CstrBag.Contradiction -> None

(* Find a rational interval for a variable *) 

  let find_Q_interval sys = 
				let rec xfind sys = 
						let variables = List.map fst (List.sort compare_status (CstrBag.status sys)) in
								match variables with
										| []  -> None
										| [v] -> let itv = CstrBag.fold (fun cstr itv -> 
																																												assert (Vect.is_null (Vect.set v (Int 0) cstr.coeffs));
																																												Interval.inter 
																																													(bound_of_constraint (Vect.get v cstr.coeffs  , cstr.cst)) itv) sys (Itv (MinusInfty, PlusInfty)) in
														(match interval_kind itv with
																	| O -> if debug then print_endline "find_Q failure" ; None
																	| Q -> if debug then print_endline "find_Q success" ; Some(itv,v) (* Build a certificate from this *)
																	| Z -> if debug then print_endline "find_Q failure" ; None (* I should try to optimise another variable *)
														)
										|  v::_  -> xfind (project v sys) in
						try 
								xfind (CstrBag.fold (fun c bg -> List.fold_right CstrBag.add (normalise c) bg)  sys CstrBag.empty)
						with CstrBag.Contradiction -> None



end
