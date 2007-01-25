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

(* I want to minimize the sum of the variables while maximizing the numbers of zeros.
   I am not quite interested in an optimal... A good value is enough
*)
let debug = false

type kind = Eq | Ge

type cstr = {coeffs :num list ; op : kind ; cst : num}


let string_of_nums l = List.fold_right (fun n s -> (string_of_num n)^";"^s) l ""

let string_of_kind = function Eq -> "Eq" | Ge -> "Ge"

let string_of_cstr  {coeffs =a  ; op = b ; cst =c} =
  Printf.sprintf "{coeffs = %s;op=%s;cst=%s}" (string_of_nums a) (string_of_kind b) (string_of_num c)
  

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

  let inter i1 i2 = 
    let res = inter i1 i2 in
    if debug then Printf.printf "inter %s %s = %s\n" (string_of_intrvl i1) (string_of_intrvl i2) (string_of_intrvl res);
    res


end
open Interval

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

let bound_of_constraint (a,b) = 
  let res =  bound_of_constraint (a,b) in
  if debug then Printf.printf "bound_of_constraint %s %s = %s\n" (string_of_num a) (string_of_num b) (string_of_intrvl res) ;
  res

exception Contradiction

(* Is-it tail-recursive ? *)

let rec partition m pos zero neg =
  match m with
    | [] -> (pos,zero,neg)
    | e::m -> 
	match e with
	  | [],b -> 
	      begin
		match bound_of_constraint ((Int 0),b) with
		  | Empty -> raise Contradiction
		  |  _    -> partition m pos zero neg
	      end
	  | [v],b -> 
	      begin
		match bound_of_constraint (v,b) with
		  | Empty -> raise Contradiction
		  | Itv (MinusInfty,PlusInfty) -> (*v=0*) partition m pos zero neg
		  |  _  -> (* is-it an upper or lower bound ? *)
		       begin
			 match compare_num v (Int 0) with
			   | 0 -> failwith "Bug"
			   | 1 -> partition m ((v,[],b)::pos) zero neg
			   | -1 -> partition m pos zero ((v,[],b)::neg)
			   | _ -> failwith "Bug"
		       end
	      end
	  | v::e,b ->  match compare_num v (Int 0) with
	      | 1 -> partition m ((v,e,b)::pos) zero neg
	      | 0 -> 
		  (* Anecdotique
		  if List.for_all (fun x -> compare_num x (Int 0) = 0) e
		  then 
		    (match bound_of_constraint (Int 0,b) with
		      | Empty -> raise Contradiction
		      | _     -> partition m pos zero neg
		    )
		  else *)
		  partition m pos ((e,b)::zero) neg
	      | _ -> partition m pos zero ((v,e,b)::neg)


(* sharing zero and one improves performance... a lot *)
let zero = Int 0
let one = Int 1

(* Should I tabulate ?*)
let add_num x y = 
  let res = add_num  x y in
    match res with
      | Int 0 -> zero
      | Int 1 -> one
      | _ -> res


let rec lin_comb x y l1 l2 =
  match l1 with 
    | [] -> List.map (mult_num y) l2
    | e1::l1' -> 
	match l2 with
	  | [] -> List.map (mult_num x) l1
	  | e2::l2 -> (add_num (mult_num x e1) (mult_num y e2))::(lin_comb x y l1' l2)


let proj_cstr (p,pc,b) (n,nc,b') =
  let nopp = minus_num n in 
  (lin_comb nopp p pc nc,add_num (mult_num nopp b) (mult_num p b'))


  
let rec rev_map_acc f l acc = 
  match l with
    | [] -> acc
    | e::l -> rev_map_acc f l ((f e)::acc)


let project m = 
  let rec _project pos neg res =
    match pos with
      | [] -> res
      | e::pos -> _project pos neg (rev_map_acc  (proj_cstr e)  neg  res) in

  let (pos,zero,neg) = partition m [] [] [] in
  _project pos neg zero





let rec bounds m itv =
  match m with
    | [] -> itv
    | e::m -> bounds m (inter itv (bound_of_constraint e))

let rec product l1 l2 = 
  match l1 with
      [] -> 
	begin
	  match l2 with
	    |[] -> (Int 0)
	    |e::l -> (Int 0)
	end
      | e1::l1 ->
	  begin
	    match l2 with
	      | [] -> (Int 0)
	      | e2::l2 -> add_num (mult_num e1 e2)  (product l1 l2)
	  end

let eval_constraint vals (coeffs,c)  = 
  match coeffs with
    | [] -> ((Int 0),c)
    | e::l -> (e,sub_num c (product l vals))

(* minimize all the variables...one by one*)

let rec optimize m =
  if debug then Printf.printf "nb of constraints %i\n" (List.length m); flush stdout;
  match m with
    | [] -> Some [] (* nothing to do - there are no constraints *)
    |  l -> (* length of constraints in l is at most 1 *)
	 try
	   match optimize (project l) with
	     | None -> None
	     | Some vals -> 
		 (* use this mapping to instanciate variables in l *)
		 let l' = List.rev_map (eval_constraint vals) l in
		 let itv =  bounds l' (Itv(MinusInfty,PlusInfty)) in
		 match pick_closed_to_zero itv with
		   | None -> None
		   | Some i -> 
		       match vals with
			 | [] -> if compare_num i (Int 0) =0 then Some [] else Some [i]
			 | _   -> Some (i::vals)
		   
	 with Contradiction -> None (* projection found a trivial contradiction *)


(* In case of equations, apply Gaussian elimination i.e. substitute *)

let find_non_zero l = 
  let rec _find_non_zero l n =
    match l with
      | [] -> None
      | e::l -> if compare_num e (Int 0) = 0 then _find_non_zero l (n+1) else Some n
  in _find_non_zero l 0

let rec split_at  (v:int) (l: num list) =
  match compare v 0 with
    | 0 ->
	begin match l with
	    | [] ->   (Int 0,[])
	    | e::l -> (e,l)
	end
    | 1 -> 
	begin match l with
	  | [] -> let (e',l') = split_at (v-1) l in (e',(Int 0)::l')
	  | e::l -> let (e',l') = split_at (v-1) l in (e',e::l')
	end
    | _ -> failwith "Split at negative"
	  

type ('a,'b) lr = L of 'a | R of 'b

let rec find_equation l cstr = 
  match l with
    | []  -> L cstr
    | e::l -> let {coeffs = coeffs ; op = op ; cst = cst} = e in
      match op with
	| Eq -> 
	    (match find_non_zero coeffs with
	      | None -> 
		  (match bound_of_constraint (Int 0,cst) with
		    | Empty -> raise Contradiction
		    | _    -> find_equation l cstr)
	      | Some n -> (R(n,e,l,cstr) ))
	| Ge -> find_equation l (e::cstr)
		

let pivot n split cstr =
  let {coeffs = coeffs ; op = op ; cst = cst'} = cstr in
  let (v,cf,cst) = split in
  let (v',cf') = split_at n coeffs in
  let (coeff',cst') = 
    match compare_num v (Int 0),compare_num v' (Int 0) with
      | 0 , _ -> failwith "Buggy"
      | _ ,0  -> (cf',cst')
      | 1 , -1 -> proj_cstr (v,cf,cst) (v',cf',cst')
      | -1 , 1 -> proj_cstr (v',cf',cst') (v,cf,cst) 
      | 1  , 1 -> proj_cstr (v',cf',cst') (minus_num v, List.map minus_num cf, minus_num cst)
      | -1 , -1 -> proj_cstr (minus_num v, List.map minus_num cf, minus_num cst) (v',cf',cst')
      | _ -> failwith "pivot" in
  {coeffs = coeff'; op = op ; cst = cst'}


let pivot n split cstr = 
  let (v,cf,cst) = split in
  let res = pivot n split cstr in 
  if debug then Printf.printf "pivot %i (%s,%s,%s) %s = %s\n" 
    n (string_of_num v) (string_of_nums cf) (string_of_num cst) (string_of_cstr cstr) (string_of_cstr res);
  res
	  
let pivots n split l =
  List.rev_map (pivot n split) l

let rec insert_at  (v:int) e l =
  match v with
    | 0 -> e::l
    | n -> match l with
	       | [] -> (Int 0)::(insert_at (n-1) e [])
	       | e'::l -> e'::(insert_at  (n-1) e l)



let rec optimize_with_equals may_contain_eq cstr = 
  if debug then Printf.printf "numbers %i %i\n" (List.length may_contain_eq) (List.length cstr);
  if debug then 
    (List.iter (fun x -> Printf.printf "%s\n" (string_of_cstr x)) may_contain_eq;
    Printf.printf "\n";
    List.iter (fun x -> Printf.printf "%s\n" (string_of_cstr x)) cstr);
  match find_equation  may_contain_eq cstr with
    | L cstr -> 
	optimize (List.rev_map (fun {coeffs = coeffs;op = op;cst=cst} -> (coeffs,cst)) cstr)
    | R(n,e,l,cstr) -> 
	let {coeffs = coeffs ; op = op ; cst = cst} = e in
	let (v,e') = split_at n coeffs in
	let l' = pivots n (v,e',cst) l in
	let cst' = pivots n (v,e',cst) cstr in
	match optimize_with_equals l' cst' with
	  | None -> None
	  | Some vals -> 
	      let (a,b) = eval_constraint vals (v::e',cst) in
	      let v = div_num b a in
	      Some (insert_at n v vals)

let optimise cstr = optimize_with_equals cstr []

(* In the following, I try to find an integer empty interval for a variable.
   Probably I could use a single Fourier elimination to get both a certificate of infeasibility AND  intervals...
   Beware : here, constraints are not sparse!
   And I do not deal with strict inequalities - neither do I do anything for disequalities...
*)

let nb_variables (l,n) = List.length l

let interval_of_constraint (l,b) = 
  bound_of_constraint  ( (match l with [] -> Int 0 | [v] -> v | _ -> failwith "interval_of_constraint"),b)
  
let  system_nb_vars m = 
  List.fold_left (fun mx e -> let mx' = nb_variables e in
		    if mx = -1 then mx' else (assert (mx = mx') ; mx)) (-1) m
  

let first_last (l,b) =
  match l with
    | [] -> (l,b)
    | e::l -> (l@[e],b)


let find_Q_interval m =
  let n = system_nb_vars m in

  let rec _narrow m n =
    if n = 1 then List.fold_left (fun itv x -> inter itv (interval_of_constraint x)) (Itv(MinusInfty,PlusInfty)) m
    else _narrow (project m) (n - 1) in

  (* _narrow_all (m:system of constraints) (p:position of the first variable in the initial system) *)
  let  rec _narrow_all m p =
    if p = n
    then None (* We have tried all the possibilities *)
    else
      (* Try to project over p *)
      let m = List.rev_map first_last m in
      let itv = _narrow m n in
	match interval_kind itv with
	  | O -> None
	  | Q -> Some(itv,p) (* Build a certificate from this *)
	  | Z -> _narrow_all m (p+1) 
  in
    _narrow_all m 0


let rec find_Q_interval_with_eq may_contain_eq cstr = 
  match find_equation  may_contain_eq cstr with
    | L cstr -> 
	find_Q_interval (List.rev_map (fun {coeffs = coeffs;op = op;cst=cst} -> (coeffs,cst)) cstr)
    | R(n,e,l,cstr) -> 
	let {coeffs = coeffs ; op = op ; cst = cst} = e in
	let (v,e') = split_at n coeffs in
	let l' = pivots n (v,e',cst) l in
	let cst' = pivots n (v,e',cst) cstr in
	  find_Q_interval_with_eq l' cst'


(*let find_Q_interval m = find_Q_interval_with_eq m []*)

(* x >= y    x <= y *)
let find_Q_interval cstr = 
  find_Q_interval (List.fold_left (fun l {coeffs = coeffs;op = op;cst=cst} -> 
							      match op with 
								| Ge -> (coeffs,cst)::l
								| Eq -> (coeffs,cst)::(List.map minus_num coeffs, minus_num cst)::l) [] cstr)



