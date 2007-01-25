(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
(* We take as input a list of polynomials [p1...pn] and return an unfeasibility certificate polynomial. *)
open Micromega.Polynomial
open Big_int
open Num

let (<+>) = add_big_int
let (<->) = minus_big_int
let (<*>) = mult_big_int

type var = coq_Var

(* In the implementation of polynomials there is a bug - corrected in  Arnaud's code *)

module Monomial :
  sig
    type t
    val const : t
    val var : var -> t
    val find : var -> t -> int
    val mult : var -> t -> t
    val prod : t -> t -> t
    val compare : t -> t -> int
    val pp : out_channel -> t -> unit
    val fold : (var -> int -> 'a -> 'a) -> t -> 'a -> 'a
  end
=
struct
  (* A monomial is code by a multiset of variables  *)
  module Map = Map.Make(struct type t = var let compare = Pervasives.compare end)
  open Map

  type t = int Map.t

  (* The monomial that corresponds to a constant *)
  let const = Map.empty

  (* The monomial 'x' *)
  let var x = Map.add x 1 Map.empty

  (* Get the degre of a variable in a monomial *)
  let find x m = try find x m with Not_found -> 0

  (* Multiply a monomial by a variable *)
  let mult x m = add x (  (find x m) + 1) m

  (* Product of monomials *)
  let prod m1 m2 = Map.fold (fun k d m -> add k ((find k m) + d) m) m1 m2

  (* Total ordering of monomials *)
  let compare m1 m2 = Map.compare Pervasives.compare m1 m2

  let pp o m = Map.iter (fun k v -> 
    if v = 1 then Printf.fprintf o "x%i." (Utils.CoqToCaml.index k)
    else     Printf.fprintf o "x%i^%i." (Utils.CoqToCaml.index k) v) m

  let fold = fold

end


module  Poly :
(* A polynomial is a map of monomials *)
(* 
   This is probably a naive implementation (expected to be fast enough - Coq is probably the bottleneck)
   *The new ring contribution is using a sparse Horner representation.
*)
sig
  type t
  val get : Monomial.t -> t -> big_int 
  val variable : var -> t
  val add : Monomial.t -> big_int -> t -> t
  val constant : big_int -> t
  val mult : Monomial.t -> big_int -> t -> t
  val product : t -> t -> t
  val addition : t -> t -> t
  val uminus : t -> t
  val fold : (Monomial.t -> big_int -> 'a -> 'a) -> t -> 'a -> 'a
  val pp : out_channel -> t -> unit
end =
struct
  (*normalisation bug : 0*x ... *)
  module P = Map.Make(Monomial)
  open P

  type t = big_int P.t

  let pp o p = P.iter (fun k v -> Printf.fprintf o "(%s*%a)+" (string_of_big_int v) Monomial.pp k) p  

  (* Get the coefficient of monomial mn *)
  let get : Monomial.t -> t -> big_int = 
    fun mn p -> try find mn p with Not_found -> zero_big_int


  (* The polynomial 1.x *)
  let variable : var -> t =
    fun  x ->  add (Monomial.var x) unit_big_int empty
    

  (* The addition of a monomial *)

  let add : Monomial.t -> big_int -> t -> t =
    fun mn v p -> add mn ((get mn p)<+>v) p


  (*The constant polynomial *)
  let constant : big_int -> t =
    fun c -> add (Monomial.const) c empty

  (** Design choice: empty is not a polynomial **)

  (* The product by a monomial *)
  let mult : Monomial.t -> big_int -> t -> t =
    fun mn v p -> fold (fun mn' v' res -> P.add (Monomial.prod mn mn') (v<*>v') res) p empty

(*  let mult mn v p = 
    let res = mult mn v p in
    Printf.printf "mult : %s*%a * %a = %a\n" (string_of_big_int v) Monomial.pp mn pp p pp res;
    res *)
      
  let  addition : t -> t -> t =
    fun p1 p2 -> fold (fun mn v p -> add mn v p) p1 p2


  let product : t -> t -> t =
    fun p1 p2 -> 
      fold (fun mn v res -> addition (mult mn v p2) res ) p1 empty


  let uminus : t -> t =
    fun p -> map (fun v -> Big_int.minus_big_int v) p

  let fold = P.fold
      

end

open Utils


let rec dev_form p =
  match p with
    | Micromega.Pconst z ->  Poly.constant (CoqToCaml.z_big_int z)
    | Micromega.Pvar v ->  Poly.variable v
    | Micromega.Pmult(p1,p2) -> 
	let p1 = dev_form p1 in
	let p2 = dev_form p2 in
	let res = Poly.product p1 p2 in
(*	Printf.fprintf stdout "%a * %a = %a\n" Poly.pp p1 Poly.pp p2 Poly.pp res ;*)
	res
    | Micromega.Pplus(p1,p2) -> Poly.addition (dev_form p1) (dev_form p2)
(*    | Minus(p1,p2) -> Poly.addition (dev_form p1) (Poly.uminus (dev_form p2))*)
    | Micromega.Popp p ->  Poly.uminus (dev_form p)

let monomial_to_polynomial mn = 
  Monomial.fold 
    (fun v i acc -> Micromega.Pmult(Micromega.Polynomial.power (Micromega.Pvar v) (CamlToCoq.z i),acc)) 
    mn 
    (Micromega.Pconst (Micromega.Zpos Micromega.XH))
    
let rec fixpoint f x =
  let y' = f x in
    if y' = x then y'
    else fixpoint f y'

let rec rec_simpl_cone = function
  | S_Mult(t1, t2) -> Micromega.simpl_cone (S_Mult (rec_simpl_cone t1, rec_simpl_cone t2))
  | S_Add(t1,t2)  -> Micromega.simpl_cone (S_Add (rec_simpl_cone t1, rec_simpl_cone t2))
  |  x           -> Micromega.simpl_cone x


let simplify_cone c = fixpoint rec_simpl_cone  c


(* The binding with Fourier might be a bit obsolete -- how does it handle equalities ? *)

(* Certificates are elements of the cone such that P = 0  *)

(* To begin with, we search for certificates of the form:
   a1.p1 + ... an.pn + b1.q1 +... + bn.qn + c = 0
   where pi >= 0 qi > 0
    ai >= 0 
    bi >= 0
    Sum bi + c >= 1
   This is a linear problem: each monomial is considered as a variable.
   Hence, we can use fourier. *)

open Fourier_num

(* let m be a monomial
   and l a list of polynomial (developped form)
   We generate the constraint:
   _
   \
   /_ l(m) = 0 if mn is not the constant monomial

   _ 
   \
   /_ l(cst) + c = 0
*)

let constrain_monomial mn l  = 
  let coeffs = List.fold_left (fun acc p -> Big_int (Poly.get mn p)::acc) [] l in
  if mn = Monomial.const
  then  
    { coeffs = (Big_int unit_big_int):: (List.rev coeffs) ; op = Eq ; cst = Big_int zero_big_int  }
  else
    { coeffs = (Big_int zero_big_int):: (List.rev coeffs) ; op = Eq ; cst = Big_int zero_big_int  }


let rec list i n = 
  if n = 0
  then []
  else (i)::(list i (n-1))


let zeros n = list (Big_int zero_big_int) n


let rec id_matrix n = 
  if n = 0
  then []
  else if n = 1
  then [ [Big_int unit_big_int] ] 
  else ((Big_int unit_big_int)::(zeros (n-1))) :: (List.map (fun l -> (Big_int zero_big_int)::l) (id_matrix (n-1)))


let rec zip l1 l2 = 
  match l1 with
    | [] -> []
    | e1::l1 -> match l2 with
	| [] -> []
	| e2::l2 -> (e1,e2) :: (zip l1 l2)

let positivity l = 
  List.fold_right (fun (pol,redop) res  ->
		     match redop with
		       | Equal -> res
		       | _     -> {coeffs = (Big_int zero_big_int) :: pol ; op = Ge ; cst = Big_int zero_big_int}::res)
    (zip (id_matrix (List.length l)) (List.map snd l)) []

open Micromega.Polynomial
open Fourier_num

(* If the certificate includes at least one strict inequality, the obtained polynomial can also be 0 *)
let build_linear_system l =
  (* Gather the monomials:  HINT add up of the polynomials *)
  let l' = List.map fst l in
  let monomials = List.fold_left (fun acc p -> Poly.addition p acc) (Poly.constant zero_big_int) l' in
  (* For each monomial, compute a constraint *)
  let s0 = Poly.fold (fun mn _ res -> (constrain_monomial mn l')::res) monomials [] in
  (* I need at least something strictly positive *)
  let strict = {coeffs = (Big_int unit_big_int)::(List.map (fun (x,y) -> match y with Strict -> Big_int unit_big_int | _ -> Big_int zero_big_int) l);
		op = Ge ; cst = Big_int unit_big_int } in
  (* Add the positivity constraint *)
    {coeffs = [Big_int unit_big_int] ; op = Ge ; cst = Big_int zero_big_int}::(strict::(positivity l)@s0)


let make_certificate cert li = 
    match cert with
      | [] -> None
      | e::cert' -> 
	  let cst = match compare_big_int e zero_big_int with
	    | 0 -> S_Z
	    | 1 ->  S_Pos (Utils.CamlToCoq.positive_big_int e) 
	    | _ -> failwith "positivity error" 
	  in
	  let rec scalar_product cert l =
	    match cert with
	      | [] -> S_Z
	      | c::cert -> match l with
		  | [] -> failwith "make_certificate(1)"
		  | i::l ->  let r = scalar_product cert l in
		      match compare_big_int c  zero_big_int with
			| -1 -> S_Add (S_Ideal (Micromega.Pconst ( Utils.CamlToCoq.bigint c), S_In (CamlToCoq.nat i)), r)
			| 0  -> r
			| _ ->  S_Add (S_Mult (S_Pos (Utils.CamlToCoq.positive_big_int c),S_In (CamlToCoq.nat i)),r) in
	    Some (simplify_cone (S_Add (cst, scalar_product cert' li)))




let raw_certificate l = 
  let sys = build_linear_system l in
    match optimise sys with
      | None -> None
      | Some cert ->  Some (rats_to_ints cert)


let simple_linear_prover l =
  let (lc,li) = List.split l in
    match raw_certificate lc with
      |  None ->None (* No certificate *)
      | Some cert -> make_certificate cert li

let linear_prover l  =
  let li = List.combine l (Sos.(--) 0 (List.length l -1)) in
  let (l1,l') = List.partition (fun (x,_) -> if snd' x = Micromega.None then true else false) li in
  let l' = List.map (fun (c,i) -> let (Micromega.Pair(x,y)) = c in 
		       match y with Micromega.None -> failwith "cannot happen" | Micromega.Some y -> ((dev_form x, y),i)) l' in
    match simple_linear_prover l' with
      | Some cert -> Some cert (* diff are useless *)
      | None  -> 
	  let (lc,li) = List.split l' in
	  let rec find_cert = function
	    | [] -> None
	    | e::l -> let (Micromega.Pair(c,_),i) = e in
	      let p = dev_form c in
	      let cone_of_big_int e = 
		match compare_big_int e zero_big_int with
		  | 1 -> S_Pos (Utils.CamlToCoq.positive_big_int e) 
		  | _ -> failwith "cone_of_big_int"
	      in
		match raw_certificate ((p,Strict)::lc) , raw_certificate ((Poly.uminus p,Strict)::lc) with
		  | Some (cst::cdiff::c), Some (cst'::diff'::c') -> 
		      let mono = S_Mult(S_Mult (cone_of_big_int cdiff, cone_of_big_int diff'),
					(S_Monoid (CamlToCoq.list Utils.CamlToCoq.nat [i]))) in
			(match make_certificate (cst::c) li , make_certificate (cst'::c') li with
			|    Some c1 , Some c2 -> Some (simplify_cone (S_Add(mono, S_Mult(c1 , c2))))
			|   _ -> None)
		  |  _  -> find_cert l in
	    find_cert l1


(* The code that follows tries to solve goals NOT solvable over the rationals 
   (2 x  = 1  -> False)
   The approch consist in finding for a variable, say x, which values range over
   a rational interval without a single integer solution.
   Fourier can find such intervals - the 'rational' checker can prove the bounds of the interval.
   Lemma in Zpol.v prove the absence of integer solutions.
*)







open Sos
module M =
struct
  open Micromega

  let rec expr_to_term = function
    |  Pconst z ->  Const  (Big_int (CoqToCaml.z_big_int z))
    |  Pvar v ->  Var ("x"^(string_of_int (CoqToCaml.index v)))
    |  Pmult(p1,p2) -> 
	 let p1 = expr_to_term p1 in
	 let p2 = expr_to_term p2 in
	 let res = Mul(p1,p2) in
(*	Printf.fprintf stdout "%a * %a = %a\n" Poly.pp p1 Poly.pp p2 Poly.pp res ;*)
	   res
    |  Pplus(p1,p2) -> Add(expr_to_term p1, expr_to_term p2)
	 (*    | Minus(p1,p2) -> Poly.addition (dev_form p1) (Poly.uminus (dev_form p2))*)
    |  Popp p ->  Opp (expr_to_term p)
	 
	 
  let rec term_to_expr = function
    | Const n ->  Pconst (CamlToCoq.bigint (big_int_of_num n))
    | Zero   ->  Pconst ( Z0)
    | Var s   ->  Pvar (CamlToCoq.index (int_of_string (String.sub s 1 (String.length s - 1))))
    | Mul(p1,p2) ->  Pmult(term_to_expr p1, term_to_expr p2)
    | Add(p1,p2) ->   Pplus(term_to_expr p1, term_to_expr p2)
    | Opp p ->   Popp (term_to_expr p)
    | Pow(t,n) ->  power (term_to_expr t) (CamlToCoq.z n)
    | Sub(t1,t2) ->  Pplus (term_to_expr t1,  Popp (term_to_expr t2))
    | _ -> failwith "term_to_expr: not implemented"

  let term_to_expr e =
    let e' = term_to_expr e in
      if debug then Printf.printf "term_to_expr : %s - %s\n"  (string_of_poly (poly_of_term  e)) (string_of_poly (poly_of_term (expr_to_term e')));
      e'

end 
open M      

open List
open Utils 

let rec scale_term t = 
  match t with
    | Zero    -> unit_big_int , Zero
    | Const n ->  (denominator n) , Const (Big_int (numerator n))
    | Var n   -> unit_big_int , Var n
    | Inv _   -> failwith "scale_term : not implemented"
    | Opp t   -> let s, t = scale_term t in s, Opp t
    | Add(t1,t2) -> let s1,y1 = scale_term t1 and s2,y2 = scale_term t2 in
      let g = gcd_big_int s1 s2 in
      let s1' = div_big_int s1 g in
      let s2' = div_big_int s2 g in
      let e = mult_big_int g (mult_big_int s1' s2') in
	if (compare_big_int e unit_big_int) = 0
	then (unit_big_int, Add (y1,y2))
	else 	e, Add (Mul(Const (Big_int s2'), y1),Mul (Const (Big_int s1'), y2))
    | Sub _ -> failwith "scale term: not implemented"
    | Mul(y,z) ->       let s1,y1 = scale_term y and s2,y2 = scale_term z in
	mult_big_int s1 s2 , Mul (y1, y2)
    |  Pow(t,n) -> let s,t = scale_term t in
	 power_big_int_positive_int s  n , Pow(t,n)
    |   _ -> failwith "scale_term : not implemented"

let scale_term t =
  let (s,t') = scale_term t in
      s,t'
							      



let rec scale_certificate pos = match pos with
  | Axiom_eq i ->  unit_big_int , Axiom_eq i
  | Axiom_le i ->  unit_big_int , Axiom_le i
  | Axiom_lt i ->   unit_big_int , Axiom_lt i
  | Monoid l   -> unit_big_int , Monoid l
  | Rational_eq n ->  (denominator n) , Rational_eq (Big_int (numerator n))
  | Rational_le n ->  (denominator n) , Rational_le (Big_int (numerator n))
  | Rational_lt n ->  (denominator n) , Rational_lt (Big_int (numerator n))
  | Square t -> let s,t' =  scale_term t in 
      mult_big_int s s , Square t'
  | Eqmul (t, y) -> let s1,y1 = scale_term t and s2,y2 = scale_certificate y in
      mult_big_int s1 s2 , Eqmul (y1,y2)
  | Sum (y, z) -> let s1,y1 = scale_certificate y and s2,y2 = scale_certificate z in
      let g = gcd_big_int s1 s2 in
      let s1' = div_big_int s1 g in
      let s2' = div_big_int s2 g in
	mult_big_int g (mult_big_int s1' s2'), Sum (Product(Rational_le (Big_int s2'), y1),Product (Rational_le (Big_int s1'), y2))
  | Product (y, z) -> 
      let s1,y1 = scale_certificate y and s2,y2 = scale_certificate z in
	mult_big_int s1 s2 , Product (y1,y2)




let is_eq = function  Equal -> true | _ -> false
let is_le = function  NonStrict -> true | _ -> false
let is_lt = function  Strict -> true | _ -> false

let get_index_of_ith_match f i l  =
  let rec get j res l =
      match l with
	| [] -> failwith "bad index"
	| e::l -> if f e
	  then 
	    (if j = i then res else get (j+1) (res+1) l )
	  else get j (res+1) l in
    get 0 0 l


let  cert_of_pos eq le lt ll l pos = 
  let s,pos = (scale_certificate pos) in
    let rec _cert_of_pos = function
	Axiom_eq i -> let idx = get_index_of_ith_match is_eq i l in
	  S_In (CamlToCoq.nat idx)
      | Axiom_le i -> let idx = get_index_of_ith_match is_le i l in
	  S_In (CamlToCoq.nat idx)
      | Axiom_lt i -> let idx = get_index_of_ith_match is_lt i l in
	  S_In (CamlToCoq.nat idx)
      | Monoid l  -> S_Monoid (CamlToCoq.list CamlToCoq.nat l)
      | Rational_eq n | Rational_le n | Rational_lt n -> 
	  if compare_num n (Int 0) = 0 then S_Z else
	    S_Pos (CamlToCoq.positive_big_int (big_int_of_num  n))
      | Square t -> S_Square (term_to_expr  t)
    | Eqmul (t, y) -> S_Ideal(term_to_expr t, _cert_of_pos y)
    | Sum (y, z) -> S_Add  (_cert_of_pos y, _cert_of_pos z)
    | Product (y, z) -> S_Mult (_cert_of_pos y, _cert_of_pos z) in
    s, simplify_cone (_cert_of_pos pos)


let  term_of_cert l pos = 
  let l = List.map fst' l in
  let rec _cert_of_pos = function
    | S_In i -> expr_to_term (List.nth l (CoqToCaml.nat i))
    | S_Pos p -> Const (Int (CoqToCaml.positive  p))
    | S_Z     -> Const (Int 0)
    | S_Square t -> Mul(expr_to_term t, expr_to_term t)
    | S_Monoid m -> List.fold_right (fun x m -> Mul (expr_to_term (List.nth l (CoqToCaml.nat x)),m)) (CoqToCaml.list (fun x -> x) m)  (Const (Int 1))
    | S_Ideal (t, y) -> Mul(expr_to_term t, _cert_of_pos y)
    | S_Add (y, z) -> Add  (_cert_of_pos y, _cert_of_pos z)
    | S_Mult (y, z) -> Mul (_cert_of_pos y, _cert_of_pos z) in
    (_cert_of_pos pos)



let rec canonical_sum_to_string = function
  | Micromega.Nil_monom -> "Nil_monom"
  | Micromega.Cons_monom (a,varlist ,sum) -> Printf.sprintf "Cons_monom(%i,%s)" (CoqToCaml.z a) (canonical_sum_to_string  sum)
  | Micromega.Cons_varlist(varlist, sum)  -> Printf.sprintf "Cons_varlist(_,%s)"  (canonical_sum_to_string  sum)

let print_canonical_sum m = Format.print_string (canonical_sum_to_string m)

let print_list_term l = 
  print_string "print_list_term\n";
  List.iter (fun (Micromega.Pair(e,k)) -> Printf.printf "q: %s %s ;" 
	       (string_of_poly (poly_of_term (expr_to_term e))) (match k with Equal -> "= " | Strict -> "> " | NonStrict -> ">= ")) l ;
  print_string "\n"


(*
  let real_nonlinear_prover i l = 
  try
    let eq , ineq = List.partition (fun (Micromega.Pair(_,k)) -> match k with Equal -> true | _ -> false) l in 
      if debug then print_list_term eq;
      let lt,le = List.partition (fun (Micromega.Pair(_,k)) -> match k with Strict -> true | _ -> false) ineq in 
	if debug then (print_list_term lt ; print_list_term le);
	let eq' = List.map (o expr_to_term fst') eq in
	let lt'  = List.map (o expr_to_term fst') lt in
	let le'  = List.map (o expr_to_term fst') le in
	let proof =  Sos.real_nonlinear_prover i eq' le' lt' in
	  if debug then Printf.printf "poly : %s\n" (string_of_poly (poly_of_term (term_of_pos eq' le' lt' proof))) ;
	  let s,proof' = scale_certificate proof in
	    if debug then Printf.printf "scaled poly : %s\n" (string_of_poly (poly_of_term (term_of_pos eq' le' lt' proof'))) ;
	    let cert  = snd (cert_of_pos  eq le lt l (List.map snd' l) proof') in
	      if debug then Printf.printf "cert poly : %s\n" (string_of_poly (poly_of_term (term_of_cert l cert)));
	      match Micromega.Polynomial.checker cert (CamlToCoq.list (fun x -> x) l) with
		| Micromega.True -> Some cert
		| Micromega.False -> if debug then (print_string "buggy certificate" ; flush stdout) ;None
  with 
    | Sos.TooDeep -> None
    |  x   -> if debug then (print_string (Printexc.to_string x); flush stdout)  ; None
*)


let partition_expr l = 
  let rec f i = function
    | [] -> ([],[],[])
    | Micromega.Pair(e,k)::l -> 
	let (eq,ge,neq) = f (i+1) l in
	match k with 
	  | Micromega.None -> (eq,ge,(e,Axiom_eq i)::neq)
	  | Micromega.Some Equal -> ((e,i)::eq,ge,neq)
	  | Micromega.Some NonStrict -> (eq,(e,Axiom_le i)::ge,neq)
	  | Micromega.Some Strict    -> (* e > 0 == e >= 0 /\ e <> 0 *) (eq, (e,Axiom_lt i)::ge,(e,Axiom_lt i)::neq)
  in f 0 l


let rec sets_of_list l =
  match l with
    | [] -> [[]]
    | e::l -> let s = sets_of_list l in
	s@(List.map (fun s0 -> e::s0) s) 

let  cert_of_pos  pos = 
  let s,pos = (scale_certificate pos) in
    let rec _cert_of_pos = function
	Axiom_eq i ->  S_In (CamlToCoq.nat i)
      | Axiom_le i ->  S_In (CamlToCoq.nat i)
      | Axiom_lt i ->  S_In (CamlToCoq.nat i)
      | Monoid l  -> S_Monoid (CamlToCoq.list CamlToCoq.nat l)
      | Rational_eq n | Rational_le n | Rational_lt n -> 
	  if compare_num n (Int 0) = 0 then S_Z else
	    S_Pos (CamlToCoq.positive_big_int (big_int_of_num  n))
      | Square t -> S_Square (term_to_expr  t)
      | Eqmul (t, y) -> S_Ideal(term_to_expr t, _cert_of_pos y)
      | Sum (y, z) -> S_Add  (_cert_of_pos y, _cert_of_pos z)
      | Product (y, z) -> S_Mult (_cert_of_pos y, _cert_of_pos z) in
      s, simplify_cone (_cert_of_pos pos)

(* The exploration is probably not complete - for simple cases, it works... *)
let real_nonlinear_prover d l =
  try 
    let (eq,ge,neq) = partition_expr l in

    let rec elim_const  = function
	[] ->  []
      | (x,y)::l -> let p = poly_of_term (expr_to_term x) in
	  if poly_isconst p then elim_const l else (p,y)::(elim_const l) in

    let eq = elim_const eq in
    let peq = List.map  fst eq in
      
    let pge = List.map (fun (e,psatz) -> poly_of_term (expr_to_term e), psatz)  ge in
	
    let monoids = List.map (fun m ->  (itlist (fun (p,kd) y -> 
						 let p = poly_of_term (expr_to_term p) in
						   match kd with
						 | Axiom_lt i -> poly_mul p y
						 | Axiom_eq i -> poly_mul (poly_pow p 2) y
						 |   _        -> failwith "monoids") m (poly_const num_1) , map  snd m)) (sets_of_list neq) in

    let (cert_ideal, cert_cone,monoid) = deepen_until d (fun d -> 
							   tryfind (fun m -> let (ci,cc) = 
								     real_positivnullstellensatz_general false d peq pge (poly_neg (fst m) ) in
								     (ci,cc,snd m)) monoids) 0 in
	  
    let proofs_ideal = map2 (fun q i -> Eqmul(term_of_poly q,Axiom_eq i))  cert_ideal (List.map snd eq) in

    let proofs_cone = map term_of_sos cert_cone in
	  
    let proof_ne =  
      let (neq , lt) = List.partition (function  Axiom_eq _ -> true | _ -> false ) monoid in
      let sq = match (List.map (function Axiom_eq i -> i | _ -> failwith "error") neq) with
	| []  -> Rational_lt num_1
	| l   -> Monoid l in
	itlist (fun x y -> Product(x,y)) lt sq in

    let proof = end_itlist (fun s t -> Sum(s,t)) (proof_ne :: proofs_ideal @ proofs_cone) in
	  
    let s,proof' = scale_certificate proof in
    let cert  = snd (cert_of_pos proof') in
      if debug then Printf.printf "cert poly : %s\n" (string_of_poly (poly_of_term (term_of_cert l cert)));
      match Micromega.Polynomial.checker cert (CamlToCoq.list (fun x -> x) l) with
	| Micromega.True -> Some cert
	| Micromega.False ->  (print_string "buggy certificate" ; flush stdout) ;None
  with 
    | Sos.TooDeep -> None


let pure_sos  l =
    let l = zip l (0-- (length l -1)) in
    let (lt,i) =  (List.find (fun (x,_) -> snd' x = Micromega.Some Strict) l) in
    let plt = poly_neg (poly_of_term (expr_to_term (fst' lt))) in
    let (n,polys) = sumofsquares plt in (* n * (ci * pi^2) *)
    let pos = Product (Rational_lt n, itlist (fun (c,p) rst -> Sum (Product (Rational_lt c, Square (term_of_poly p)), rst)) polys (Rational_lt num_0)) in
    let proof = Sum(Axiom_lt i, pos) in
    let s,proof' = scale_certificate proof in
    let cert  = snd (cert_of_pos proof') in
      Some cert

(* zprover.... *)

(* I need to gather the set of variables --->
   Then go for fold 
   Une fois que j'ai un interval -> je dois trouver un certificat => 2 autres fouriers
*)

let make_linear_system l =
  let l' = List.map fst l in
  let monomials = List.fold_left (fun acc p -> Poly.addition p acc) (Poly.constant zero_big_int) l' in
  let monomials = Poly.fold (fun mn _ l -> if mn = Monomial.const then l else mn::l) monomials [] in
    (List.map (fun (c,op) -> {coeffs = (List.map (fun mn -> Big_int (Poly.get mn c)) monomials) ; op = op ; cst = minus_num (Big_int (Poly.get Monomial.const c))}) l,monomials)


open Interval 
let pplus x y = Micromega.Pplus(x,y)
let pmult x y = Micromega.Pmult(x,y)
let pconst x = Micromega.Pconst x
let popp x = Micromega.Popp x

let zlinear_prover l =
  (* get rid of  <> and relax > *)
  let ll = List.fold_right (fun (Micromega.Pair(e,k)) r -> match k with 
			       Micromega.None -> r  
			     | Micromega.Some k -> (dev_form e , match k with
					    | Strict | NonStrict -> Ge (* Loss of precision -- weakness of fourier*)
					    | Equal              -> Eq) :: r) l [] in
  let (sys,var) = make_linear_system ll in
    match find_Q_interval sys with
      | None -> None
      | Some (Itv(Bd lb, Bd ub),i) -> (* lb <= x <= ub *)
	  if debug then (Printf.printf "[%s;%s]" (string_of_num lb) (string_of_num ub); flush stdout);
	  let var = monomial_to_polynomial (List.nth var i)  in 
	  let (lbn,lbd) = (CamlToCoq.bigint (numerator lb) , CamlToCoq.bigint (denominator lb)) in
	    let (ubn,ubd) = (CamlToCoq.bigint (numerator ub) , CamlToCoq.bigint (denominator ub)) in
	      (match 
		 (*x <= ub ->  x  > ub *)
		 linear_prover (Micromega.Pair( pplus  (pmult (pconst ubd) var)  (popp (pconst ubn)) , Micromega.Some Strict) :: l) ,
		 (* lb <= x  -> lb > x *)
		     linear_prover (Micromega.Pair( pplus  (popp (pmult  (pconst lbd) var)) (pconst lbn) , Micromega.Some Strict)::l) with
		   | Some cub , Some clb  ->   Some (var,ub,cub,lb,clb)
		   | _ -> None
	      )
      |  _ -> None


