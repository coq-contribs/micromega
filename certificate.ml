(** Header **)(* We take as input a list of polynomials [p1...pn] and return an unfeasibility certificate polynomial. *)
(*open Micromega.Polynomial*)
open Big_int
open Num

module Mc = Micromega
module Ml2C = Utils.CamlToCoq
module C2Ml = Utils.CoqToCaml

let (<+>) = add_num
let (<->) = minus_num
let (<*>) = mult_num

type var = Mc.positive

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
  if v = 1 then Printf.fprintf o "x%i." (C2Ml.index k)
  else     Printf.fprintf o "x%i^%i." (C2Ml.index k) v) m

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
 val get : Monomial.t -> t -> num
 val variable : var -> t
 val add : Monomial.t -> num -> t -> t
 val constant : num -> t
 val mult : Monomial.t -> num -> t -> t
 val product : t -> t -> t
 val addition : t -> t -> t
 val uminus : t -> t
 val fold : (Monomial.t -> num -> 'a -> 'a) -> t -> 'a -> 'a
 val pp : out_channel -> t -> unit
 val compare : t -> t -> int
end =
struct
 (*normalisation bug : 0*x ... *)
 module P = Map.Make(Monomial)
 open P

 type t = num P.t

 let pp o p = P.iter (fun k v -> 
  if compare_num v (Int 0) <> 0
  then 
   if Monomial.compare Monomial.const k = 0
   then 	Printf.fprintf o "%s " (string_of_num v)
   else Printf.fprintf o "%s*%a " (string_of_num v) Monomial.pp k) p  

 (* Get the coefficient of monomial mn *)
 let get : Monomial.t -> t -> num = 
  fun mn p -> try find mn p with Not_found -> (Int 0)


 (* The polynomial 1.x *)
 let variable : var -> t =
  fun  x ->  add (Monomial.var x) (Int 1) empty
   



 (*The constant polynomial *)
 let constant : num -> t =
  fun c -> add (Monomial.const) c empty

 (* The addition of a monomial *)

 let add : Monomial.t -> num -> t -> t =
  fun mn v p -> 
   let vl = (get mn p) <+> v in
    add mn vl p

 (* This code (which corrects a normalisation bug) breaks build_linear_system (see the HINT comment...) 
    
    let add : Monomial.t -> num -> t -> t =
    fun mn v p -> 
    let vl = (get mn p) <+> v in
    if compare_num vl zero_num <> 0
    then add mn vl p
    else 
    let rm = remove mn p in
    if is_empty rm 
    then constant zero_num (* Why not empty *)
    else rm
 *)


 (** Design choice: empty is not a polynomial 
     I do not remember why .... 
 **)

 (* The product by a monomial *)
 let mult : Monomial.t -> num -> t -> t =
  fun mn v p -> fold (fun mn' v' res -> P.add (Monomial.prod mn mn') (v<*>v') res) p empty

 (*  let mult mn v p = 
     let res = mult mn v p in
     Printf.printf "mult : %s*%a * %a = %a\n" (string_of_num v) Monomial.pp mn pp p pp res;
     res *)
   
 let  addition : t -> t -> t =
  fun p1 p2 -> fold (fun mn v p -> add mn v p) p1 p2


 let product : t -> t -> t =
  fun p1 p2 -> 
   fold (fun mn v res -> addition (mult mn v p2) res ) p1 empty


 let uminus : t -> t =
  fun p -> map (fun v -> minus_num v) p

 let fold = P.fold

 let compare = compare compare_num
end

open Utils
type 'a number_spec = {
 bigint_to_number : big_int -> 'a;
 number_to_num : 'a  -> num;
 zero : 'a;
 unit : 'a;
 mult : 'a -> 'a -> 'a;
 eqb  : 'a -> 'a -> Mc.bool
}

let z_spec = {
 bigint_to_number = Ml2C.bigint ;
 number_to_num = (fun x -> Big_int (C2Ml.z_big_int x));
 zero = Mc.Z0;
 unit = Mc.Zpos Mc.XH;
 mult = Mc.zmult;
 eqb  = Mc.zeq_bool
}


 (*let num_to_q num = {Mc.qnum = Ml2C.bigint (numerator num) ; Mc.qden = Ml2C.positive_big_int (denominator num) }*)

let q_spec = {
 bigint_to_number = (fun x -> {Mc.qnum = Ml2C.bigint x; Mc.qden = Mc.XH});
 number_to_num = C2Ml.q_to_num;
 zero = {Mc.qnum = Mc.Z0;Mc.qden = Mc.XH};
 unit = {Mc.qnum =  (Mc.Zpos Mc.XH) ; Mc.qden = Mc.XH};
 mult = Mc.qmult;
 eqb  = Mc.qeq_bool
}

let r_spec = z_spec




let dev_form n_spec  p =
 let rec dev_form p = 
  match p with
   | Mc.PEc z ->  Poly.constant (n_spec.number_to_num z)
   | Mc.PEX v ->  Poly.variable v
   | Mc.PEmul(p1,p2) -> 
      let p1 = dev_form p1 in
      let p2 = dev_form p2 in
      let res = Poly.product p1 p2 in
      (*	Printf.fprintf stdout "%a * %a = %a\n" Poly.pp p1 Poly.pp p2 Poly.pp res ;*)
       res
   | Mc.PEadd(p1,p2) -> Poly.addition (dev_form p1) (dev_form p2)
      (*    | Minus(p1,p2) -> Poly.addition (dev_form p1) (Poly.uminus (dev_form p2))*)
   | Mc.PEopp p ->  Poly.uminus (dev_form p)
   | Mc.PEsub(p1,p2) ->  Poly.addition (dev_form p1) (Poly.uminus (dev_form p2))
   | Mc.PEpow(p,n)   ->  
      let p = dev_form p in
      let n = C2Ml.n n in
      let rec pow n = if n = 0 then Poly.constant (n_spec.number_to_num n_spec.unit)
       else Poly.product p (pow (n-1)) in
       pow n in
  dev_form p


let monomial_to_polynomial mn = 
 Monomial.fold 
  (fun v i acc -> 
   let mn = if i = 1 then Mc.PEX v else Mc.PEpow (Mc.PEX v ,Ml2C.n i) in
    if acc = Mc.PEc (Mc.Zpos Mc.XH)
    then mn 
    else Mc.PEmul(mn,acc))
  mn 
  (Mc.PEc (Mc.Zpos Mc.XH))
  
let list_to_polynomial vars l = 
 assert (List.for_all (fun x -> ceiling_num x =/ x) l);
 let var x = monomial_to_polynomial (List.nth vars x)  in 
 let rec xtopoly p i = function
  | [] -> p
  | c::l -> if c =/  (Int 0) then xtopoly p (i+1) l 
    else let c = Mc.PEc (Ml2C.bigint (numerator c)) in
    let mn = 
     if c =  Mc.PEc (Mc.Zpos Mc.XH)
     then var i
     else Mc.PEmul (c,var i) in
    let p' = if p = Mc.PEc Mc.Z0 then mn else
      Mc.PEadd (mn, p) in
     xtopoly p' (i+1) l in
  
  xtopoly (Mc.PEc Mc.Z0) 0 l

let rec fixpoint f x =
 let y' = f x in
  if y' = x then y'
  else fixpoint f y'








let  rec_simpl_cone n_spec e = 
 let simpl_cone = Mc.simpl_cone n_spec.zero n_spec.unit n_spec.mult n_spec.eqb in
 let rec rec_simpl_cone  = function
 | Mc.S_Mult(t1, t2) -> simpl_cone  (Mc.S_Mult (rec_simpl_cone t1, rec_simpl_cone t2))
 | Mc.S_Add(t1,t2)  -> simpl_cone (Mc.S_Add (rec_simpl_cone t1, rec_simpl_cone t2))
 |  x           -> simpl_cone x in
  rec_simpl_cone e


let simplify_cone n_spec c = fixpoint (rec_simpl_cone n_spec) c

type cone_prod = Const of cone | Ideal of cone *cone | Mult of cone * cone | Other of cone
and cone =   Mc.zWitness



let factorise_linear_cone c =

 let rec cone_list  c l = 
  match c with
   | Mc.S_Add (x,r) -> cone_list  r (x::l)
   |  _        ->  c :: l in

 let factorise c1 c2 =
  match c1 , c2 with
   | Mc.S_Ideal(x,y) , Mc.S_Ideal(x',y') -> if x = x' then Some (Mc.S_Ideal(x, Mc.S_Add(y,y'))) else None
   | Mc.S_Mult(x,y) , Mc.S_Mult(x',y') -> if x = x' then Some (Mc.S_Mult(x, Mc.S_Add(y,y'))) else None
   |  _     -> None in

 let rec rebuild_cone l pending  =
  match l with
   | [] -> (match pending with
      | None -> Mc.S_Z
      | Some p -> p
     )
   | e::l -> 
      (match pending with
       | None -> rebuild_cone l (Some e) 
       | Some p -> (match factorise p e with
	  | None -> Mc.S_Add(p, rebuild_cone l (Some e))
	  | Some f -> rebuild_cone l (Some f) )
      ) in

  (rebuild_cone (List.sort Pervasives.compare (cone_list c [])) None)



(* The binding with Fourier might be a bit obsolete -- how does it handle equalities ? *)

(* Certificates are elements of the cone such that P = 0  *)

(* To begin with, we search for certificates of the form:
   a1.p1 + ... an.pn + b1.q1 +... + bn.qn + c = 0   
   where pi >= 0 qi > 0
   ai >= 0 
   bi >= 0
   Sum bi + c >= 1
   This is a linear problem: each monomial is considered as a variable.
   Hence, we can use fourier.

   The variable c is at index 0
*)

open Mfourier
   (*module Fourier = Fourier(Vector.VList)(SysSet(Vector.VList))*)
   (*module Fourier = Fourier(Vector.VSparse)(SysSetAlt(Vector.VSparse))*)
module Fourier = Fourier(Vector.VSparse)(*(SysSetAlt(Vector.VMap))*)

module Vect = Fourier.Vect
open Fourier.Cstr

(* fold_left followed by a rev ! *)

let constrain_monomial mn l  = 
 let coeffs = List.fold_left (fun acc p -> (Poly.get mn p)::acc) [] l in
  if mn = Monomial.const
  then  
   { coeffs = Vect.from_list ((Big_int unit_big_int):: (List.rev coeffs)) ; op = Eq ; cst = Big_int zero_big_int  }
  else
   { coeffs = Vect.from_list ((Big_int zero_big_int):: (List.rev coeffs)) ; op = Eq ; cst = Big_int zero_big_int  }

    
let positivity l = 
 let rec xpositivity i l = 
  match l with
   | [] -> []
   | (_,Mc.Equal)::l -> xpositivity (i+1) l
   | (_,_)::l -> {coeffs = Vect.update (i+1) (fun _ -> Int 1) Vect.null ; op = Ge ; cst = Int 0 }  :: (xpositivity (i+1) l)
 in
  xpositivity 0 l


let string_of_op = function
 | Mc.Strict -> "> 0" 
 | Mc.NonStrict -> ">= 0" 
 | Mc.Equal -> "= 0"
 | Mc.NonEqual -> "<> 0"



(* If the certificate includes at least one strict inequality, the obtained polynomial can also be 0 *)
let build_linear_system l =
 (* List.iter (fun (p,c) -> Printf.printf "%a %s\n" Poly.pp p (string_of_op c)) l ;
    flush stdout; *)

 (* Gather the monomials:  HINT add up of the polynomials *)
 let l' = List.map fst l in
 let monomials = List.fold_left (fun acc p -> Poly.addition p acc) (Poly.constant (Int 0)) l' in
  (* For each monomial, compute a constraint *)
 let s0 = Poly.fold (fun mn _ res -> (constrain_monomial mn l')::res) monomials [] in
  (* I need at least something strictly positive *)
 let strict = {coeffs = Vect.from_list ((Big_int unit_big_int)::(List.map (fun (x,y) -> match y with Mc.Strict -> Big_int unit_big_int | _ -> Big_int zero_big_int) l));
	       op = Ge ; cst = Big_int unit_big_int } in
  (* Add the positivity constraint *)
  {coeffs = Vect.from_list ([Big_int unit_big_int]) ; op = Ge ; cst = Big_int zero_big_int}::(strict::(positivity l)@s0)


let big_int_to_z = Ml2C.bigint




(* For Q, this is a pity that the certificate has been scaled -- at a lower layer, certificates are using nums... *)
let make_certificate n_spec cert li = 
 let big_int_to_constant = n_spec.bigint_to_number in
 match cert with
  | [] -> None
  | e::cert' -> 
     let cst = match compare_big_int e zero_big_int with
      | 0 -> Mc.S_Z
      | 1 ->  Mc.S_Pos (big_int_to_constant e) 
      | _ -> failwith "positivity error" 
     in
     let rec scalar_product cert l =
      match cert with
       | [] -> Mc.S_Z
       | c::cert -> match l with
	  | [] -> failwith "make_certificate(1)"
	  | i::l ->  let r = scalar_product cert l in
		      match compare_big_int c  zero_big_int with
		       | -1 -> Mc.S_Add (Mc.S_Ideal (Mc.PEc ( big_int_to_constant c), Mc.S_In (Ml2C.nat i)), r)
		       | 0  -> r
		       | _ ->  Mc.S_Add (Mc.S_Mult (Mc.S_Pos (big_int_to_constant c), Mc.S_In (Ml2C.nat i)),r) in

      Some ((factorise_linear_cone (simplify_cone n_spec (Mc.S_Add (cst, scalar_product cert' li)))))


exception Found of Monomial.t

let raw_certificate l = 
 let sys = build_linear_system l in
  try 
   match Fourier.find_point sys with
    | None -> None
    | Some cert ->  Some (rats_to_ints (Vect.to_list cert)) (* should not use rats_to_ints *)
  with x -> (if debug then Printf.printf "raw certificate %s" (Printexc.to_string x);   flush stdout ;None)

(*let raw_certificate l = 
  print_string "<" ; flush stdout ; 
  let res = raw_certificate l  in 
  print_string ">" ; flush stdout  ; res
*)

let simple_linear_prover to_constant l =
 let (lc,li) = List.split l in
  match raw_certificate lc with
   |  None -> None (* No certificate *)
   | Some cert -> make_certificate to_constant cert li
      
(* linear_prover is able to deal with <> operators - case split...
   There is no explosion: over the rationals, disequlities cannot collaborate... 
   In the current implem, disequalities are wiped out by the cnf conversion....

let linear_prover n_spec l  =
 let li = List.combine l (Sos.(--) 0 (List.length l -1)) in
 let (l1,l') = List.partition (fun (x,_) -> if snd' x = Mc.NonEqual then true else false) li in
 let l' = List.map (fun (c,i) -> let (Mc.Pair(x,y)) = c in 
				  match y with Mc.NonEqual -> failwith "cannot happen" |  y -> ((dev_form n_spec.number_to_num x, y),i)) l' in
  
  match simple_linear_prover n_spec l' with
   | Some cert -> Some cert (* diff are useless *) 
   | None  -> 
      (let (lc,li) = List.split l' in
      let rec find_cert = function
       | [] -> None
       | e::l -> let (Mc.Pair(c,_),i) = e in
	 let p = dev_form n_spec.number_to_num c in
	 let cone_of_big_int e = 
	  match compare_big_int e zero_big_int with
	   | 1 -> Mc.S_Pos (Ml2C.bigint e) 
	   | _ -> failwith "cone_of_big_int"
	 in
	  match raw_certificate ((p,Mc.Strict)::lc) , raw_certificate ((Poly.uminus p,Mc.Strict)::lc) with
	   | Some (cst::cdiff::c), Some (cst'::diff'::c') -> 
	      let mono = Mc.S_Mult(Mc.S_Mult (cone_of_big_int cdiff, cone_of_big_int diff'),
				  (Mc.S_Monoid (Ml2C.list Ml2C.nat [i]))) in
	       (match make_certificate n_spec (cst::c) li , make_certificate n_spec (cst'::c') li with
		|    Some c1 , Some c2 -> Some (simplify_cone n_spec (Mc.S_Add(mono, Mc.S_Mult(c1 , c2))))
		|   _ -> None)
	   |  _  -> find_cert l in
       find_cert l1)
*)


let linear_prover n_spec l  =
 let li = List.combine l (Sos.(--) 0 (List.length l -1)) in
 let (l1,l') = List.partition (fun (x,_) -> if snd' x = Mc.NonEqual then true else false) li in
 let l' = List.map (fun (c,i) -> let (Mc.Pair(x,y)) = c in 
				  match y with Mc.NonEqual -> failwith "cannot happen" |  y -> ((dev_form n_spec x, y),i)) l' in
  
  simple_linear_prover n_spec l' 


let linear_prover n_spec l  =
 try linear_prover n_spec l with
   x -> (print_string (Printexc.to_string x); None)

open Sos
module M =
struct
 open Mc

 let rec expr_to_term = function
  |  PEc z ->  Const  (Big_int (C2Ml.z_big_int z))
  |  PEX v ->  Var ("x"^(string_of_int (C2Ml.index v)))
  |  PEmul(p1,p2) -> 
      let p1 = expr_to_term p1 in
      let p2 = expr_to_term p2 in
      let res = Mul(p1,p2) in 	   res
			    (*	Printf.fprintf stdout "%a * %a = %a\n" Poly.pp p1 Poly.pp p2 Poly.pp res ;*)

  | PEadd(p1,p2) -> Add(expr_to_term p1, expr_to_term p2)
  | PEsub(p1,p2) -> Sub(expr_to_term p1, expr_to_term p2)
  | PEpow(p,n)   -> Pow(expr_to_term p , C2Ml.n n)
     (*    | Minus(p1,p2) -> Poly.addition (dev_form p1) (Poly.uminus (dev_form p2))*)
  |  PEopp p ->  Opp (expr_to_term p)

      
 let rec term_to_expr = function
  | Const n ->  PEc (Ml2C.bigint (big_int_of_num n))
  | Zero   ->  PEc ( Z0)
  | Var s   ->  PEX (Ml2C.index (int_of_string (String.sub s 1 (String.length s - 1))))
  | Mul(p1,p2) ->  PEmul(term_to_expr p1, term_to_expr p2)
  | Add(p1,p2) ->   PEadd(term_to_expr p1, term_to_expr p2)
  | Opp p ->   PEopp (term_to_expr p)
  | Pow(t,n) ->  PEpow (term_to_expr t,Ml2C.n n)
  | Sub(t1,t2) ->  PEsub (term_to_expr t1,  term_to_expr t2)
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




let is_eq = function  Mc.Equal -> true | _ -> false
let is_le = function  Mc.NonStrict -> true | _ -> false
let is_lt = function  Mc.Strict -> true | _ -> false

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
		  Mc.S_In (Ml2C.nat idx)
  | Axiom_le i -> let idx = get_index_of_ith_match is_le i l in
		   Mc.S_In (Ml2C.nat idx)
  | Axiom_lt i -> let idx = get_index_of_ith_match is_lt i l in
		   Mc.S_In (Ml2C.nat idx)
  | Monoid l  -> Mc.S_Monoid (Ml2C.list Ml2C.nat l)
  | Rational_eq n | Rational_le n | Rational_lt n -> 
     if compare_num n (Int 0) = 0 then Mc.S_Z else
      Mc.S_Pos (Ml2C.bigint (big_int_of_num  n))
  | Square t -> Mc.S_Square (term_to_expr  t)
  | Eqmul (t, y) -> Mc.S_Ideal(term_to_expr t, _cert_of_pos y)
  | Sum (y, z) -> Mc.S_Add  (_cert_of_pos y, _cert_of_pos z)
  | Product (y, z) -> Mc.S_Mult (_cert_of_pos y, _cert_of_pos z) in
  s, simplify_cone z_spec (_cert_of_pos pos)


let  term_of_cert l pos = 
 let l = List.map fst' l in
 let rec _cert_of_pos = function
  | Mc.S_In i -> expr_to_term (List.nth l (C2Ml.nat i))
  | Mc.S_Pos p -> Const (C2Ml.num  p)
  | Mc.S_Z     -> Const (Int 0)
  | Mc.S_Square t -> Mul(expr_to_term t, expr_to_term t)
  | Mc.S_Monoid m -> List.fold_right (fun x m -> Mul (expr_to_term (List.nth l (C2Ml.nat x)),m)) (C2Ml.list (fun x -> x) m)  (Const (Int 1))
  | Mc.S_Ideal (t, y) -> Mul(expr_to_term t, _cert_of_pos y)
  | Mc.S_Add (y, z) -> Add  (_cert_of_pos y, _cert_of_pos z)
  | Mc.S_Mult (y, z) -> Mul (_cert_of_pos y, _cert_of_pos z) in
  (_cert_of_pos pos)



let rec canonical_sum_to_string = function s -> failwith "not implemented"
 (*  | Mc.Nil_monom -> "Nil_monom"
     | Mc.Cons_monom (a,varlist ,sum) -> Printf.sprintf "Cons_monom(%i,%s)" (C2Ml.z a) (canonical_sum_to_string  sum)
     | Mc.Cons_varlist(varlist, sum)  -> Printf.sprintf "Cons_varlist(_,%s)"  (canonical_sum_to_string  sum)
 *)
let print_canonical_sum m = Format.print_string (canonical_sum_to_string m)

let print_list_term l = 
 print_string "print_list_term\n";
 List.iter (fun (Mc.Pair(e,k)) -> Printf.printf "q: %s %s ;" 
  (string_of_poly (poly_of_term (expr_to_term e))) (match k with Mc.Equal -> "= " | Mc.Strict -> "> " | Mc.NonStrict -> ">= " | _ -> failwith "not_implemented")) l ;
 print_string "\n"


(*
  let real_nonlinear_prover i l = 
  try
  let eq , ineq = List.partition (fun (Mc.Pair(_,k)) -> match k with Equal -> true | _ -> false) l in 
  if debug then print_list_term eq;
  let lt,le = List.partition (fun (Mc.Pair(_,k)) -> match k with Strict -> true | _ -> false) ineq in 
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
  match Mc.Polynomial.checker cert (Ml2C.list (fun x -> x) l) with
  | Mc.True -> Some cert
  | Mc.False -> if debug then (print_string "buggy certificate" ; flush stdout) ;None
  with 
  | Sos.TooDeep -> None
  |  x   -> if debug then (print_string (Printexc.to_string x); flush stdout)  ; None
*)


let partition_expr l = 
 let rec f i = function
  | [] -> ([],[],[])
  | Mc.Pair(e,k)::l -> 
     let (eq,ge,neq) = f (i+1) l in
      match k with 
       | Mc.Equal -> ((e,i)::eq,ge,neq)
       | Mc.NonStrict -> (eq,(e,Axiom_le i)::ge,neq)
       | Mc.Strict    -> (* e > 0 == e >= 0 /\ e <> 0 *) (eq, (e,Axiom_lt i)::ge,(e,Axiom_lt i)::neq)
       | Mc.NonEqual -> (eq,ge,(e,Axiom_eq i)::neq) (* Not quite sure -- Coq interface has changed *)
	  

 in f 0 l


let rec sets_of_list l =
 match l with
  | [] -> [[]]
  | e::l -> let s = sets_of_list l in
	     s@(List.map (fun s0 -> e::s0) s) 

let  cert_of_pos  pos = 
 let s,pos = (scale_certificate pos) in
 let rec _cert_of_pos = function
   Axiom_eq i ->  Mc.S_In (Ml2C.nat i)
  | Axiom_le i ->  Mc.S_In (Ml2C.nat i)
  | Axiom_lt i ->  Mc.S_In (Ml2C.nat i)
  | Monoid l  -> Mc.S_Monoid (Ml2C.list Ml2C.nat l)
  | Rational_eq n | Rational_le n | Rational_lt n -> 
     if compare_num n (Int 0) = 0 then Mc.S_Z else
      Mc.S_Pos (Ml2C.bigint (big_int_of_num  n))
  | Square t -> Mc.S_Square (term_to_expr  t)
  | Eqmul (t, y) -> Mc.S_Ideal(term_to_expr t, _cert_of_pos y)
  | Sum (y, z) -> Mc.S_Add  (_cert_of_pos y, _cert_of_pos z)
  | Product (y, z) -> Mc.S_Mult (_cert_of_pos y, _cert_of_pos z) in
  s, simplify_cone z_spec (_cert_of_pos pos)

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
   match Mc.zWeakChecker (Ml2C.list (fun x -> x) l)  cert with
    | Mc.True -> Some cert
    | Mc.False ->  (print_string "buggy certificate" ; flush stdout) ;None
 with 
  | Sos.TooDeep -> None


(* This is somewhat buggy, over Z, strict inequality vanish... *)
let pure_sos  l =
 (* If there is no strict inequality, I should nonetheless be able to try something - over Z  > is equivalent to -1  >= *)
 try 
  let l = zip l (0-- (length l -1)) in
  let (lt,i) =  try (List.find (fun (x,_) -> snd' x =  Mc.Strict) l) with Not_found -> List.hd l in
  let plt = poly_neg (poly_of_term (expr_to_term (fst' lt))) in
  let (n,polys) = sumofsquares plt in (* n * (ci * pi^2) *)
  let pos = Product (Rational_lt n, itlist (fun (c,p) rst -> Sum (Product (Rational_lt c, Square (term_of_poly p)), rst)) polys (Rational_lt num_0)) in
  let proof = Sum(Axiom_lt i, pos) in
  let s,proof' = scale_certificate proof in
  let cert  = snd (cert_of_pos proof') in
   Some cert
 with
  | Not_found -> (* This is no strict inequality *) None
  |  x        -> None


(* zprover.... *)

(* I need to gather the set of variables --->
   Then go for fold 
   Once I have an interval, I need a certificate : 2 other fourier elims.
   (I could probably get the certificate directly as it is done in the fourier contrib.)
*)

let make_linear_system l =
 let l' = List.map fst l in
 let monomials = List.fold_left (fun acc p -> Poly.addition p acc) (Poly.constant (Int 0)) l' in
 let monomials = Poly.fold (fun mn _ l -> if mn = Monomial.const then l else mn::l) monomials [] in
  (List.map (fun (c,op) -> {coeffs =
    Vect.from_list (List.map (fun mn ->  (Poly.get mn c)) monomials) ; 
			    op = op ; cst = minus_num ( (Poly.get Monomial.const c))}) l,monomials)


open Interval 
let pplus x y = Mc.PEadd(x,y)
let pmult x y = Mc.PEmul(x,y)
let pconst x = Mc.PEc x
let popp x = Mc.PEopp x

let debug = false
 
(* keep track of enumerated vectors *)
let rec mem p x  l = match l with [] -> false | e::l -> if p x e then true else mem p x l
let rec remove_assoc p x l = match l with [] -> [] | e::l -> if p x (fst e) then remove_assoc p x l else e::(remove_assoc p x l)

let eq x y = Vect.compare x y = 0

(* Beurk... this code is a shame *)

let rec zlinear_prover sys = xzlinear_prover [] sys

and xzlinear_prover enum l :  (Mc.proofTerm option) = 
 match linear_prover z_spec l with
  | Some prf ->  Some (Mc.RatProof prf)
  | None     ->  
     let ll = List.fold_right (fun (Mc.Pair(e,k)) r -> match k with 
       Mc.NonEqual -> r  
      | k -> (dev_form z_spec e , 
	     match k with
	      | Mc.Strict | Mc.NonStrict -> Ge (* Loss of precision -- weakness of fourier*)
	      | Mc.Equal              -> Eq
	      | Mc.NonEqual -> failwith "Cannot happen") :: r) l [] in

     let (sys,var) = make_linear_system ll in
     let res = 
      match Fourier.find_Q_interval sys with
       | Some(i,x,j) -> if i =/ j then Some(i,Vect.set x (Int 1) Vect.null,i) else None 
       | None -> None in
     let res = match res with
      | None ->
	 begin
	  let candidates = List.fold_right 
	   (fun cstr acc -> 
	    let gcd = Big_int (Vect.gcd cstr.coeffs) in
	    let vect = Vect.mul (Int 1 // gcd) cstr.coeffs in
	     if mem eq vect enum then acc
	     else ((vect,Fourier.optimise vect sys)::acc)) sys [] in
	  let candidates = List.fold_left (fun l (x,i) -> match i with None -> (x,Empty)::l | Some i ->  (x,i)::l) [] (candidates) in
	   match List.fold_left (fun (x1,i1) (x2,i2) -> if smaller_itv i1 i2 then (x1,i1) else (x2,i2)) (Vect.null,Itv(None,None)) candidates with
	    | (i,Empty) -> None
	    | (x,Itv(Some i, Some j))  -> Some(i,x,j)
	    | (x,Point n) ->  Some(n,x,n)
	    |   x        ->   match Fourier.find_Q_interval sys with
		 | None -> None
		 | Some(i,x,j) -> if i =/ j then Some(i,Vect.set x (Int 1) Vect.null,i) else None 
	 end
      |   _ -> res in

      match res with 
       | Some (lb,e,ub) -> 
	  let (lbn,lbd) = (Ml2C.bigint (sub_big_int (numerator lb) unit_big_int), Ml2C.bigint (denominator lb)) in
	  let (ubn,ubd) = (Ml2C.bigint (add_big_int unit_big_int (numerator ub)) , Ml2C.bigint (denominator ub)) in
	  let expr = list_to_polynomial var (Vect.to_list e) in
	   (match 
	     (*x <= ub ->  x  > ub *)
	     linear_prover z_spec (Mc.Pair( pplus  (pmult (pconst ubd) expr)  (popp (pconst  ubn)) ,  Mc.NonStrict) :: l) ,
	    (* lb <= x  -> lb > x *)
	    linear_prover z_spec (Mc.Pair( pplus  (popp (pmult  (pconst lbd) expr)) (pconst lbn) ,  Mc.NonStrict)::l) with
	     | Some cub , Some clb  ->   
		(match zlinear_enum (e::enum)   expr (ceiling_num lb)  (floor_num ub) l with
		 | None -> None
		 | Some prf -> Some (Mc.EnumProof(Ml2C.q lb,expr,Ml2C.q ub,clb,cub,prf)))
	     | _ -> None
	   )
       |  _ -> None
and xzlinear_enum enum expr clb cub l = 
 if clb >/  cub
 then Some Mc.Nil
 else 
  let pexpr = pplus (popp (pconst (Ml2C.bigint (numerator clb)))) expr in
  let sys' = (Mc.Pair(pexpr, Mc.Equal))::l in
   match xzlinear_prover enum sys' with
    | None -> if debug then print_string "zlp?"; None
    | Some prf -> if debug then print_string "zlp!";
    match zlinear_enum enum expr (clb +/ (Int 1)) cub l with
     | None -> None
     | Some prfl -> Some (Mc.Cons(prf,prfl))

and zlinear_enum enum expr clb cub l = 
 let res = xzlinear_enum enum expr clb cub l in
  if debug then Printf.printf "zlinear_enum %s %s -> %s\n" 
   (string_of_num clb) 
   (string_of_num cub) 
   (match res with
    | None -> "None"
    | Some r -> "Some") ; res

