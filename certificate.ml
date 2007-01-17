(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
(* We take as input a list of polynomials [p1...pn] and return an unfeasibility certificate polynomial.
*)
open Micromega.M
open Big_int
open Num

let (<+>) = add_big_int
let (<->) = minus_big_int
let (<*>) = mult_big_int

type var = coq_Var


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


let power_pos (p:Micromega.positive) (pol:Poly.t) : Poly.t =
  Micromega.iter_pos p  (Poly.product pol)  (Poly.constant unit_big_int)

let rec power z pol = 
  match z with
    | Micromega.Z0 -> Poly.constant unit_big_int
    | Micromega.Zneg _ -> Poly.constant zero_big_int
    | Micromega.Zpos p -> power_pos p pol



let rec dev_form p =
  match p with
    | C z ->  Poly.constant (CoqToCaml.z_big_int z)
    | V v ->  Poly.variable v
    | Mult(p1,p2) -> 
	let p1 = dev_form p1 in
	let p2 = dev_form p2 in
	let res = Poly.product p1 p2 in
(*	Printf.fprintf stdout "%a * %a = %a\n" Poly.pp p1 Poly.pp p2 Poly.pp res ;*)
	res
    | Add(p1,p2) -> Poly.addition (dev_form p1) (dev_form p2)
    | Minus(p1,p2) -> Poly.addition (dev_form p1) (Poly.uminus (dev_form p2))
    | UMinus p ->  Poly.uminus (dev_form p)
    | Power(p,n) -> 
	let p = dev_form p in
	power n p

(* Certificates are elements of the cone such that P <= -1  *)

(* To begin with, we search for certificates of the form:
   a1.p1 + ... an.pn <= -1    ai >= 0
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
   /_ l(cst) <= -1  == 
   _ 
   \
   /_  - l(cst) >= 1 


*)

let rec constrain_monomial mn l = 
  if mn = Monomial.const
  then  
    let coeffs = List.fold_left (fun acc p -> (minus_num (Big_int (Poly.get mn p)))::acc) [] l  in
    { coeffs = List.rev coeffs ; op = Ge ; cst = Big_int unit_big_int }
  else
    let coeffs = List.fold_left (fun acc p -> Big_int (Poly.get mn p)::acc) [] l in
    {coeffs = List.rev coeffs ; op = Eq ; cst = Big_int zero_big_int}


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



let positivity l = 
  List.map (fun l -> {coeffs = l ; op = Ge ; cst = Big_int zero_big_int}) (id_matrix (List.length l))


(* Each expr E  represents a polynomial constraint E >= 0 *)
let build_linear_system l =
  (* Gather the monomials  HINT add up of the polynomials *)
  let monomials = List.fold_left (fun acc p -> Poly.addition p acc) (Poly.constant zero_big_int) l in
  (* For each monomial, compute a constraint *)
  let s0 = Poly.fold (fun mn _ res -> (constrain_monomial mn l)::res) monomials [] in
  (* Add the positivity constraint *)
  ((positivity l)@s0)

(* Keep the positivity constraint implicit *)
(*let build_linear_system l =
  (* Gather the monomials  HINT add up of the polynomials *)
  let monomials = List.fold_left (fun acc p -> Poly.addition p acc) (Poly.constant zero_big_int) l in
  (* For each monomial, compute a constraint *)
  let s0 = Poly.fold (fun mn _ res -> (constrain_monomial mn l)::res) monomials [] in
  (* Add the positivity constraint *)
    s0
    (*  ((positivity l)@s0)*)
*)


open Micromega.M


let certificate l =
  (* Developp the polynomials *)
  let l = List.map dev_form l in
(*  List.iter (fun x -> Poly.pp stdout x ; output_string stdout "\n") l; flush stdout;*)
  let sys = build_linear_system l in
(*  Printf.printf "searching certificate found" ; flush stdout; *)
  match optimise sys with
    | None -> None (* No certificate *)
    | Some cert -> 
(*	Printf.printf "certificate found" ; flush stdout; *)
	let cert =  (rats_to_ints cert) in
	let rec make_cert cert i =
	  match cert with
	    | [] -> S_Z
	    | e::l -> 
		( 
		  match compare_big_int e  zero_big_int with
		    | 1 ->  
			S_Add (S_Mult (S_Pos (Utils.CamlToCoq.positive_big_int e),S_In (CamlToCoq.nat i)),make_cert l (i+1))
		    | 0 -> make_cert l (i+1)
		    | -1 -> failwith "Positivity violation"
		    | _ -> failwith "compare -1 0 1"
		)
	in
	let res = Some (make_cert cert 0) in
	res


let rec products l = 
  match l with
    | [] -> []
    | e::l' -> (List.map (Poly.product e) l)@(products l')


let debug = false

let decode l x = 
  let rec decode_aux slice_size slice_nb x = 
    if x < 0 then failwith "decode_aux: buggy";
    if debug then Printf.printf "decode_aux %i %i %i\n" slice_size slice_nb x;
    if x < slice_size
    then 
      (slice_nb,x+slice_nb)
    else 
      decode_aux (slice_size - 1) (slice_nb + 1) (x - slice_size) in
  decode_aux l 0 x




let cone_expr_of_int hints nb_poly i =
  let prods = nb_poly * (nb_poly + 1) / 2 in
  if i < nb_poly
  then S_In (CamlToCoq.nat i)
  else if i < prods + nb_poly
  then
    let (x,y) = decode nb_poly (i-nb_poly) in
    S_Mult (S_In (CamlToCoq.nat x), S_In (CamlToCoq.nat y))
  else 
    S_Square (List.nth  hints (i- (prods + nb_poly)))


let certificate_ext hints l =
  (* Developp the polynomials *)
  let l = List.map dev_form l in
  let hints_dev = List.map (fun x -> let p = dev_form x in Poly.product p p) hints in
  (* Go further in the cone : add products *)
  let l' = l@(products l)@hints_dev in
  let len = List.length l in 
  let sys = build_linear_system l' in
  match optimise sys with
    | None -> None (* No certificate *)
    | Some cert -> 
	let cert =  (rats_to_ints cert) in
	let rec make_cert cert i =
	  match cert with
	    | [] -> S_Z
	    | e::l -> 
		( 
		  match compare_big_int e  zero_big_int with
		    | 1 ->  
			S_Add (S_Mult (S_Pos (Utils.CamlToCoq.positive_big_int e),cone_expr_of_int hints len i),make_cert l (i+1))
		    | 0 -> make_cert l (i+1)
		    | -1 -> failwith "Positivity violation"
		    | _ -> failwith "compare -1 0 1"
		)
	in
	let res = Some (make_cert cert 0) in
	res




let linear_certificate l =
  (* Developp the polynomials *)
  let l = List.map dev_form l in
(*  List.iter (fun x -> Poly.pp stdout x ; output_string stdout "\n") l; flush stdout;*)
  let sys = build_linear_system l in
  match optimise sys with
    | None -> None (* No certificate *)
    | Some cert -> 
	let cert =  (rats_to_ints cert) in
	let rec make_cert cert i =
	  match cert with
	    | [] -> Micromega.Nil
	    | e::l -> 
		( 
		  match compare_big_int e  zero_big_int with
		    | 1 ->  
			Micromega.Cons( (Micromega.Pair(Utils.CamlToCoq.positive_big_int e, CamlToCoq.nat i)),make_cert l 0)
		    | 0 -> make_cert l (i+1)
		    | -1 -> failwith "Positivity violation"
		    | _ -> failwith "compare -1 0 1"
		)
	in
	let res = Some (make_cert cert 0) in
	res

