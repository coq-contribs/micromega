(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
module type Solver =
  sig
    open Big_int
    type state

    val init : unit -> state
    val find_witness :   state -> Micromega.M.coq_Expr Micromega.list -> big_int list option
  end


module CoqToCaml =
struct
  open Micromega

  let rec nat = function
    | O -> 0
    | S n -> (nat n) + 1


  let rec positive p = 
    match p with
    | XH -> 1
    | XI p -> 1+ 2*(positive p)
    | XO p -> 2*(positive p)


  let rec index i = (* Swap left-right ? *)
    match i with
      | End_idx -> 1
      | Right_idx i -> 1+(2*(index i))
      | Left_idx i -> 2*(index i)


  let z x = 
    match x with
      | Z0 -> 0
      | Zpos p -> (positive p)
      | Zneg p -> - (positive p)

  open Big_int

  let rec positive_big_int p =
    match p with
      | XH -> unit_big_int
      | XI p -> add_int_big_int 1 (mult_int_big_int 2 (positive_big_int p))
      | XO p -> (mult_int_big_int 2 (positive_big_int p))


  let z_big_int x = 
    match x with
      | Z0 -> zero_big_int
      | Zpos p -> (positive_big_int p)
      | Zneg p -> minus_big_int (positive_big_int p)


  let num x = Num.Big_int (z_big_int x)

  let rec list elt l =
    match l with
      | Nil -> []
      | Cons(e,l) -> (elt e)::(list elt l)
end


module CamlToCoq =
struct
  open Micromega

  let rec nat = function
    | 0 -> O
    | n -> S (nat (n-1))


  let rec positive n =
    if n=1 then XH
    else if n land 1 = 1 then XI (positive (n lsr 1))
    else  XO (positive (n lsr 1))
	
      
  let index n = 
    (*a.k.a path_of_int *)
    (* returns the list of digits of n in reverse order with
       initial 1 removed *)
    let rec digits_of_int n =
      if n=1 then [] 
      else (n mod 2 = 1)::(digits_of_int (n lsr 1))
    in
    List.fold_right 
      (fun b c -> (if b then Right_idx c else Left_idx c))
      (List.rev (digits_of_int n))
	(End_idx)


  let z x = 
    match compare x 0 with
      | 0 -> Z0
      | 1 -> Zpos (positive x)
      | _ -> (* this should be -1 *)
	  Zneg (positive (-x)) 

  open Big_int

  let positive_big_int n = 
    let two = big_int_of_int 2 in 
    let rec _pos n = 
      if eq_big_int n unit_big_int then XH
      else
	let (q,m) = quomod_big_int n two  in
	if eq_big_int unit_big_int m 
	then XI (_pos q)
	else XO (_pos q) in
    _pos n

  let bigint x = 
    match sign_big_int x with
      | 0 -> Z0
      | 1 -> Zpos (positive_big_int x)
      | _ -> Zneg (positive_big_int (minus_big_int x))


  let list elt l = List.fold_right (fun x l -> Cons(elt x, l)) l Nil

end
