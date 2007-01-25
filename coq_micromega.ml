(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
open Utils
let debug = false

let time str f x = 
  let t0 = (Unix.times()).Unix.tms_utime in
  let res = f x in 
  let t1 = (Unix.times()).Unix.tms_utime in 
  if debug then (Printf.printf "time %s %f\n" str (t1 -. t0) ; flush stdout); 
  res


module M =
struct
  open Micromega
  open Micromega.Polynomial
  open Coqlib
  open Term
    (*    let constant = gen_constant_in_modules "Omicron" coq_modules*)
    
    
  let logic_dir = ["Coq";"Logic";"Decidable"]
  let coq_modules =
    init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules @ [ ["Coq";"Lists";"List"];["Micromega"];
									 ["Coq";"QArith"; "QArith_base"];
									 ["Zpol"]]
      
  let constant = gen_constant_in_modules "Micromega" coq_modules
    
  let coq_cons = lazy (constant "cons")
  let coq_nil = lazy (constant "nil")
  let coq_list = lazy (constant "list")

  let coq_O = lazy (constant "O")
  let coq_S = lazy (constant "S")
  let coq_nat = lazy (constant "nat")
  let coq_pair = lazy (constant "pair")
  let coq_positive = lazy (constant "positive")
  let coq_xH = lazy (constant "xH")
  let coq_xO = lazy (constant "xO")
  let coq_xI = lazy (constant "xI")
  let coq_Z = lazy (constant "Z")
  let coq_ZERO = lazy (constant  "Z0")
  let coq_POS = lazy (constant  "Zpos")
  let coq_NEG = lazy (constant  "Zneg")

  let coq_Witness = lazy (constant "Build_Witness")
  let coq_Q = lazy (constant "Qmake")

  let coq_Zgt = lazy (constant "Zgt")
  let coq_Zge = lazy (constant "Zge")
  let coq_Zle = lazy (constant "Zle")
  let coq_Zlt = lazy (constant "Zlt")
  let coq_Eq  = lazy (constant "eq")

  let coq_Zplus = lazy (constant "Zplus")
  let coq_Zminus = lazy (constant "Zminus")
  let coq_Zopp = lazy (constant "Zopp")
  let coq_Zmult = lazy (constant "Zmult")

  open Ring
  let coq_V = coq_Pvar
  let coq_C = coq_Pconst
  let coq_Add = coq_Pplus
  let coq_UMinus = coq_Popp
  let coq_Mult = coq_Pmult

  let coq_OpEq = lazy (gen_constant_in_modules "Micromega" [["Micromega"]] "OpEq")
  let coq_OpNEq = lazy (gen_constant_in_modules "Micromega" [["Micromega"]] "OpNEq")
  let coq_OpLe = lazy (gen_constant_in_modules "Micromega" [["Micromega"]] "OpLe")
  let coq_OpLt = lazy (gen_constant_in_modules "Micromega" [["Micromega"]] "OpLt")
  let coq_OpGe = lazy (gen_constant_in_modules "Micromega" [["Micromega"]] "OpGe")
  let coq_OpGt = lazy (gen_constant_in_modules "Micromega" [["Micromega"]] "OpGt")


  let coq_S_In = lazy (constant "S_In")
  let coq_S_Square = lazy (constant "S_Square")
  let coq_S_Monoid = lazy (constant "S_Monoid")
  let coq_S_Ideal = lazy (constant "S_Ideal")
  let coq_S_Mult = lazy (constant "S_Mult")
  let coq_S_Add  = lazy (constant "S_Add")
  let coq_S_Pos  = lazy (constant "S_Pos")
  let coq_S_Z    = lazy (constant "S_Z")
    

  let coq_make_impl = lazy (gen_constant_in_modules "Micromega" [["Refl"]] "make_impl")
  let coq_make_conj = lazy (gen_constant_in_modules "Micromega" [["Refl"]] "make_conj")

  let coq_Build = lazy (constant "Build_Cstr")
  let coq_Cstr = lazy (constant "Cstr")

  let get_left_construct term = 
    match Term.kind_of_term term with
      | Term.Construct(_,i) -> (i,[| |])
      | Term.App(l,rst) -> 
	  (match Term.kind_of_term l with
	    | Term.Construct(_,i) -> (i,rst)
	    |   _     -> failwith "get_left_construct")
      | _ -> failwith "get_left_construct"
	
	
  let rec parse_nat term = 
    let (i,c) = get_left_construct term in
    match i with
      | 1 -> O
      | 2 -> S (parse_nat (c.(0)))
      |   _ -> failwith "not a natural number"
	    

  let pp_nat o n = Printf.fprintf o "%i" (CoqToCaml.nat n)


  let rec dump_nat x = 
    match x with
      | O -> Lazy.force coq_O
      | S p -> Term.mkApp(Lazy.force coq_S,[| dump_nat p |])



  let rec parse_positive term = 
    let (i,c) = get_left_construct term in
    match i with
      | 1 -> XI (parse_positive c.(0))
      | 2 -> XO (parse_positive c.(0))
      | 3 -> XH
      | _ -> failwith "not a positive"
	

  let rec dump_positive x = 
    match x with
      | XH -> Lazy.force coq_xH
      | XO p -> Term.mkApp(Lazy.force coq_xO,[| dump_positive p |])
      | XI p -> Term.mkApp(Lazy.force coq_xI,[| dump_positive p |])

  let pp_positive o x = Printf.fprintf o "%i" (CoqToCaml.positive x)	  


  open Quote

  let rec dump_index x = 
    match x with
      | End_idx -> Lazy.force coq_End_idx
      | Left_idx p -> Term.mkApp(Lazy.force coq_Left_idx,[| dump_index p |])
      | Right_idx p -> Term.mkApp(Lazy.force coq_Right_idx,[| dump_index p |])


  let pp_index o x = Printf.fprintf o "%i" (CoqToCaml.index x)	  


  let dump_pair t1 t2 dump_t1 dump_t2 (Pair (x,y)) =
    Term.mkApp(Lazy.force coq_pair,[| t1 ; t2 ; dump_t1 x ; dump_t2 y|])


  let rec parse_z term =
    let (i,c) = get_left_construct term in
    match i with
      | 1 -> Z0
      | 2 -> Zpos (parse_positive c.(0))
      | 3 -> Zneg (parse_positive c.(0))
      | _ -> failwith "not a positive"

  let dump_z x =
    match x with
      | Z0 ->Lazy.force coq_ZERO
      | Zpos p -> Term.mkApp(Lazy.force coq_POS,[| dump_positive p|])  
      | Zneg p -> Term.mkApp(Lazy.force coq_NEG,[| dump_positive p|])  

  let pp_z o x = Printf.fprintf o "%i" (CoqToCaml.z x)

	
  let rec parse_list parse_elt term = 
    let (i,c) = get_left_construct term in
    match i with
      | 1 -> Nil
      | 2 -> Cons(parse_elt c.(1), parse_list parse_elt c.(2))
      | _ -> failwith "not a list"


  let rec dump_list typ dump_elt l =
    match l with
	| Nil -> Term.mkApp(Lazy.force coq_nil,[| typ |])
	| Cons(e,l) -> Term.mkApp(Lazy.force coq_cons, [| typ; dump_elt e;dump_list typ dump_elt l|])
	  

  let pp_list op cl elt o l = 
    let rec _pp  o l = 
      match l with
	| Nil -> ()
	| Cons(e,Nil) -> Printf.fprintf o "%a" elt e
	| Cons(e,l) -> Printf.fprintf o "%a ,%a" elt e  _pp l in
    Printf.fprintf o "%s%a%s" op _pp l cl 



  let pp_var  = pp_index
  let dump_var = dump_index

  let rec pp_expr o e = 
    match e with
      | Micromega.Pvar n -> Printf.fprintf o "V %a" pp_var n
      | Micromega.Pconst z -> pp_z o z
      | Micromega.Pplus(e1,e2) -> Printf.fprintf o "(%a)+(%a)" pp_expr e1 pp_expr e2
      | Micromega.Pmult(e1,e2) -> Printf.fprintf o "%a*(%a)" pp_expr e1 pp_expr e2
      | Micromega.Popp e -> Printf.fprintf o "-(%a)" pp_expr e

  let rec dump_expr typ e =
    match e with
      | Micromega.Pvar n -> mkApp(Lazy.force coq_V,[| typ; dump_var n |])
      | Micromega.Pconst z -> mkApp(Lazy.force coq_C,[| typ ; dump_z z |])
      | Micromega.Pplus(e1,e2) -> mkApp(Lazy.force coq_Add,[| typ; dump_expr typ e1;dump_expr typ e2|])
      | Micromega.Popp e -> mkApp(Lazy.force coq_UMinus,[| typ; dump_expr typ e|])
      | Micromega.Pmult(e1,e2) ->  mkApp(Lazy.force coq_Mult,[| typ; dump_expr typ e1;dump_expr typ e2|])

  let rec dump_monoid l = dump_list (Lazy.force coq_nat) dump_nat l


  let rec dump_cone e =
    match e with
      | S_In n -> mkApp(Lazy.force coq_S_In,[| dump_nat n |])
      | S_Ideal(e,c) -> mkApp(Lazy.force coq_S_Ideal, [| dump_expr (Lazy.force coq_Z) e ; dump_cone c |])
      | S_Square e -> mkApp(Lazy.force coq_S_Square, [| dump_expr (Lazy.force coq_Z) e|])
      | S_Monoid l -> mkApp (Lazy.force coq_S_Monoid, [|dump_monoid l|])
      | S_Add(e1,e2) -> mkApp(Lazy.force coq_S_Add,[| dump_cone e1; dump_cone e2|])
      | S_Mult(e1,e2) -> mkApp(Lazy.force coq_S_Mult,[| dump_cone e1; dump_cone e2|])
      | S_Pos p -> mkApp(Lazy.force coq_S_Pos,[| dump_positive p|])
      | S_Z    -> Lazy.force coq_S_Z


  let rec pp_cone o e = 
    match e with 
      | S_In n -> Printf.fprintf o "(S_In %a)%%nat" pp_nat n
      | S_Ideal(e,c) -> Printf.fprintf o "(S_Ideal %a %a)" pp_expr e pp_cone c
      | S_Square e -> Printf.fprintf o "(S_Square %a)" pp_expr e
      | S_Monoid l -> Printf.fprintf o "(S_Monoid %a)" (pp_list "[" "]" pp_nat) l
      | S_Add(e1,e2) -> Printf.fprintf o "(S_Add %a %a)" pp_cone e1 pp_cone e2
      | S_Mult(e1,e2) -> Printf.fprintf o "(S_Mult %a %a)" pp_cone e1 pp_cone e2
      | S_Pos p -> Printf.fprintf o "(S_Pos %a)%%positive" pp_positive p
      | S_Z    -> Printf.fprintf o "S_Z"




  let rec parse_op term = 
    let (i,c) = get_left_construct term in
    match i with
      | 1 -> OpEq
      | 2 -> OpLe
      | 3 -> OpGe
      | 4 -> OpGt
      | 5 -> OpLt
      | _ -> failwith "not_an_operator"


  let rec dump_op = function
      | OpEq-> Lazy.force coq_OpEq
      | OpNEq-> Lazy.force coq_OpNEq
      | OpLe -> Lazy.force coq_OpLe
      | OpGe -> Lazy.force coq_OpGe
      | OpGt-> Lazy.force coq_OpGt
      | OpLt-> Lazy.force coq_OpLt



  let pp_op o e= 
    match e with 
      | OpEq-> Printf.fprintf o "="
      | OpNEq-> Printf.fprintf o "<>"
      | OpLe -> Printf.fprintf o "=<"
      | OpGe -> Printf.fprintf o ">="
      | OpGt-> Printf.fprintf o ">"
      | OpLt-> Printf.fprintf o "<"



(*  let  parse_cstr term =
    let (i,c) = get_left_construct term in
    {lhs = parse_expr c.(0); op0 = parse_op c.(1) ; rhs = parse_expr c.(2)}
*)

  let pp_cstr o {lhs = l ; op = op ; rhs = r } =
    Printf.fprintf o"(%a %a %a)" pp_expr l pp_op op pp_expr r

  let dump_cstr {lhs = e1 ; op = o ; rhs = e2} =
    let z = Lazy.force coq_Z in
    Term.mkApp(Lazy.force coq_Build,[| dump_expr z e1 ; dump_op o ; dump_expr z e2|])


  let parse_zop op =
    match kind_of_term op with
      | Const x -> 
	  (match Names.string_of_con x with
	    | "Coq.ZArith.BinInt#<empty>#Zgt" -> OpGt
	    | "Coq.ZArith.BinInt#<empty>#Zge" -> OpGe
	    | "Coq.ZArith.BinInt#<empty>#Zlt" -> OpLt
	    | "Coq.ZArith.BinInt#<empty>#Zle" -> OpLe
	    | "Coq.Init.Logic#<empty>#not" -> OpNEq
	    |   s -> failwith ("parse_zop "^s)
	  )
      |  Ind(n,0) -> 
	   (match Names.string_of_kn n with
	     | "Coq.Init.Logic#<empty>#eq" -> OpEq
	     | s -> failwith ("parse_zop"^s)
	   )
      |   _ -> failwith "parse_zop"

  module Env =
  struct 
    type t = constr list
	
    let compute_rank_add env v =
      let rec _add env n v =
	match env with
	  | [] -> ([v],n)
	  | e::l -> 
	      if eq_constr e v 
	      then (env,n)
	      else 
		let (env,n) = _add l ( n+1) v in
		(e::env,n) in
      let (env, n) =  _add env 1 v in
      (env, CamlToCoq.idx n)

	
    let empty = []
      
    let elements env = env

  end


  let is_constant t = (* This is an approx *)
    match kind_of_term t with
      | Construct(i,_) -> true 
      |   _ -> false

	    
  let rec parse_zexpr env term = 
    let combine env op (t1,t2) =
      let (expr1,env) = parse_zexpr env t1 in
      let (expr2,env) = parse_zexpr env t2 in
      (op expr1 expr2,env) in
      match kind_of_term term with
	| App(t,args) -> 
	    (
	      match kind_of_term t with
		| Const c -> 
		    (match  Names.string_of_con c with
		       | "Coq.ZArith.BinInt#<empty>#Zplus" -> 
			   combine env (fun x y -> Pplus(x,y)) (args.(0),args.(1))
		    | "Coq.ZArith.BinInt#<empty>#Zminus" -> 
			combine env (Polynomial.coq_Minus) (args.(0),args.(1)) 
		    | "Coq.ZArith.BinInt#<empty>#Zmult"-> 
			combine env (fun x y -> Pmult (x,y)) (args.(0),args.(1))
		    | "Coq.ZArith.BinInt#<empty>#Zopp"-> 
			let (expr,env) = parse_zexpr env args.(0) in
			  (Popp expr, env)
		    | "Coq.ZArith.Zpower#<empty>#Zpower"-> 
			(* This is convertible to a product *)
			let (expr,env) = parse_zexpr env args.(0) in
			  (power expr (parse_z args.(1))  , env) 
		    |  s -> 
			 let (env,n) = Env.compute_rank_add env term in  (Pvar n , env)
		    )
		| Construct(i,_) -> 
		    begin
		      try 
			( Pconst (parse_z term) , env)
		      with _ -> 
			let (env,n) = Env.compute_rank_add env term in
			  (Pvar  n , env)
		    end
		|   _   -> let (env,n) = Env.compute_rank_add env term in
		      (Pvar  n , env)
	    ) 
	| Var   id    ->   let (env,n) = Env.compute_rank_add env term in
	    (Pvar  n , env)
	|  Construct(i,_) -> ( Pconst (parse_z term) , env)
	     (*  Paramters  x : Z ... *)
	|  t   ->   let (env,n) = Env.compute_rank_add env term in
	     (Pvar  n , env)
	       
	     (* Pp.pp (Printer.prterm  term); Pp.pp_flush () ;*)

	      
(*  let check_term str term =
    match kind_of_term term with
      | Ind(n,_) -> str =  (Names.string_of_kn n)
      |     _    -> failwith "check term : not implemented"**)

  let rec parse_arith env cstr = 
    match kind_of_term cstr with
      | App(op,args) -> 
	  let zop = parse_zop op in
	    (match zop  with
	      | OpLe | OpLt | OpGe | OpGt -> 
		  let (e1,env) = parse_zexpr env args.(0) in
		  let (e2,env) = parse_zexpr env args.(1) in
		    ({lhs = e1; op = zop;rhs = e2},env)
	      | OpEq -> if args.(0) <> Lazy.force coq_Z
		then failwith "error: not an integer equation" 		  
		else
		  let (e1,env) = parse_zexpr env args.(1) in
		  let (e2,env) = parse_zexpr env args.(2) in
		    ({lhs = e1; op = zop;rhs = e2},env)
	      | OpNEq -> 
		  let ({lhs = e1; op = op;rhs = e2},env) = parse_arith env args.(0) in
		    match op with 
		      | OpEq -> ({lhs = e1; op = OpNEq;rhs = e2},env)
		      | _    -> failwith "error: parse_arith(1)"  )
      |  _ -> failwith "error : parse_arith(2)"




  let rec parse_conj env term = 
    match kind_of_term term with
      | App(l,rst) -> 
	  (match kind_of_term l with
	    | Ind (n,_) -> 
		( match Names.string_of_kn n with
		  | "Coq.Init.Logic#<empty>#and" -> 
		      let (e1,env) = parse_arith env rst.(0) in
		      let (e2,env) = parse_conj env rst.(1) in
			(Cons(e1,e2),env)
		  |   _ -> (* This might be an equality *) 
			let (e,env) = parse_arith env term in
			  (Cons(e,Nil),env))
	    |  _ -> (* This is an arithmetic expression *)
		 let (e,env) = parse_arith env term in
		   (Cons(e,Nil),env))
      |  _ -> failwith "parse_conj(2)"


  let rec parse_concl env term =
    match kind_of_term term with
      | Prod(_,expr,rst) -> (* a -> b *)
	  let (lhs,rhs,env) = parse_concl env rst in
	  let (e,env) = parse_arith env expr in
	  (Cons(e,lhs),rhs,env)
      | App(_,_) -> 
	  let (conj, env) = parse_conj env term in
	  (Nil,conj,env)
      |  Ind(n,_) -> (match (Names.string_of_kn n) with
	   | "Coq.Init.Logic#<empty>#False" -> (Nil,Nil,env)
	   |    _                           -> failwith "parse_concl")
      |  _ -> failwith "parse_concl"


  let rec parse_hyps env goal_hyps hyps = 
    match hyps with
      | [] -> ([],goal_hyps,env)
      | (i,t)::l -> 
	  let (li,lt,env) = parse_hyps env goal_hyps l in
	  try 
	    let (c,env) = parse_arith env  t in
	    (i::li, Cons(c,lt), env)
	  with Failure x -> 
	    (*(if debug then Printf.printf "parse_arith : %s\n" x);*)
	    (li,lt,env)

  exception ParseError


  let parse_goal env hyps term = 
    try
      let (lhs,rhs,env) = parse_concl env term in
      let (li,lt,env) = parse_hyps env lhs hyps in
	(li,lt,rhs,env)
    with Failure x -> raise ParseError



(* ! reverse the list of bindings *)
  let set l concl =
    let rec _set acc = function
      | [] -> acc
      | (e::l) ->  
	  let (name,expr,typ) = e in
	  _set (Term.mkNamedLetIn
	    (Names.id_of_string name)
	    expr typ acc) l in
    _set concl l


end            

open M
open Micromega.Polynomial

let find_witness prover    polys1 =
  let l = CoqToCaml.list (fun x -> x) polys1 in
    match 
      try_any prover l
    with
      | None -> None
      | Some cert -> (*let (Micromega.Pair (e,op)) = eval_cone polys1 cert in
	  (if debug then Printf.printf "witness : %a %s\n" pp_expr e 
	     (match op with Strict -> "Strict" | NonStrict -> "NonStrict" |  Equal -> "Equal") ; flush stdout);*)
	  Some cert

let rec witness prover   l1 l2 = 
  match l2 with
    | Micromega.Nil -> Some (Micromega.Nil)
    | Micromega.Cons(e,l2) -> 
	match find_witness prover   (Micromega.Cons( e,l1)) with
	  | None -> None
	  | Some w -> 
	      (match witness prover   l1 l2 with
		| None -> None
		| Some l -> Some (Micromega.Cons (w,l))
	      )


let rec apply_ids t ids = 
  match ids with
    | [] -> t
    | i::ids -> apply_ids (Term.mkApp(t,[| Term.mkVar i |])) ids



let micromega_empty_change env polys1 gl = 
  let t = 
    set 
      [ 
	("__poly", dump_list (Lazy.force coq_Cstr) dump_cstr polys1, Term.mkApp(Lazy.force coq_list,[| Lazy.force coq_Cstr|]));
	("__varmap", Quote.btree_of_array (Array.of_list env) (Lazy.force coq_Z) , (constant "varmap_type"))
      ]  	
      (Term.mkApp(Lazy.force coq_make_impl, 
      [| 
	constant "Cstr";
	Term.mkApp (Tacmach.pf_parse_const gl "eval",[|Term.mkVar (Names.id_of_string "__varmap")|]);
	Term.mkVar (Names.id_of_string "__poly"); 
	constant "False"
      |])) in
  Tactics.change_in_concl None t gl


let micromega_empty prover env ids   polys1 gl = 
  match find_witness prover   (Micromega.Checkers.normalise_list polys1) with
    | None -> Tacticals.tclFAIL 0 (Pp.str "Cannot find witness") gl
    | Some res -> 
	let res' = dump_cone res in
	  if debug then (pp_cone stdout res ; print_newline () ;flush stdout);
	(Tacticals.tclTHENSEQ
	  [
	    Tactics.generalize (List.map Term.mkVar ids);
	    micromega_empty_change env polys1 ;
	    Tactics.intro ; Tactics.intro ;
	    Tactics.apply (Tacmach.pf_parse_const gl "empty_checkerT_sound") ;
	    Tactics.constructor_tac (Some 1) 1 (Rawterm.ImplicitBindings [res'])
	  ]) gl






let micromega_order_change env  polys1 polys2 gl = 
  Tactics.change_in_concl None
    (set 
      [ 
	("__poly1", dump_list (Lazy.force coq_Cstr) dump_cstr polys1, Term.mkApp(Lazy.force coq_list,[| Lazy.force coq_Cstr|]));
	("__poly2", dump_list (Lazy.force coq_Cstr) dump_cstr polys2, Term.mkApp(Lazy.force coq_list,[| Lazy.force coq_Cstr|]));
	("__varmap", Quote.btree_of_array (Array.of_list env) (Lazy.force coq_Z) , (constant "varmap_type"))
      ]  	

      (Term.mkApp(Lazy.force coq_make_impl, 
      [| 
	constant "Cstr";
	Term.mkApp (Tacmach.pf_parse_const gl "eval",[|Term.mkVar (Names.id_of_string "__varmap")|]);
	Term.mkVar (Names.id_of_string "__poly1"); 
	(Term.mkApp(Lazy.force coq_make_conj, 
	[| 
	  constant "Cstr";
	  Term.mkApp (Tacmach.pf_parse_const gl "eval",[|Term.mkVar (Names.id_of_string "__varmap")|]);
	  Term.mkVar (Names.id_of_string "__poly2"); 
	|])) |])))
    gl 
  

let micromega_order prover env ids   polys1 polys2  gl = 
  match witness prover   (Micromega.Checkers.normalise_list polys1) (Micromega.Checkers.negate_list polys2) with
    | None -> Tacticals.tclFAIL 0 (Pp.str "Cannot find witness") gl
    | Some res -> 
	let res' = dump_list (constant "ConeMember") dump_cone res in
	  if debug then (pp_list "[" "]" pp_cone stdout res ; print_newline ();flush stdout);
	(Tacticals.tclTHENSEQ
	  [
	    Tactics.generalize (List.map Term.mkVar ids);
	    micromega_order_change env  polys1 polys2 ;
	    Tactics.intro ; Tactics.intro ;
	    Tactics.apply (Tacmach.pf_parse_const gl "order_checkerT_sound") ;
	    Tactics.constructor_tac (Some 1) 1 (Rawterm.ImplicitBindings [res'])
	  ]) gl



let micromega_gen prover  gl =

    let concl = Tacmach.pf_concl gl in
    let hyps  = Tacmach.pf_hyps_types gl in
      try
	let (ids, polys1,polys2,env) = parse_goal Env.empty hyps concl in
	  (*      (if debug then 
		  let l = CoqToCaml.list (fun x -> x) polys1 in
		  List.iter (fun x -> Printf.printf "%a\n" pp_cstr x) l) ;*)
	let env = Env.elements env in
	  match polys2 with
	    | Micromega.Nil  -> micromega_empty prover env ids   polys1 gl
	    | _              -> micromega_order prover env ids   polys1 polys2 gl
      with Failure x -> flush stdout ; Pp.pp_flush () ; Tacticals.tclFAIL 0 (Pp.str x) gl
	| ParseError  -> Tacticals.tclFAIL 0 (Pp.str "Bad logical fragment") gl





(* Pure sos decomposition *)
let sos gl = micromega_gen [Certificate.pure_sos , "pure sos refutation"]   gl

(* psatz *)
let micromega   i gl = micromega_gen [Certificate.real_nonlinear_prover i , "sos refutation"]   gl

(* Fourier  : beware it does not handle <> *)
let omicron gl = micromega_gen [Certificate.linear_prover, "fourier refutation" ]   gl



(* zomicron *)

let dump_q bd1 = 
  Term.mkApp(Lazy.force coq_Q, [|dump_z (CamlToCoq.bigint (numerator bd1)) ; dump_positive (CamlToCoq.positive_big_int (denominator bd1)) |])



let dump_zwitness (var,bd1,c1,bd2,c2) = 
  Term.mkApp(Lazy.force coq_Witness, [| dump_expr (Lazy.force coq_Z) var ; 
				       dump_pair (constant "Q") (constant "ConeMember") dump_q dump_cone (Micromega.Pair(bd1,c1)) ; 
				       dump_pair (constant "Q") (constant "ConeMember") dump_q dump_cone (Micromega.Pair(bd2,c2)) |])


let zomicron  gl =
    let concl = Tacmach.pf_concl gl in
    let hyps  = Tacmach.pf_hyps_types gl in
      try
	let (ids, polys1,polys2,env) = parse_goal Env.empty hyps concl in
	  (*      (if debug then 
		  let l = CoqToCaml.list (fun x -> x) polys1 in
		  List.iter (fun x -> Printf.printf "%a\n" pp_cstr x) l) ;*)
	let env = Env.elements env in
	  match polys2 with
	    | Micromega.Nil  -> 
		begin
		  match Certificate.zlinear_prover  (CoqToCaml.list (fun x -> x) (Micromega.Checkers.normalise_list polys1)) with
		    | None -> Tacticals.tclFAIL 0 (Pp.str "Cannot find witness") gl
		    | Some res -> 
			let res' = dump_zwitness res in
			  (Tacticals.tclTHENSEQ
			     [
			       Tactics.generalize (List.map Term.mkVar ids);
			       micromega_empty_change env polys1 ;
			       Tactics.intro ; Tactics.intro ;
			       Tactics.apply (constant "zChecker_sound") ;
			       Tactics.constructor_tac (Some 1) 1 (Rawterm.ImplicitBindings [res'])
			     ]) gl
		end
	    | _              -> failwith "Bad Logical Fragment (False expected)"
      with Failure x -> flush stdout ; Pp.pp_flush () ; Tacticals.tclFAIL 0 (Pp.str x) gl
	| ParseError  -> Tacticals.tclFAIL 0 (Pp.str "Bad logical fragment") gl

