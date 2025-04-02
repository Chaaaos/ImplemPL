(** ML IMPLEMENTATION OF TYPED LAMBDA-CALCULUS **)
(* Based on the "Bidirectionnal Typing",
   Dunfield & Krishnaswami 2020. *)


(** Structure of simple types. *)
type s_ty =
  | TyUnit
  | TyArr of s_ty * s_ty


(** Typing contexts> *)
type var_ctx = s_ty list

(* Adds the typing information for a new variable
   in head position. *)
let add_type (ty : s_ty) (ctx : var_ctx) = (ty :: ctx)

(* Execption to rise when a variable
   is not typed in the given context. *)
exception VarNotTyped

(* Given a typing context and a De Bruijn index,
   returns the type of the corresponding variable when it exists.*)
let rec get_type (ctx : var_ctx) (i : int) : s_ty =
  match i, ctx with
  | 0, [ty] -> ty
  | j, (ty :: ctx') when (j > 0) -> (get_type ctx' (j-1))
  | _, _ -> raise VarNotTyped


(** Inductive structure of terms. *)
type term =
  | TmUnit (* Added for bidirectionalisation. *)
  | TmVar of int
  | TmAnnot of term * s_ty (* Added for bidirectionalisation. *)
  | TmAbs of s_ty * term (* Adding the type of the bound variable. *)
  | TmApp of term * term


(** Bidirectional Typing. *)

(* Exceptions to raise when it is impossible
   to synthetise a type. *)
exception NotSynthetising
(* Exceptions to raise when it is impossible
   to check against a type. *)
exception NotChecking
(* Exceptions to raise when syntax directed checking
   failed, but subsumption could work. *)
exception TrySubsumption

(* Mutually defined type checking & type synthetising functions. *)
let rec type_check (ctx : var_ctx) (tm : term) (ty : s_ty) : unit  =
  (* Subsubmption as an auxiliary function for checking. *)
  let aux_subs (ctx : var_ctx) (tm : term) (ty : s_ty) : unit  =
    try
      let ty_syn = type_synth ctx tm in
      assert (ty_syn = ty)
    with fail -> raise NotChecking in
  begin try
      match tm, ty with
      (* unit <= *)
      | TmUnit, TyUnit -> ()
      (* ->i <= *)
      | TmAbs (tx, e), TyArr(ty_x, ty_e) ->
         if (tx = ty_x) ;
         then let ctx' = add_type ty_x ctx in
              type_check ctx' e ty_e
         else raise NotChecking
      | _, _ -> raise TrySubsumption
                      (* replace with missing patterns *) 
    with TrySubsumption -> (aux_subs ctx tm ty)
  end
and type_synth (ctx : var_ctx) (t : term) : s_ty  =
  match t with
  (* Var => *)
  | TmVar i -> get_type ctx i
  (* Anno => *)
  | TmAnnot (tm, ty) ->
     (type_check ctx tm ty) ; ty
  (* ->e => *)
  | TmApp (t1, t2) ->
     let ty_t1 =  type_synth ctx t1 in
     begin match ty_t1 with
     | TyArr(tyA,tyB) ->
        (type_check ctx t2 tyA) ; tyB
     | _ -> raise NotSynthetising
     end
  | TmUnit -> raise NotSynthetising
  | TmAbs (ty, tm) -> raise NotSynthetising




(** De Bruijn indices - Shifting. *)
(* Same as in the untyped version. *)

let shift (t : term) (d : int) : term =
  let rec shift_aux (t : term) (c : int) =
    match t with
    | TmUnit -> TmUnit
    | TmAnnot (tm, ty) -> TmAnnot (shift_aux tm c, ty) 
    | TmVar k when (k < c) -> TmVar k
    | TmVar k  -> TmVar (k + d)
    | TmAbs (ty, u) -> TmAbs (ty, (shift_aux u (c + 1)))
    | TmApp (u, v) -> TmApp ((shift_aux u c), (shift_aux v c))
  in
  shift_aux t 0


(** Substitution. WIP *)
(* Same as in the untyped version.
   Relies on the fact that we should always substitute with
   terms whose type match the one of the variable they replace. *)


let rec subst (t: term) (j : int) (s : term) : term =
  match t with
  | TmUnit -> TmUnit
  | TmVar k when k = j -> s
  | TmVar k -> TmVar k
  | TmAnnot (tm, ty) -> TmAnnot (subst tm j s, ty)
  | TmAbs (ty, u) -> TmAbs (ty, (subst u (j+1) (shift s 1)))
  | TmApp (u, v) -> TmApp ((subst u j s), (subst v j s))


(** Prerequisites for evaluation. *)
(* Checks if the term is a value. *)
(* Same as in the untyped version. *)
let rec isval (t : term) =
  match t with
  | TmAbs _ -> true
  | _ -> false
let head_subst t v =
  let t' =  subst t 0 (shift v 1) in
  (shift t' (-1))

(* Exception to rise when the term is not a value as expected. *)
exception NotAValue
(* Exception to rise when no rule applies. *)
exception NoRuleApplies



(** Evaluation.  *)
(* a. Single step. *)
let rec eval_1step (t : term) =
  match t with
  | TmApp (TmAbs (ty, t1), v2) when (isval v2) ->
     head_subst t1 v2
  | TmApp (v1, t2) when (isval v1) ->
     TmApp (v1, eval_1step t2)
  | TmApp (t1, t2) ->
     TmApp (eval_1step t1, t2)
  | _ -> raise NoRuleApplies

(* b. Multi-step.*)
let rec eval_mstep (t : term) =
  try let u = (eval_1step t) in
      (eval_mstep u)
  with NoRuleApplies -> t

                          (* c. Big-step. *)
