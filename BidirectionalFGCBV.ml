(** ML IMPLEMENTATION OF
    FINE GRAINED CBV LAMBDA-CALCULUS **)
(* Based on Chapters 10 and 11 of TAPL. *)


(** Structure of simple types. *)
type s_ty =
  | TyUnit
  | TyArr of s_ty * s_ty
  | TyProd of s_ty * s_ty
  | TySum of s_ty * s_ty

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
(* Based on 5.1, with additional constructors. *)
type value =
  | ValUnit
  | ValVar of int
  | ValAbs of s_ty * comp (* Binds one variable. *)
  | ValPair of value * value
  | ValInL of value * s_ty
  | ValInR of s_ty * value 
and comp =
  | CompApp of value * value
  | CompProj1 of value
  | CompProj2 of value
  | CompCaseOf of value * s_ty * comp * s_ty * comp (* Binds two variables. *)
  | CompLet of comp * comp
  | CompReturn of value


(** Exceptions for typing and evaluation. *)

(**
   (* Typing - Exception to raise when the types do not match
   in an application (CompApp) or when deconstructing a sum. *)
   exception TypeMismatch

   (* Typing - Exception to raise when the first term of an application
   (CompApp) does not have an arrow type as expected. *)
   exception NotAnArrow

   (* Typing - Exception to raise when a projection (CompProj1/2)
   is applied to a value whose type is not a product. *)
   exception NotAProduct

   (* Typing - Exception to raise when a case computation (CompCaseOf)
   is applied to a value whose type is not a sum. *)
   exception NotASum

   (* Evaluation - Exception to raise when no rule applies. *)
   exception NoRuleApplies *)

(* Exceptions to raise when it is impossible
   to synthetise a type. *)
exception NotSynthetising
(* Exceptions to raise when it is impossible
   to check against a type. *)
exception NotChecking
(* Exceptions to raise when syntax directed checking
   failed, but subsumption could work. *)
exception TrySubsumption

(** Typing. *)

let rec ty_check_value (ctx : var_ctx) (v : value) (ty : s_ty) : unit =
  let aux_subs_val (ctx : var_ctx) (v : value) (ty : s_ty) : unit  =
    try
      let ty_syn = ty_synth_value ctx v in
      assert (ty_syn = ty)
    with fail -> raise NotChecking in
  (* Subsumption is a checking rule,
     so when it fails, then it is a checking failure. *)
  
  begin try
      match v, ty with
      | ValUnit, TyUnit -> ()
      | ValVar i, _ -> raise TrySubsumption
      | ValAbs (tx, e),  TyArr(ty_x, ty_e) ->
         if (tx = ty_x)
         then let ctx' = add_type ty_x ctx in
              (ty_check_comp ctx' e ty_e)
         else raise NotChecking
      | ValPair (v1, v2), TyProd (ty1, ty2) ->
         (ty_check_value ctx v1 ty1) ;
         (ty_check_value ctx v2 ty2)
      | ValInL (vL, ty_R), TySum (tyL, tyR) ->
         if (ty_R = tyR)
         then (ty_check_value ctx vL tyL)
         else raise NotChecking
      | ValInR (ty_L, vR), TySum (tyL, tyR) ->
         if (ty_L = tyL)
         then (ty_check_value ctx vR ty)
         else raise NotChecking
      | _, _ -> raise TrySubsumption
                      (* change this asap & add missing patterns *)
    with TrySubsumption -> (aux_subs_val ctx v ty)
                             (* change with the right exception*)
  end
and ty_check_comp (ctx : var_ctx) (t : comp)  (ty : s_ty) : unit =
  
  let aux_subs_comp (ctx : var_ctx) (t : comp) (ty : s_ty) : unit  =
    try
      let ty_syn = ty_synth_comp ctx t in
      assert (ty_syn = ty)
    with fail -> raise NotChecking in
  try
    match t, ty with
    | CompReturn v, ty -> ty_check_value ctx v ty
    | _, _ -> raise TrySubsumption
                    (* replace with missing patterns *)
  with TrySubsumption -> (aux_subs_comp ctx t ty)


and  ty_synth_value (ctx : var_ctx) (v : value) : s_ty  =
  match v with
  | ValUnit -> raise NotSynthetising
  | ValVar i -> get_type ctx i
  | ValAbs (ty, t1) -> raise NotSynthetising
  | ValPair (v1, v2) -> raise NotSynthetising
  | ValInL (vL, tyR) -> raise NotSynthetising
  | ValInR (tyL, vR) -> raise NotSynthetising
and ty_synth_comp (ctx : var_ctx) (t : comp) : s_ty =
  match t with
  | CompApp (t1, t2) ->
     let ty_t1 =  ty_synth_value ctx t1 in
     begin match ty_t1 with
     | TyArr(tyA,tyB) ->
        (ty_check_value ctx t2 tyA) ; tyB
     | _ -> raise NotSynthetising
     end
  | CompProj1 v ->
     let ty = ty_synth_value ctx v in
     begin match ty with
     | TyProd (ty1, ty2) -> ty1
     | _ -> raise NotSynthetising
     end
  | CompProj2 v ->
     let ty = ty_synth_value ctx v in
     begin match ty with
     | TyProd (ty1, ty2) -> ty2
     | _ -> raise NotSynthetising
     end
  | CompCaseOf (v, a1, t1, a2, t2) -> (* asymmetric version *)
     let ty = ty_synth_value ctx v in
     begin if (ty = TySum (a1, a2))
           then
             let ctx1 = add_type a1 ctx in
             let ctx2 = add_type a2 ctx in
             let b = ty_synth_comp ctx1 t1 in
             (ty_check_comp ctx2 t2 b) ; b
           else raise NotSynthetising
     end
  | CompLet (m, n) ->
     let ty_m = ty_synth_comp ctx m in
     let ctx' = add_type ty_m ctx in
     (ty_synth_comp ctx' n)
  | CompReturn v -> ty_synth_value ctx v



(** De Bruijn indices - Shifting. *)
(* Same as in the untyped version. *)

let rec shift_aux (d : int) (v : value) (c : int) =
  match v with
  | ValUnit -> ValUnit
  | ValVar k when (k < c) -> ValVar k
  | ValVar k  -> ValVar (k + d)
  | ValAbs (ty, u) -> ValAbs (ty, (shift_comp_aux d u (c + 1)))
  | ValPair (v1, v2) -> ValPair ((shift_aux d v1 c), (shift_aux d v2 c))
  | ValInL (vL, tyR) -> ValInL (shift_aux d vL c, tyR)
  | ValInR (tyL, vR) -> ValInR (tyL, shift_aux d vR c)

and shift_comp_aux (d : int) (t : comp) (c : int) =
  match t with
  | CompApp (u, v) -> CompApp ((shift_aux d u c), (shift_aux d v c))
  | CompProj1 v -> CompProj1 (shift_aux d v c)
  | CompProj2 v -> CompProj2 (shift_aux d v c)
  | CompCaseOf (v, ty_vL, tL, ty_vR, tR) ->
     CompCaseOf ((shift_aux d v c), ty_vL, (shift_comp_aux d tL (c+1)), ty_vR, (shift_comp_aux d tR (c+1)))
  | CompLet (t1, t2) -> CompLet ((shift_comp_aux d t1 c), (shift_comp_aux d t2 (c+1)))
  | CompReturn t' -> CompReturn (shift_aux d t' c)

let shift (t : value) (d : int) : value =
  shift_aux d t 0
and shift_comp (t : comp) (d : int) : comp =
  shift_comp_aux d t 0

(** Substitution. WIP *) 
(* Based on Definition 6.2.4. *)
(* Same as in the untyped version.
   Relies on the fact that we should always substitute with
   terms whose type match the one of the variable they replace. *)


let rec subst_value (v : value) (j : int) (s : value) : value =
  match v with
  | ValUnit -> ValUnit
  | ValVar k when k = j -> s
  | ValVar k -> ValVar k
  | ValAbs (ty, u) -> ValAbs (ty, (subst u (j+1) (shift s 1)))
  | ValPair (t1, t2) -> ValPair ((subst_value t1 j s), (subst_value t2 j s))
  | ValInL (vL, tyR) -> ValInL (subst_value vL j s, tyR)
  | ValInR (tyL, vR) -> ValInR (tyL , subst_value vR j s)

and  subst (t: comp) (j : int) (s : value) : comp =
  match t with
  | CompApp (u, v) -> CompApp ((subst_value u j s), (subst_value v j s))
  | CompProj1 t' -> CompProj1 (subst_value t' j s)
  | CompProj2 t' -> CompProj2 (subst_value t' j s)
  | CompCaseOf (v, ty_vL, tL, ty_vR, tR) ->
     CompCaseOf (subst_value v j s,
                 ty_vL, subst tL (j+1) (shift s 1),
                 ty_vR, subst tR (j+1) (shift s 1))
  | CompLet (t1, t2) -> CompLet ((subst t1 j s), (subst t2 (j+1) (shift s 1)))
  | CompReturn t' -> CompReturn (subst_value t' j s)


(** Prerequisites for evaluation. *)
(* Checks if the term is a value. *)
(* Same as in the untyped version. *)
let head_subst t v =
  let t' =  subst t 0 (shift v 1) in
  (shift_comp t' (-1))

(* Exception to rise when the term is not a value as expected. *)
exception NotAValue
(* Exception to rise when no rule applies. *)
exception NoRuleApplies


(** Evaluation. *)


(* a. Single step. *)
let rec eval_1step (t : comp) =
  match t with
  | CompApp (ValAbs (ty, t1), v2) ->
     head_subst t1 v2
  | CompProj1 (ValPair (v1, v2)) -> CompReturn v1
  | CompProj2 (ValPair (v1, v2)) -> CompReturn v2
  | CompCaseOf (ValInL (v0, tyR), ty_vL, tL, ty_vR, tR) ->
     head_subst tL v0
  | CompCaseOf (ValInR (tyL, v0), ty_vL, tL, ty_vR, tR) ->
     head_subst tR  v0
  | CompLet (CompReturn(v1), t2) ->
     head_subst t2 v1
  | _ -> raise NoRuleApplies


(* b. Multi-step.*)
let rec eval_mstep (t : comp) =
  try let u = (eval_1step t) in
      (eval_mstep u)
  with NoRuleApplies -> t

                          (* c. Big-step. *)
