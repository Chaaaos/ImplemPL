(** ML IMPLEMENTATION OF TYPED LAMBDA-CALCULUS **)
(* Based on Chaptesr 10 and 11 of TAPL. *)


(** Structure of simple types. *)
type s_ty =
  | TyBool
  | TyArr of s_ty * s_ty
  | TyProd of s_ty * s_ty
  | TySum of s_ty * s_ty
(* In the book, the chosen base type is Bool, but maybe we could view it as a parameter ? Or consider a Set of base types ? *)

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
(* Based on 5.1. *)
type term =
  | TmVar of int
  | TmAbs of s_ty * term (* Binds one variable. *)
  | TmApp of term * term
  | TmPair of term * term
  | TmProj1 of term
  | TmProj2 of term
  | TmInL of term * s_ty
  | TmInR of s_ty * term
  | TmCaseOf of term * s_ty * term * s_ty * term (* Binds two variables. *)
  | TmLet of term * term (* Binds one variable. *)



(** Typing. WIP *)

(** Exceptions for typing and evaluation. *)

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
exception NoRuleApplies



let rec type_of (ctx : var_ctx) (t : term) : s_ty  =
  match t with
  | TmVar i -> get_type ctx i
  | TmAbs (ty, t1) ->
     let ctx' = add_type ty ctx in
     let ty_t1 = type_of ctx' t1 in
     TyArr(ty, ty_t1)
  | TmApp (t1,t2) ->
     let ty_t1 =  type_of ctx t1 in
     let ty_t2 =  type_of ctx t2 in
     begin match ty_t1 with
     | TyArr(ty1,ty2) -> if (ty_t2 = ty1) then ty2
                         else raise TypeMismatch
     | _ -> raise NotAnArrow
     end
  | TmPair (t1, t2) ->
     let ty1 = type_of ctx t1 in
     let ty2 = type_of ctx t2 in
     TyProd (ty1, ty2)
  | TmProj1 t ->
     let ty = type_of ctx t in
     begin match ty with
     | TyProd (t1, t2) -> t1
     | _ -> raise NotAProduct
     end
  | TmProj2 t ->
     let ty = type_of ctx t in
     begin match ty with
     | TyProd (t1, t2) -> t2
     | _ -> raise NotAProduct
     end
  | TmInL (vL, tyR) ->
     let tyL =  type_of ctx vL in
     TySum (tyL, tyR)
  | TmInR (tyL, vR) ->
     let tyR =  type_of ctx vR in
     TySum (tyL, tyR) 
  | TmCaseOf (v, ty_vL, tL, ty_vR, tR) ->
     let ty = type_of ctx v in
     begin if (ty = TySum (ty_vL, ty_vR))
           then
             let ctx' = add_type ty ctx in
             let tyL = type_of ctx' tL in
             let tyR = type_of ctx' tR in
             if (tyL = tyR) then tyL else raise TypeMismatch
           else raise NotASum
     end
  | TmLet (t1, t2) ->
     let ty1 = type_of ctx t1 in
     let ctx' = add_type ty1 ctx in
     (type_of ctx' t2)



(** De Bruijn indices - Shifting. *)
(* Same as in the untyped version. *)

let shift (t : term) (d : int) : term =
  let rec shift_aux (t : term) (c : int) =
    match t with
    | TmVar k when (k < c) -> TmVar k
    | TmVar k  -> TmVar (k + d)
    | TmAbs (ty, u) -> TmAbs (ty, (shift_aux u (c + 1)))
    | TmApp (u, v) -> TmApp ((shift_aux u c), (shift_aux v c))
    | TmPair (t1, t2) -> TmPair ((shift_aux t1 c), (shift_aux t2 c))
    | TmProj1 t' -> TmProj1 (shift_aux t' c)
    | TmProj2 t' -> TmProj2 (shift_aux t' c)
    | TmInL (vL, tyR) -> TmInL (shift_aux vL c, tyR)
    | TmInR (tyL, vR) -> TmInR (tyL, shift_aux vR c)
    | TmCaseOf (v, ty_vL, tL, ty_vR, tR) ->
       TmCaseOf ((shift_aux v c),
                 ty_vL, (shift_aux tL (c+1)),
                 ty_vR, (shift_aux tR (c+1)))
    | TmLet (t1, t2) ->
       TmLet ((shift_aux t1 c), (shift_aux t2 (c+1)))

  in
  shift_aux t 0


(** Substitution. WIP *) 
(* Based on Definition 6.2.4. *)
(* Same as in the untyped version.
   Relies on the fact that we should always substitute with
   terms whose type match the one of the variable they replace. *)


let rec subst (t: term) (j : int) (s : term) : term =
  match t with
  | TmVar k when k = j -> s
  | TmVar k -> TmVar k
  | TmAbs (ty, u) -> TmAbs (ty, (subst u (j+1) (shift s 1)))
  | TmApp (u, v) -> TmApp ((subst u j s), (subst v j s))
  | TmPair (t1, t2) -> TmPair ((subst t1 j s), (subst t2 j s))
  | TmProj1 t' -> TmProj1 (subst t' j s)
  | TmProj2 t' -> TmProj2 (subst t' j s)
  | TmInL (vL, tyR) -> TmInL (subst vL j s, tyR)
  | TmInR (tyL, vR) -> TmInR(tyL, subst vR j s)
  | TmCaseOf (v, ty_vL, tL, ty_vR, tR) ->
     TmCaseOf (subst v j s,
                 ty_vL, subst tL (j+1) (shift s 1),
                 ty_vR, subst tR (j+1) (shift s 1))
  | TmLet (t1, t2) ->
     TmLet ((subst t1 j s), (subst t2 (j+1) (shift s 1)))



(** Prerequisites for evaluation. *)
(* Checks if the term is a value. *)
(* Same as in the untyped version. *)
let rec is_val (t : term) =
  match t with
  | TmAbs _ -> true
  | TmPair (v1, v2) when ((is_val v1) && (is_val v2)) -> true
  | _ -> false
let head_subst t v =
let t' =  subst t 0 (shift v 1) in
     (shift t' (-1))

(* Exception to rise when the term is not a value as expected. *)
exception NotAValue

(* Exception to rise when the term is not a value as expected. *)
exception IllAppliedProjection

(* Exception to rise when no rule applies. *)
exception NoRuleApplies



(** Evaluation. WIP *)
(* a. Single step. *)
let rec eval_1step (t : term) =
  match t with
  | TmApp (TmAbs (ty, t1), v2) when (is_val v2) ->
     head_subst t1 v2
  | TmApp (v1, t2) when (is_val v1) ->
     TmApp (v1, eval_1step t2)
  | TmApp (t1, t2) ->
     TmApp (eval_1step t1, t2)
  | TmProj1 v when (is_val v) ->
     (* is this the best way to organise theses cases ? *)
     begin match v with
     | TmPair (v1, v2) -> v1
     | _ -> raise IllAppliedProjection
     end
  | TmProj2 v when (is_val v)->
     begin match v with
     | TmPair (v1, v2) -> v2
     | _ -> raise IllAppliedProjection
     end
  | TmProj1 u ->
     let u' = eval_1step u in
     TmProj1 u'
  | TmProj2 u ->
     let u' = eval_1step u in
     TmProj2 u'
  | TmPair (v1, t2) when (is_val v1) ->
     let t2'= eval_1step t2 in
     TmPair (v1, t2')
  | TmPair (t1, t2) ->
     let t1' = eval_1step t1 in
     TmPair (t1', t2)
  | TmCaseOf (TmInL (v0, tyR), ty_vL, tL, ty_vR, tR)
       when (is_val v0) -> head_subst tL v0
  | TmCaseOf (TmInR (tyL, v0), ty_vL, tL, ty_vR, tR)
       when (is_val v0) -> head_subst tR  v0
  | TmLet (v0, t)
       when (is_val v0) -> head_subst t v0
  | _ -> raise NoRuleApplies


(* b. Multi-step.*)
let rec eval_mstep (t : term) =
  try let u = (eval_1step t) in
      (eval_mstep u)
  with NoRuleApplies -> t

(* c. Big-step. *)
