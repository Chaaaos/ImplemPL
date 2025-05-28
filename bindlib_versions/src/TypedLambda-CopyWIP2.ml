(** ML IMPLEMENTATION OF TYPED LAMBDA-CALCULUS **)
(* Based on Chapter 10 of TAPL. *)


(** Structure of simple types. *)
type s_ty =
  | TyBool
  | TyArr of s_ty * s_ty
(* In the book, the chosen base type is Bool, but maybe we could view it as a parameter ? Or consider a Set of base types ? *)

(** Adding binding information to variables. *)
(* In the book, variable typing info is added in contexts,
   which they already implemented for the untyped version. *)
(* Since I did it differently and did not use contexts,
   I want to try and continue without them.
   This may not be a good idea.*)
type var_ctx = int -> s_ty option 


(** Inductive structure of terms. *)
(* Based on 5.1. *)
type term =
  | TmVar of int
  | TmAbs of s_ty * term (* Adding the type of the bound variable. *)
  | TmApp of term * term


(** Typing. WIP *)

exception VarNotTyped
exception TypeMismatch
exception NotAnArrow


let rec type_of ctx t : s_ty  =
match t with
| TmVar i ->
   begin  match (ctx i) with
   | Some ty -> ty
   | None -> raise VarNotTyped
   end
| TmAbs (ty, t1) ->
   let ctx' = ctx in
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


(** De Bruijn indices - Shifting.  WIP *)

(* WIP *)
let context_shift (c : var_ctx) (d : int) (th : int) : var_ctx =
  fun (k : int) -> (if (k < th) then (c k) else (c k))
(* Change this - only for Ocaml typechecking. *)

(* WIP *)
(* We should shift both the indices and the type context, right ? *)
let shift (t : term) (d : int) : term =
  let rec shift_aux (t : term) (c : int) =
    match t with
    | TmVar k when (k < c) -> TmVar k
    | TmVar k  -> TmVar (k + d)
    | TmAbs (ty, u) -> TmAbs (ty, (shift_aux u (c + 1)))
    | TmApp (u, v) -> TmApp ((shift_aux u c), (shift_aux v c))
  in
  shift_aux t 0








(** ------------------------------------------------------ *)


(** Substitution. WIP *) 
(* Based on Definition 6.2.4. *)
let rec subst (t: term) (j : int) (s : term) : term =
  match t with
  | TmVar k when k = j -> s
  | TmVar k -> TmVar k
  | TmAbs (ty, u) -> TmAbs (ty, (subst u (j+1) (shift s 1)))
  | TmApp (u, v) -> TmApp ((subst u j s), (subst v j s))

(** Prerequisites for evaluation. *)
(* Checks if the term is a value. *)
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

(** Evaluation. WIP *)
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
