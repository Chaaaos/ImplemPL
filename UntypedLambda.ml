(** ML IMPLEMENTATION OF UNTYPED LAMBDA-CALCULUS **)
(* Based on Chapter 7 of TAPL. *)


(** Inductive structure of terms. *)
(* Based on 5.1. *)
type term =
  | TmVar of int
  | TmAbs of term
  | TmApp of term * term


(** De Bruijn indices - Shifting. *)
(* Based on Definition 6.2.1. *)
let shift (t : term) (d : int) : term =
  let rec shift_aux (t : term) (c : int) =
    match t with
    | TmVar k when (k < c) -> TmVar k
    | TmVar k  -> TmVar (k + d)
    | TmAbs u -> TmAbs (shift_aux u (c + 1))
    | TmApp (u, v) -> TmApp ((shift_aux u c), (shift_aux v c))
  in
  shift_aux t 0
  

(** Substitution. *)
(* Based on Definition 6.2.4. *)
let rec subst (t: term) (j : int) (s : term) : term =
  match t with
  | TmVar k when k = j -> s
  | TmVar k -> TmVar k
  | TmAbs u -> TmAbs (subst u (j+1) (shift s 1))
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

(** Evaluation. *)
           (* a. Single step. *)
let rec eval_1step (t : term) =
  match t with
  | TmApp (TmAbs t1, v2) when (isval v2) ->
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
