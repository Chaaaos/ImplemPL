(** ML IMPLEMENTATION OF UNTYPED ARITHMETIC EXPRESSIONS **)
(* Based on Chapter 4 of TAPL. *)


(** Inductive structure of terms. *)
type term =
  TmTrue
| TmFalse
| TmIf of term * term * term
| TmZero
| TmSucc of term
| TmPred of term
| TmIsZero of term
(* In the book's version,
   terms carry an additional "info" data,
   representing parsing information.*)


(** Functions needed for evaluation. *)
(* Checks if the term is a numerical value. *)
let rec isnumericval t =
  match t with
  |TmZero -> true
  | TmSucc t1 -> isnumericval t1
  | _ -> false

(* Checks if the term is a value. *)
let rec isval t =
  match t with
  | TmTrue -> true
  | TmFalse -> true
  | t when isnumericval t -> true
  | _ -> false

(* Exception to rise when no rule applies. *)
exception NoRuleApplies

(** Evaluation. *)
(* Single-Step. *)
let rec eval1 t =
  match t with
    TmIf(TmTrue,t2,t3) ->
     t2
  | TmIf(TmFalse,t2,t3) ->
     t3
  | TmIf(t1,t2,t3) ->
     let t1' = eval1 t1 in
     TmIf(t1', t2, t3)
  | TmSucc(t1) ->
     let t1' = eval1 t1 in
     TmSucc(t1')
  | TmPred(TmZero) ->
     TmZero
  | TmPred(TmSucc(nv1)) when (isnumericval nv1) ->
     nv1
  | TmPred(t1) ->
     let t1' = eval1 t1 in
     TmPred(t1')
  | TmIsZero(TmZero) ->
     TmTrue
  | TmIsZero(TmSucc(nv1)) when (isnumericval nv1) ->
     TmFalse
  | TmIsZero(t1) ->
     let t1' = eval1 t1 in
     TmIsZero(t1')
  | _ ->
     raise NoRuleApplies
(* The use of `isval` and `isnumerical` in the evaluator
 adds a form of typing/typing condition to the rules,
 which matches the intuition.*)

(* Simple evaluation. *)
let rec eval t =
  try let t' = eval1 t
      in eval t'
  with NoRuleApplies -> t


(* -> Do exercises 4.2.1 and 4.2.2. *)
(* -> See the code of the whole interpreter. *)
