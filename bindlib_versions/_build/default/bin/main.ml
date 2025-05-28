(** BINDLIB IMPLEMENTATION OF LAMBDA-CALCULUS WITH CONSTRUCTORS **)
(* Based on the paper "Abstract Representation of Binders in OCaml
   using the Bindlib Library" by R. Lepigre and C. Rafalli.*)
(* Follows closely the example presented in the article for System F. *)



open Bindlib
(*let test = Bindlib.new_mvar*)



(** SYNTAX. *)
(** Structure of simple types. *)
(* Adapting the previous definition to Bindlib. *)
type s_ty =
  | TyBool
  | TyArr of s_ty * s_ty
  | TyProd of s_ty * s_ty
  | TySum of s_ty * s_ty


(** Structure of terms with additional constructors. *)
(* Adapting the previous definition to Bindlib. *)
type term =
  | TmVar of term var
  | TmAbs of s_ty * (term,  term) binder (* Binds one term variable. *)
  | TmApp of term * term
  | TmPair of term * term
  | TmProj1 of term
  | TmProj2 of term
  | TmInL of term * s_ty
  | TmInR of s_ty * term
  | TmCaseOf of term * s_ty * (term, term) binder * s_ty * (term, term) binder (* Binds two term variables. *)
  | TmLet of term * (term, term) binder (* Binds one term variable. *)





(** NORMALISATION. *)
(** Preliminary definitions for smart constructors. *)
let box_apply5 : ('a -> 'b -> 'c -> 'd -> 'e -> 'f)
                 -> 'a box -> 'b box -> 'c box -> 'd box -> 'e box
                 -> 'f box
  = fun f t1 t2 t3 t4 t5
  -> apply_box (box_apply2 (unbox (box_apply2 f t1 t2)) t3 t4) t5



(** Smart constructors. *)
(* Smart constructors are needed to work under binders,
 which is required to write the normalisation function. *)

(* TYPES. *)
(* Not useful here, they will be later. *)
(* Base type. *)
let _TyBool : s_ty box = box TyBool
  
(* Arrow type. *)
let _TyArr : s_ty box -> s_ty box -> s_ty box =
  box_apply2 (fun a b -> TyArr(a,b))

(* Type Product. *)
let _TyProd : s_ty box -> s_ty box -> s_ty box =
  box_apply2 (fun a b -> TyProd(a,b))

(* Type Sum. *)
let _TySum : s_ty box -> s_ty box -> s_ty box =
  box_apply2 (fun a b -> TySum(a,b))



(* TERMS.*)
(* Variable. *)
let _TmVar : term var -> term box = box_var

(* Abstraction. *)
let _TmAbs : s_ty box -> (term,term) binder box -> term box =
  box_apply2 (fun a f -> TmAbs(a,f))
(* Application. *)
let _TmApp : term box -> term box -> term box =
  box_apply2 (fun t u -> TmApp(t,u))

(* Pairing. *)
let _TmPair : term box -> term box -> term box =
  box_apply2 (fun t1 t2 -> TmPair(t1,t2))
(* 1st Projection. *)
let _TmProj1 : term box -> term box =
  box_apply (fun p -> TmProj1(p))
(* 2nd Projection. *)
let _TmProj2 : term box -> term box =
  box_apply (fun p -> TmProj2(p))

(* Left Injection. *)
let _TmInL : term box -> s_ty box -> term box =
  box_apply2 (fun tL tyR -> TmInL(tL,tyR))
(* Right Injection. *)
let _TmInR : s_ty box -> term box -> term box =
  box_apply2 (fun tyL tR -> TmInR(tyL,tR))
(* Case constructor. *)
let _TmCaseOf : term box
                -> s_ty box -> (term, term) binder box
                -> s_ty box -> (term, term) binder box -> term box =
  box_apply5 (fun v ty1 v1 ty2 v2 -> TmCaseOf(v, ty1, v1, ty2, v2))

(* Let constructor. *)
let _TmLet : term box -> (term,term) binder box -> term box =
  box_apply2 (fun a f -> TmLet(a,f))


(** Lifting functions. *)
(* Needed to define the normalisation function,
 to box subterms after normalising under a binder. *)

let rec lift_ty : s_ty -> s_ty box = fun a ->
  match a with
  | TyBool -> _TyBool
  | TyArr(a, b) -> _TyArr (lift_ty a) (lift_ty b)
  | TyProd(a, b) -> _TyProd (lift_ty a) (lift_ty b)
  | TySum(a, b) -> _TySum (lift_ty a) (lift_ty b)

let rec lift_te : term -> term box = fun t ->
  match t with
  | TmVar(x) -> _TmVar x
  | TmAbs(a, t) -> _TmAbs (lift_ty a) (box_binder lift_te t)
  | TmApp(t, u) -> _TmApp (lift_te t) (lift_te u)
  | TmPair(t1, t2) -> _TmPair (lift_te t1) (lift_te t2)
  | TmProj1(p) -> _TmProj1 (lift_te p)
  | TmProj2(p) -> _TmProj2 (lift_te p)
  | TmInL(tL, tyR) -> _TmInL (lift_te tL) (lift_ty tyR)
  | TmInR(tyL, tR) -> _TmInR (lift_ty tyL) (lift_te tR)
  | TmCaseOf(v, ty1, v1, ty2, v2)
    -> _TmCaseOf (lift_te v) (lift_ty ty1) (box_binder lift_te v1) (lift_ty ty2) (box_binder lift_te v2)
  | TmLet(m, n) -> _TmLet (lift_te m) (box_binder lift_te n)
(* failwith "not yet defined" *)


(** Normalisation function. *)

let rec nf : term -> term = fun t ->
  match t with
  | TmVar(_) ->
     t

  | TmAbs(ty, f) -> (* /!\ : Binds one term variable. *)
      let (x,e) = unbind f in
      TmAbs(ty, unbox (bind_var x (lift_te (nf e))))
  | TmApp(t, u) ->
     let u' = nf u in
     begin
       match nf t with
       | TmAbs(_,f) -> nf (subst f u)
       | t' -> TmApp(t', u')
     end

  | TmPair(t1, t2) ->
     let t1' = nf t1 in
     let t2' = nf t2 in
     TmPair (t1', t2')
  | TmProj1(p) ->
     begin
       match p with
       | TmPair(t1, _) -> t1
       | p' -> TmProj1(p')
     end
  | TmProj2(p) -> 
     begin
       match p with
       | TmPair(_, t2) -> t2
       | p' -> TmProj2(p')
     end

  | TmInL(tL, tyR) ->
     let tL' = nf tL in
       TmInL(tL', tyR)
  | TmInR(tyL, tR) ->
     let tR' = nf tR in
     TmInR(tyL, tR')

  | TmCaseOf(v, ty1, v1, ty2, v2) -> (* /!\ : Binds two term variables. *)
     let (x1, e1) = unbind v1 in
     let (x2, e2) = unbind v2 in
     TmCaseOf(nf v, ty1, unbox(bind_var x1 (lift_te (nf e1))), ty2,  unbox(bind_var x2 (lift_te (nf e2))))

  | TmLet(m, n) -> (* /!\ : Binds one term variable. *)
     let (x, e) = unbind n in
     TmLet(nf m, unbox(bind_var x (lift_te (nf e))))


(** Example of types and terms. --TODO *)
(* Having examples could be useful to test the normalisation and typing functions. *)







(** TYPING. --WIP *)


(** Typing contexts. *)
(* This part is the same as in the System F example, from the Bindlib paper.*)

(* Type of variable typing contexts. *)
type var_ctx = (term var * s_ty) list
(* formerly: type var_ctx = s_ty list *)

(* Adds the typing information for a new variable
 in head position. *)
let add_type (te_ty : term var * s_ty) (ctx : var_ctx) = (te_ty :: ctx)

(* Gets the type of a given variable in a given context
   by comparing the id of the variables. *)
let find_ctx : term var -> var_ctx -> s_ty option = fun x ctx ->
try Some(snd (List.find (fun (y,_) -> eq_vars x y) ctx))
with Not_found -> None


(** Typing function. --TODO *)

