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
  -> apply_box (apply_box (apply_box (box_apply2 f t1 t2) t3) t4) t5



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

  (* /!\ : Binds one term variable. *)
  | TmAbs(ty, f) ->
     let (x,e) = unbind f in
     TmAbs(ty, unbox (bind_var x (lift_te (nf e))))
  | TmApp(t, u) ->
     let u' = nf u in
     begin
       match nf t with
       | TmAbs(_,f) -> nf (subst f u')
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

  (* /!\ : Binds two term variables. *)
  | TmCaseOf (v0, ty1, v1, ty2, v2) ->
     let (x1, e1) = unbind v1 in
     let e1' = nf e1 in
     let v1' = unbox (bind_var x1 (lift_te e1')) in
     (* this looks too complicated, could it be simpler ? *)
     let (x2, e2) = unbind v2 in
     let e2' = nf e2 in
     let v2' = unbox (bind_var x2 (lift_te e2')) in
     begin
       match (nf v0) with
       | TmInL (v0', _) -> nf (subst v1' v0')
       | TmInR (_, v0') -> nf (subst v2' v0')
       | v0' -> TmCaseOf (v0', ty1, v1', ty2, v2')
     end

  (* /!\ : Binds one term variable. *)
  | TmLet (m, n) ->
     let (x, e) = unbind n in
     let e' = nf e in
     let n' = unbox (bind_var x (lift_te e')) in
     let m' = nf m in
     nf (subst n' m')


(** Example of types and terms. --TODO *)
(* Having examples could be useful to test the normalisation and typing functions. *)







(** TYPING. *)


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
let find_type : term var -> var_ctx -> s_ty option = fun x ctx ->
  try Some(snd (List.find (fun (y,_) -> eq_vars x y) ctx))
  with Not_found -> None


(** Exceptions for typing. *)
(* Exceptions to raise when it is impossible
   to synthetise a type. *)
exception NotSynthetising
(* Exceptions to raise when it is impossible
   to check against a type. *)
exception NotChecking
(* Exceptions to raise when syntax directed checking
   failed, but subsumption could work. *)
exception TrySubsumption



(** Typing function. --WIP *)
(* Adapting the version from `BidirectionalFGCBV.ml`
   to use the Bindlib library.*)
let rec ty_check (ctx : var_ctx) (t : term) (ty : s_ty) : unit =
  let aux_subs (ctx : var_ctx) (t : term) (ty : s_ty) : unit  =
    try
      let ty_syn = ty_synth ctx t in
      assert (ty_syn = ty)
    with _ -> raise NotChecking in
  (* Subsumption is a checking rule,
     so when it fails, then it is a checking failure. *)
  
  begin try
      match t, ty with
      | TmVar _, _ -> raise TrySubsumption
        
      | TmAbs (tx, f),  TyArr(ty_x, ty_e) when (tx = ty_x) ->
         let (x, e) = unbind f in
         let ctx' = add_type (x, ty_x) ctx in
         (ty_check ctx' e ty_e)
      | TmAbs _ , _ -> raise NotChecking

        
      | TmPair (v1, v2), TyProd (ty1, ty2) ->
         (ty_check ctx v1 ty1) ;
         (ty_check ctx v2 ty2)       
      | TmPair _ , _ -> raise NotChecking
        
      | TmInL (vL, ty_R), TySum (tyL, tyR) when (ty_R = tyR) ->
         (ty_check ctx vL tyL)
      | TmInL _ , _ -> raise NotChecking
        
      | TmInR (ty_L, vR), TySum (tyL, tyR) when (ty_L = tyL) ->
         (ty_check ctx vR tyR)
      | TmInR _ , _ -> raise NotChecking
      (* check if ok *)
        
      | TmApp _, _ -> raise TrySubsumption     
      | TmProj1 _ , _ -> raise TrySubsumption  
      | TmProj2 _ , _ -> raise TrySubsumption
      | TmCaseOf _ , _ -> raise TrySubsumption
      | TmLet _ , _ -> raise TrySubsumption      
    with TrySubsumption -> (aux_subs ctx t ty)                            end

and  ty_synth (ctx : var_ctx) (t : term) : s_ty  =
  match t with
  | TmVar x ->
     begin
       match (find_type x ctx) with
       | None -> raise NotSynthetising
       | Some ty_x -> ty_x
     end 
  | TmAbs _ -> raise NotSynthetising
  | TmApp (t1, t2) ->
     let ty_t1 =  ty_synth ctx t1 in
     begin match ty_t1 with
     | TyArr(tyA,tyB) ->
        (ty_check ctx t2 tyA) ; tyB
     | _ -> raise NotSynthetising
     end

  | TmPair _ -> raise NotSynthetising
  | TmProj1 p ->
     let ty = ty_synth ctx p in
     begin match ty with
     | TyProd (ty1, _) -> ty1
     | _ -> raise NotSynthetising
     end
  | TmProj2 p ->
     let ty = ty_synth ctx p in
     begin match ty with
     | TyProd (_, ty2) -> ty2
     | _ -> raise NotSynthetising
     end

  | TmInL _ -> raise NotSynthetising
  | TmInR _ -> raise NotSynthetising
  | TmCaseOf (v, ty1, e1, ty2, e2) -> (* asymmetric version *)
     let ty = ty_synth ctx v in
     begin if (ty = TySum (ty1, ty2))
           then
             let (x1, f1) = unbind e1 in
             let (x2, f2) = unbind e2 in
             let ctx1 = add_type (x1, ty1) ctx in
             let ctx2 = add_type (x2, ty2) ctx in
             let b = ty_synth ctx1 f1 in
             (ty_check ctx2 f2 b) ; b
           else raise NotSynthetising
     end

  | TmLet (m, n) ->
     let ty_m = ty_synth ctx m in
     let (xn, fn) = unbind n in
     let ctx' = add_type (xn, ty_m) ctx in
     (ty_synth ctx' fn)
       (* check if this is ok *)
