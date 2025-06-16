(** BINDLIB IMPLEMENTATION OF SYSTEM F **)
(* Based on the paper "Abstract Representation of Binders in OCaml
   using the Bindlib Library" by R. Lepigre and C. Rafalli.*)
(* Follows closely the example presented in the article for System F. *)



open Bindlib
(*let test = Bindlib.new_mvar*)



(** SYNTAX. *)
(** Structure of simple types. *)
(* Bindlib version of SystemF types (with additional constructors). *)
type s_ty =
  | TyVar of s_ty var
  | TyArr of s_ty * s_ty
  | TyAll of (s_ty, s_ty) binder

  | TyProd of s_ty * s_ty
  | TySum of s_ty * s_ty


(** Structure of terms with additional constructors. *)
(* Bindlib version of SystemF terms (with additional constructors). *)
type value =
  | ValVar of value var
  | ValAbs of s_ty * (value,  comp) binder (* Is it right to bind a value here ? *)
  | ValLam of (s_ty, value) binder
  | ValSpe of value * s_ty

  | ValPair of value * value
  | ValInL of value * s_ty
  | ValInR of s_ty * value

and comp =
  | CompApp of value * value

  | CompProj1 of value
  | CompProj2 of value
  | CompCaseOf of value * s_ty * (value, comp) binder * s_ty * (value, comp) binder (* Binds two term variables. *)
  | CompBind of comp * (value, comp) binder (* Binds one term variable. *)
  | CompReturn of value


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
(* Type Variable. *)
let _TyVar : s_ty var -> s_ty box = box_var
(* Arrow type. *)
let _TyArr : s_ty box -> s_ty box -> s_ty box =
  box_apply2 (fun a b -> TyArr(a,b))
(* Universal Quantifier. *)
let _TyAll : (s_ty, s_ty) binder box -> s_ty box =
  box_apply (fun a -> TyAll a)

(* Type Product. *)
let _TyProd : s_ty box -> s_ty box -> s_ty box =
  box_apply2 (fun a b -> TyProd(a,b))

(* Type Sum. *)
let _TySum : s_ty box -> s_ty box -> s_ty box =
  box_apply2 (fun a b -> TySum(a,b))



(* VALUES.*)
(* Variable. *)
let _ValVar : value var -> value box = box_var
(* Abstraction. *)
let _ValAbs : s_ty box -> (value, comp) binder box -> value box =
  box_apply2 (fun a f -> ValAbs(a,f))
(* Type Abstraction. *)
let _ValLam : (s_ty, value) binder box -> value box =
  box_apply (fun t -> ValLam(t))
(* Type Specialisation. *)
let _ValSpe : value box -> s_ty box -> value box =
  box_apply2 (fun t ty -> ValSpe (t, ty))


(* Pairing. *)
let _ValPair : value box -> value box -> value box =
  box_apply2 (fun t1 t2 -> ValPair(t1,t2))
(* Left Injection. *)
let _ValInL : value box -> s_ty box -> value box =
  box_apply2 (fun tL tyR -> ValInL(tL,tyR))
(* Right Injection. *)
let _ValInR : s_ty box -> value box -> value box =
  box_apply2 (fun tyL tR -> ValInR(tyL,tR))

(* COMPUTATIONS.*)
(* Application. *)
let _CompApp : value box -> value box -> comp box =
  box_apply2 (fun t u -> CompApp(t,u))

(* 1st Projection. *)
let _CompProj1 : value box -> comp box =
  box_apply (fun p -> CompProj1(p))
(* 2nd Projection. *)
let _CompProj2 : value box -> comp box =
  box_apply (fun p -> CompProj2(p))
(* Case constructor. *)
let _CompCaseOf : value box
                  -> s_ty box -> (value, comp) binder box
                  -> s_ty box -> (value, comp) binder box -> comp box =
  box_apply5 (fun v ty1 v1 ty2 v2 -> CompCaseOf(v, ty1, v1, ty2, v2))

(* Let constructor. *)
let _CompBind : comp box -> (value, comp) binder box -> comp box =
  box_apply2 (fun a f -> CompBind(a,f))
(* Return constructor. *)
let _CompReturn : value box -> comp box =
  box_apply (fun v -> CompReturn(v))

(** Lifting functions. *)
(* Needed to define the normalisation function,
   to box subterms after normalising under a binder. *)
let rec lift_ty : s_ty -> s_ty box = fun a ->
  match a with
  | TyVar a -> _TyVar a
  | TyAll a -> _TyAll (box_binder lift_ty a)
  | TyArr(a, b) -> _TyArr (lift_ty a) (lift_ty b)
  | TyProd(a, b) -> _TyProd (lift_ty a) (lift_ty b)
  | TySum(a, b) -> _TySum (lift_ty a) (lift_ty b)

let rec lift_val : value -> value box = fun v ->
  match v with
  | ValVar(x) -> _ValVar x
  | ValAbs(a, t) -> _ValAbs (lift_ty a) (box_binder lift_comp t)
  | ValLam t -> _ValLam (box_binder lift_val t)
  | ValSpe (t, a) -> _ValSpe (lift_val t) (lift_ty a) 

  | ValPair(t1, t2) -> _ValPair (lift_val t1) (lift_val t2)
  | ValInL(tL, tyR) -> _ValInL (lift_val tL) (lift_ty tyR)
  | ValInR(tyL, tR) -> _ValInR (lift_ty tyL) (lift_val tR)
and lift_comp : comp -> comp box = fun c ->
  match c with
  | CompApp(t, u) -> _CompApp (lift_val t) (lift_val u)

  | CompProj1(p) -> _CompProj1 (lift_val p)
  | CompProj2(p) -> _CompProj2 (lift_val p)
  | CompCaseOf(v, ty1, v1, ty2, v2) ->
     _CompCaseOf (lift_val v) (lift_ty ty1) (box_binder lift_comp v1) (lift_ty ty2) (box_binder lift_comp v2)

  | CompBind(m, n) -> _CompBind (lift_comp m) (box_binder lift_comp n)
  | CompReturn v -> _CompReturn (lift_val v)
(* failwith "Not yet defined." *)

(** Exceptions for normalisation. *)
(* Exception to rise when the term is not a value as expected. *)
exception NotAValue
(* Exception to rise when no rule applies. *)
exception NoRuleApplies


(** Normalisation function. *)
let rec nf_comp : comp -> comp = fun t ->
  match t with
  (* /!\ : Substitutes one term variable. *)
  | CompApp(ValAbs(_,f), u) ->
     let u' = nf_val u in
     nf_comp (subst f u')
  | CompApp (t, u) ->
     let u' = nf_val u in
     CompApp (t, u')

  | CompProj1(p) ->
     begin
       match nf_val p with
       | ValPair(t1, _) -> CompReturn t1
       | p' -> CompProj1(p')
     end
  | CompProj2(p) ->
     begin
       match nf_val p with
       | ValPair(_, t2) -> CompReturn t2
       | p' -> CompProj2(p')
     end

  (* /!\ : Substitutes two term variables. *)
  | CompCaseOf (v0, ty1, v1, ty2, v2) ->
     begin
       match (nf_val v0) with
       | ValInL (v0', _) -> nf_comp (subst v1 v0')
       | ValInR (_, v0') -> nf_comp (subst v2 v0')
       | v0' -> CompCaseOf (v0', ty1, v1, ty2, v2)
     end
  (* /!\ : Substitutes one term variable. *)
  | CompBind(m, n) ->
     let m' = nf_comp m in
     begin
       match m' with
       | CompReturn (v) ->
          nf_comp (subst n v)
       | CompApp _ | CompProj1 _ | CompProj2 _ | CompCaseOf _ | CompBind _ as e -> CompBind(e, n)   
     end

  | CompReturn v ->
     let v' = nf_val v in
     CompReturn v'

and nf_val : value -> value = fun v ->
  match v with
  | ValVar _ ->
     v
  | ValAbs(ty, f) ->
     let (x,e) = unbind f in
     let e' = lift_comp (nf_comp e) in
     ValAbs(ty, unbox (bind_var x e'))
  | ValLam f ->
     let (a, e) = unbind f in
     let e' = lift_val (nf_val e) in
     ValLam (unbox (bind_var a e'))
  (* ValSpe is a value so there is no substitution involved, right ? *)
  | ValSpe (f, a) ->
     let f' = nf_val f in
     ValSpe (f', a)

  | ValPair (t1, t2) -> 
     let t1' = nf_val t1 in
     let t2' = nf_val t2 in
     ValPair (t1', t2')
  | ValInL (tL, tyR) ->  
     let tL' = nf_val tL in
     ValInL(tL', tyR)
  | ValInR(tyL, tR) ->
     let tR' = nf_val tR in
     ValInR(tyL, tR')


(** Example of types and terms. --TODO *)
(* Having examples could be useful to test the normalisation and typing functions. *)







(** TYPING. *)


(** Typing contexts. *)
(* This part is the same as in the System F example, from the Bindlib paper.*)

(* Type of variable typing contexts. *)
type var_ctx = (value var * s_ty) list
(* formerly: type var_ctx = s_ty list *)

(* Adds the typing information for a new variable
   in head position. *)
let add_type (te_ty : value var * s_ty) (ctx : var_ctx) = (te_ty :: ctx)

(* Gets the type of a given variable in a given context
   by comparing the id of the variables. *)
let find_type : value var -> var_ctx -> s_ty option = fun x ctx ->
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




(** Typing function. *)
(* Adapting the implementation of type checking and synthetising
   for SystemF from the Bindlib paper to FG-CB
   + adding new constructors.*)

let rec ty_check_val (ctx : var_ctx) (t : value) (ty : s_ty) : unit =
  let aux_subs (ctx : var_ctx) (t : value) (ty : s_ty) : unit  =
    try
      let ty_syn = ty_synth_val ctx t in
      assert (ty_syn = ty)
    with _ -> raise NotChecking in
  (* Subsumption is a checking rule,
     so when it fails, then it is a checking failure. *)
  
  begin try
      match t, ty with
      | ValVar _, _ ->
         raise TrySubsumption
        
      | ValAbs (tx, f),  TyArr(ty_x, ty_e) when (tx = ty_x) ->
         let (x, e) = unbind f in
         let ctx' = add_type (x, ty_x) ctx in
         (ty_check_comp ctx' e ty_e)
      | ValAbs _ , _ ->
         raise NotChecking

      | ValLam _ , _ ->
         raise TrySubsumption
      | ValSpe _ , _ ->
         raise TrySubsumption
        
      | ValPair (v1, v2), TyProd (ty1, ty2) ->
         (ty_check_val ctx v1 ty1) ;
         (ty_check_val ctx v2 ty2)       
      | ValPair _ , _ -> raise NotChecking
        
      | ValInL (vL, ty_R), TySum (tyL, tyR) when (ty_R = tyR) ->
         (ty_check_val ctx vL tyL)
      | ValInL _ , _ -> raise NotChecking
        
      | ValInR (ty_L, vR), TySum (tyL, tyR) when (ty_L = tyL) ->
         (ty_check_val ctx vR tyR)
      | ValInR _ , _ -> raise NotChecking
        
    with TrySubsumption -> (aux_subs ctx t ty)                            end
and ty_check_comp (ctx : var_ctx) (t : comp) (ty : s_ty) : unit =    
  let aux_subs_comp (ctx : var_ctx) (t : comp) (ty : s_ty) : unit  =
    try
      let ty_syn = ty_synth_comp ctx t in
      assert (ty_syn = ty)
    with _ -> raise NotChecking in
  
  try
    match t, ty with
    | CompReturn v, ty -> ty_check_val ctx v ty
    | CompApp _, _ | CompProj1 _, _ | CompProj2 _, _ | CompCaseOf _, _ | CompBind _ , _ -> raise TrySubsumption

  with TrySubsumption -> (aux_subs_comp ctx t ty)

and  ty_synth_val (ctx : var_ctx) (t : value) : s_ty  =
  match t with
  | ValVar x ->
     begin
       match (find_type x ctx) with
       | None -> raise NotSynthetising
       | Some ty_x -> ty_x
     end 
  | ValAbs _ -> raise NotSynthetising

  | ValLam f ->
     let (a, e) = unbind f in
     let ty_e = ty_synth_val ctx e in
     let ty_bind = unbox (bind_var a (lift_ty ty_e)) in
     (* is there a way to avoid lifting, and
        then immediately unboxing here ?*)
     TyAll (ty_bind)
  | ValSpe (v0, arg_ty) ->
     let ty_v0 = ty_synth_val ctx v0 in
     begin
       match ty_v0 with
       | TyAll f -> subst f arg_ty
       | _ -> raise NotSynthetising
     end

  | ValPair _ -> raise NotSynthetising
  | ValInL _ -> raise NotSynthetising
  | ValInR _ -> raise NotSynthetising

and  ty_synth_comp (ctx : var_ctx) (t : comp) : s_ty  =
  match t with
  | CompApp (t1, t2) ->
     let ty_t1 =  ty_synth_val ctx t1 in
     begin match ty_t1 with
     | TyArr(tyA,tyB) ->
        (ty_check_val ctx t2 tyA) ; tyB
     | _ -> raise NotSynthetising
     end
  | CompProj1 p ->
     let ty = ty_synth_val ctx p in
     begin match ty with
     | TyProd (ty1, _) -> ty1
     | _ -> raise NotSynthetising
     end
  | CompProj2 p ->
     let ty = ty_synth_val ctx p in
     begin match ty with
     | TyProd (_, ty2) -> ty2
     | _ -> raise NotSynthetising
     end
  | CompCaseOf (v, ty1, e1, ty2, e2) -> (* asymmetric version *)
     let ty = ty_synth_val ctx v in
     begin if (ty = TySum (ty1, ty2))
           then
             let (x1, f1) = unbind e1 in
             let (x2, f2) = unbind e2 in
             let ctx1 = add_type (x1, ty1) ctx in
             let ctx2 = add_type (x2, ty2) ctx in
             let b = ty_synth_comp ctx1 f1 in
             (ty_check_comp ctx2 f2 b) ; b
           else raise NotSynthetising
     end
  | CompBind (m, n) ->
     let ty_m = ty_synth_comp ctx m in
     let (xn, fn) = unbind n in
     let ctx' = add_type (xn, ty_m) ctx in
     (ty_synth_comp ctx' fn)
  | CompReturn v ->
     (ty_synth_val ctx v)
