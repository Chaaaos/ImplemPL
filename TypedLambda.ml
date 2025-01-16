(** ML IMPLEMENTATION OF TYPED LAMBDA-CALCULUS **)
(* Based on Chapter 10 of TAPL. *)


type sty_bool =
  TyBool
| TyMap of sty_bool * sty_bool
(* In the book, the chosen base type is Bool, but maybe we could view it as a parameter ? *)
