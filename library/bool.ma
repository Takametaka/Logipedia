include "basics/pts.ma".
include "connectives.ma".
include "leibniz.ma".
include "logic.ma".
include "relations.ma".
axiom bool : Type[0].
axiom true : (bool) .
axiom false : (bool) .
axiom match_bool_prop : \forall (return_:((bool) ) -> Prop). ((return_) ((true) )) -> ((return_) ((false) )) -> \forall (z:(bool) ). (return_) (z).
axiom match_bool_type : \forall return_ : Type[0] . (return_) -> (return_) -> ((bool) ) -> return_.
axiom axiom_match_bool_type_true : \forall return_. \forall (case_true:return_). \forall (case_false:return_). (((equal) (return_)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((true) ))) (case_true).
definition eq_match_bool_type_true : \forall return_. \forall (case_true:return_). \forall (case_false:return_). (((leibniz) (return_)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((true) ))) (case_true) := \lambda return_ : Type[0]. \lambda case_true : return_. \lambda case_false : return_. ((((equal_leibniz) (return_)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((true) ))) (case_true)) ((((axiom_match_bool_type_true) (return_)) (case_true)) (case_false)).
axiom axiom_match_bool_type_false : \forall return_. \forall (case_true:return_). \forall (case_false:return_). (((equal) (return_)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((false) ))) (case_false).
definition eq_match_bool_type_false : \forall return_. \forall (case_true:return_). \forall (case_false:return_). (((leibniz) (return_)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((false) ))) (case_false) := \lambda return_ : Type[0]. \lambda case_true : return_. \lambda case_false : return_. ((((equal_leibniz) (return_)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((false) ))) (case_false)) ((((axiom_match_bool_type_false) (return_)) (case_true)) (case_false)).
definition sym_eq_match_bool_type_true : \forall return_. \forall (case_true:return_). \forall (case_false:return_). (((leibniz) (return_)) (case_true)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((true) )) := \lambda return_ : Type[0]. \lambda case_true : return_. \lambda case_false : return_. ((((sym_leibniz) (return_)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((true) ))) (case_true)) ((((eq_match_bool_type_true) (return_)) (case_true)) (case_false)).
definition sym_eq_match_bool_type_false : \forall return_. \forall (case_true:return_). \forall (case_false:return_). (((leibniz) (return_)) (case_false)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((false) )) := \lambda return_ : Type[0]. \lambda case_true : return_. \lambda case_false : return_. ((((sym_leibniz) (return_)) (((((match_bool_type) (return_)) (case_true)) (case_false)) ((false) ))) (case_false)) ((((eq_match_bool_type_false) (return_)) (case_true)) (case_false)).
definition bool_discr : \forall (x:(bool) ). \forall (y:(bool) ). ((((eq) ((bool) )) (x)) (y)) -> ((((match_bool_type) (Prop)) (((((match_bool_type) (Prop)) (\forall (P:Prop). (P) -> P)) (\forall (P:Prop). P)) (y))) (((((match_bool_type) (Prop)) (\forall (P:Prop). P)) (\forall (P:Prop). (P) -> P)) (y))) (x) := \lambda x : (bool) . \lambda y : (bool) . \lambda Deq : (((eq) ((bool) )) (x)) (y). (((((((eq_ind) ((bool) )) (x)) (\lambda x_13 : (bool) . ((((match_bool_type) (Prop)) (((((match_bool_type) (Prop)) (\forall (P:Prop). (P) -> P)) (\forall (P:Prop). P)) (x_13))) (((((match_bool_type) (Prop)) (\forall (P:Prop). P)) (\forall (P:Prop). (P) -> P)) (x_13))) (x))) (((((match_bool_prop) (\lambda j__ : (bool) . ((((match_bool_type) (Prop)) (((((match_bool_type) (Prop)) (\forall (P:Prop). (P) -> P)) (\forall (P:Prop). P)) (j__))) (((((match_bool_type) (Prop)) (\forall (P:Prop). P)) (\forall (P:Prop). (P) -> P)) (j__))) (j__))) ((((((sym_eq_match_bool_type_true) (Prop)) (((((match_bool_type) (Prop)) (\forall (P:Prop). (P) -> P)) (\forall (P:Prop). P)) ((true) ))) (((((match_bool_type) (Prop)) (\forall (P:Prop). P)) (\forall (P:Prop). (P) -> P)) ((true) ))) (\lambda x0 : Prop. x0)) ((((((sym_eq_match_bool_type_true) (Prop)) (\forall (P:Prop). (P) -> P)) (\forall (P:Prop). P)) (\lambda x0 : Prop. x0)) (\lambda P : Prop. \lambda DH : P. (DH))))) ((((((sym_eq_match_bool_type_false) (Prop)) (((((match_bool_type) (Prop)) (\forall (P:Prop). (P) -> P)) (\forall (P:Prop). P)) ((false) ))) (((((match_bool_type) (Prop)) (\forall (P:Prop). P)) (\forall (P:Prop). (P) -> P)) ((false) ))) (\lambda x0 : Prop. x0)) ((((((sym_eq_match_bool_type_false) (Prop)) (\forall (P:Prop). P)) (\forall (P:Prop). (P) -> P)) (\lambda x0 : Prop. x0)) (\lambda P : Prop. \lambda DH : P. (DH))))) (x))) (y)) (Deq)).
definition not_eq_true_false : ((Not) ) ((((eq) ((bool) )) ((true) )) ((false) )) := ((nmk) ((((eq) ((bool) )) ((true) )) ((false) ))) (\lambda Heq : (((eq) ((bool) )) ((true) )) ((false) ). (((((((eq_match_bool_type_false) (Prop)) (\forall (P:Prop). (P) -> P)) (\forall (P:Prop). P)) (\lambda x : Prop. x)) ((((((eq_match_bool_type_true) (Prop)) (((((match_bool_type) (Prop)) (\forall (P:Prop). (P) -> P)) (\forall (P:Prop). P)) ((false) ))) (((((match_bool_type) (Prop)) (\forall (P:Prop). P)) (\forall (P:Prop). (P) -> P)) ((false) ))) (\lambda x : Prop. x)) ((((bool_discr) ((true) )) ((false) )) (Heq)))) ((False) ))).
definition notb : ((bool) ) -> (bool)  := \lambda b : (bool) . ((((match_bool_type) ((bool) )) ((false) )) ((true) )) (b).
definition andb : ((bool) ) -> ((bool) ) -> (bool)  := \lambda b1 : (bool) . \lambda b2 : (bool) . ((((match_bool_type) ((bool) )) (b2)) ((false) )) (b1).
definition andb_true_l : \forall (b1:(bool) ). \forall (b2:(bool) ). ((((eq) ((bool) )) ((((andb) ) (b1)) (b2))) ((true) )) -> (((eq) ((bool) )) (b1)) ((true) ) := \lambda b1 : (bool) . ((((match_bool_prop) (\lambda j__ : (bool) . \forall (b2:(bool) ). ((((eq) ((bool) )) ((((andb) ) (j__)) (b2))) ((true) )) -> (((eq) ((bool) )) (j__)) ((true) ))) (\lambda b2 : (bool) . (((((sym_eq_match_bool_type_true) ((bool) )) (b2)) ((false) )) (\lambda x : (bool) . ((((eq) ((bool) )) (x)) ((true) )) -> (((eq) ((bool) )) ((true) )) ((true) ))) (\lambda auto : (((eq) ((bool) )) (b2)) ((true) ). (((((((rewrite_l) ((bool) )) (b2)) (\lambda j__ : (bool) . (((eq) ((bool) )) (j__)) ((true) ))) (((((((rewrite_l) ((bool) )) (b2)) (\lambda j__ : (bool) . (((eq) ((bool) )) (b2)) (j__))) (((refl) ((bool) )) (b2))) ((true) )) (auto))) ((true) )) (auto))))) (\lambda j_b2 : (bool) . (((((sym_eq_match_bool_type_false) ((bool) )) (j_b2)) ((false) )) (\lambda x : (bool) . ((((eq) ((bool) )) (x)) ((true) )) -> (((eq) ((bool) )) ((false) )) ((true) ))) (\lambda auto : (((eq) ((bool) )) ((false) )) ((true) ). (((((((rewrite_r) ((bool) )) ((true) )) (\lambda j__ : (bool) . (((eq) ((bool) )) (j__)) ((true) ))) (((refl) ((bool) )) ((true) ))) ((false) )) (auto))))) (b1).
definition andb_true_r : \forall (b1:(bool) ). \forall (b2:(bool) ). ((((eq) ((bool) )) ((((andb) ) (b1)) (b2))) ((true) )) -> (((eq) ((bool) )) (b2)) ((true) ) := \lambda b1 : (bool) . \lambda b2 : (bool) . ((((match_bool_prop) (\lambda j__ : (bool) . ((((eq) ((bool) )) ((((andb) ) (j__)) (b2))) ((true) )) -> (((eq) ((bool) )) (b2)) ((true) ))) ((((((sym_eq_match_bool_type_true) ((bool) )) (b2)) ((false) )) (\lambda x : (bool) . ((((eq) ((bool) )) (x)) ((true) )) -> (((eq) ((bool) )) (b2)) ((true) ))) (\lambda auto : (((eq) ((bool) )) (b2)) ((true) ). (((((((rewrite_l) ((bool) )) (b2)) (\lambda j__ : (bool) . (((eq) ((bool) )) (b2)) (j__))) (((refl) ((bool) )) (b2))) ((true) )) (auto))))) ((((((sym_eq_match_bool_type_false) ((bool) )) (b2)) ((false) )) (\lambda x : (bool) . ((((eq) ((bool) )) (x)) ((true) )) -> (((eq) ((bool) )) (b2)) ((true) ))) (((((match_bool_prop) (\lambda j__ : (bool) . ((((eq) ((bool) )) ((false) )) ((true) )) -> (((eq) ((bool) )) (j__)) ((true) ))) (\lambda auto : (((eq) ((bool) )) ((false) )) ((true) ). (((refl) ((bool) )) ((true) )))) (\lambda auto : (((eq) ((bool) )) ((false) )) ((true) ). (((((((rewrite_r) ((bool) )) ((true) )) (\lambda j__ : (bool) . (((eq) ((bool) )) (j__)) ((true) ))) (((refl) ((bool) )) ((true) ))) ((false) )) (auto)))) (b2)))) (b1).
definition true_or_false : \forall (b:(bool) ). (((Or) ) ((((eq) ((bool) )) (b)) ((true) ))) ((((eq) ((bool) )) (b)) ((false) )) := \lambda b : (bool) . ((((match_bool_prop) (\lambda j__ : (bool) . (((Or) ) ((((eq) ((bool) )) (j__)) ((true) ))) ((((eq) ((bool) )) (j__)) ((false) )))) ((((or_introl) ((((eq) ((bool) )) ((true) )) ((true) ))) ((((eq) ((bool) )) ((true) )) ((false) ))) (((refl) ((bool) )) ((true) )))) ((((RC_reflexive) ((bool) )) (\lambda j__ : (bool) . \lambda j_0 : (bool) . (((eq) ((bool) )) ((false) )) ((true) ))) ((false) ))) (b).