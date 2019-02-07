Set Implicit Arguments.

Require Import Unify.
Require Import Schemes.
Require Import List.
Require Import ListIds.
Require Import Context.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.

Require Import LibTactics.

Inductive new_tv_ty : ty -> id -> Prop :=
| new_tv_con : forall i i' : id, new_tv_ty (con i') i
| new_tv_var : forall i i' : id, i < i' -> new_tv_ty (var i) i'
| new_tv_arrow : forall (tau tau' : ty) (i : id), new_tv_ty tau i ->
                                             new_tv_ty tau' i ->
                                             new_tv_ty (arrow tau tau') i.

Inductive new_tv_schm : schm -> id -> Prop :=
| new_tv_sc_con : forall i i' : id, new_tv_schm (sc_con i') i
| new_tv_sc_var : forall i i' : id, i < i' -> new_tv_schm (sc_var i) i'
| new_tv_sc_gen : forall i i' : id, new_tv_schm (sc_gen i') i
| new_tv_sc_arrow : forall (tau tau' : schm) (i : id), new_tv_schm tau i ->
                                               new_tv_schm tau' i ->
                                               new_tv_schm (sc_arrow tau tau') i.

Inductive new_tv_ctx : ctx -> id -> Prop :=
| new_tv_ctx_nil : forall i : id, new_tv_ctx nil i
| new_tv_ctx_cons : forall (G : ctx) (i x : id) (sigma : schm),
                            new_tv_ctx G i ->
                            new_tv_schm sigma i ->
                            new_tv_ctx ((x, sigma) :: G) i.

Inductive new_tv_subst : substitution -> id -> Prop :=
| new_tv_subst_intro : forall (i : id) (s : substitution),
                  (forall x : id, in_list_id x (FV_subst s) = true -> x < i) ->
                  new_tv_subst s i.


Lemma new_tv_compose_subst : forall (s1 s2 : substitution) (i : id),
                             new_tv_subst s1 i ->
                             new_tv_subst s2 i ->
                             new_tv_subst (s1 ++ s2) i.
Admitted.

