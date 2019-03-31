Set Implicit Arguments.

Require Import LibTactics.
Require Import Arith.Arith_base List Omega.
Require Import SimpleTypes.

(* This is here just for lazyness *)
Fixpoint find_subst (s : list (id * ty)) (i : id) : option ty :=
  match s with
    | nil => None
    | (v,t') :: s' => if (eq_id_dec v i) then Some t' else find_subst s' i
  end.

Ltac s :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H
    | [ H : _ \/ _ |- _] => destruct H
    | [ |- context[eq_id_dec ?a ?b] ] => destruct (eq_id_dec a b) ; subst ; try congruence
    | [ |- context[eq_nat_dec ?a ?b] ] => destruct (eq_nat_dec a b) ; subst ; try congruence
    | [ H : context[eq_nat_dec ?a ?a] |- _ ] => destruct (eq_nat_dec a a) ; subst ; try congruence
    | [ x : (id * ty)%type |- _ ] => let t := fresh "t" in destruct x as [x t]
    | [ H : (_,_) = (_,_) |- _] => inverts* H
    | [ H : Some _ = Some _ |- _] => inverts* H
    | [ H : Some _ = None |- _] => congruence
    | [ H : None = Some _ |- _] => congruence
    | [ |- _ /\ _] => split ~
    | [ H : ex _ |- _] => destruct H
  end.

Ltac mysimp := (repeat (simpl; s)) ; simpl; auto with arith.

Ltac inversionExist :=
  match goal with
    | [ H : exist _ _ _ = exist _ _ _ |- _] => inversion H; clear H
    | [ H : existT _ _ _ = existT _ _ _ |- _] => inversion H; clear H
  end.                                                        

Hint Rewrite app_nil_r:RE.
Hint Rewrite app_nil_l:RE.
Hint Rewrite app_nil_end:Re.

Hint Rewrite app_nil_r:RELOOP.
Hint Rewrite app_nil_l:RELOOP.
Hint Rewrite app_nil_end:RELOOP.


Ltac crush' :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H
    | [ H : _ \/ _ |- _] => destruct H
    | [ x : (_ * _)%type |- _ ] => let t := fresh "t" in destruct x as [x t]
    | [ H : (_,_) = (_,_) |- _] => inverts* H
    | [ H : option _ |- _] => destruct H
    | [ H : Some _ = Some _ |- _] => inverts* H
    | [ H : Some _ = None |- _] => congruence
    | [ H : None = Some _ |- _] => congruence
    | [ H : true = false |- _] => inversion H
    | [ H : false = true |- _] => inversion H
    | [ H : ex _ |- _] => destruct H
    | [ H : sig _ |- _] => destruct H
    | [ H : sigT _ |- _] => destruct H
    | [ H :  let _ := _ in _  |- _] => simpl in H
    | [ H : context[fst (_, _)] |- _] => simpl in H
    | [ H : context[snd (_, _)] |- _] => simpl in H
    | [ H : context[_ ++ nil] |- _] => rewrite app_nil_r in H
    | [ H : context[nil ++ _] |- _] => rewrite app_nil_l in H
    | [ |- context[eq_id_dec ?a ?b] ] => destruct (eq_id_dec a b) ; subst ; try congruence
    | [ H : context[eq_id_dec ?a ?b] |- _ ] => destruct (eq_id_dec a b) ; subst ; try congruence
    | [ |- context[eq_nat_dec ?a ?b] ] => destruct (eq_nat_dec a b) ; subst ; try congruence
    | [ |- context[find_subst ?s ?a] ] => destruct (find_subst ?s ?a) ; subst ; try congruence
    | [ H : context[eq_nat_dec ?a ?a] |- _ ] => destruct (eq_nat_dec a a) ; subst ; try congruence
  end.

Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ eauto ]
  end.

Ltac rewriterP := repeat (rewriteHyp; autorewrite with RE in *).
Ltac rewriter := autorewrite with RE in *; rewriterP; eauto; fail.

Ltac crush := repeat (intros; simpl in *; try crush'; subst; eauto); eauto; try contradiction; repeat inversionExist; try splits; 
                simpl in *; try (subst; omega); try rewriter; autorewrite with RELOOP using congruence; eauto.