Set Implicit Arguments.

Require Import Schemes.
Require Import SubstSchm.
Require Import Gen.
Require Import List.
Require Import ListIds.
Require Import Context.
Require Import Typing.
Require Import NewTypeVariable.
Require Import SimpleTypes.
Require Import Subst.
Require Import MyLtacs.

Require Import LibTactics.

Inductive more_general : schm -> schm -> Prop :=
    | more_general_intro : forall sigma1 sigma2 : schm,
      (forall tau : ty, is_schm_instance tau sigma2 -> is_schm_instance tau sigma1) ->
      more_general sigma1 sigma2.

Hint Constructors more_general.

Inductive more_general_ctx : ctx -> ctx -> Prop :=
  | more_general_ctx_nil : more_general_ctx nil nil
  | more_general_ctx_cons : forall (G1 G2 : ctx) (i : id) (sigma1 sigma2 : schm),
     more_general_ctx G1 G2 -> more_general sigma1 sigma2 ->
     more_general_ctx ((i, sigma1) :: G1) ((i, sigma2) :: G2).

Hint Constructors more_general_ctx.

Lemma typing_in_a_more_general_ctx : forall (e : term) (G2 G1 : ctx) (t : ty),
    more_general_ctx G1 G2 -> has_type G2 e t -> has_type G1 e t.
Proof.
  (* hard *)
Admitted.

Hint Resolve typing_in_a_more_general_ctx.

Lemma more_general_gen_ty : forall (G1 G2 : ctx) (t : ty),
    more_general_ctx G1 G2 -> more_general (gen_ty t G1) (gen_ty t G2).
  (* ultra hard *)
Admitted.

Hint Resolve more_general_gen_ty.

Lemma more_general_ctx_refl : forall G : ctx, more_general_ctx G G.
simple induction G; auto.
intros; elim a; auto.
Qed.

Hint Resolve more_general_ctx_refl.
 