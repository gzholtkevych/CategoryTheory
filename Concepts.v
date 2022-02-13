Require Export Utf8.
Require Import Lists.List.
Import ListNotations.


Class Category_Axioms
        (object : Type)
        (arrow : object → object → Type)
        (id : ∀ x : object, arrow x x)
        (compose : 
          ∀ (x y z : object) (f : arrow x y) (g : arrow y z), arrow x z)
            : Prop :=
  { id_is_id : ∀ (x y : object) (f : arrow x y), 
                 compose x x y (id x) f = f /\
                 compose x y y f (id y) = f
  ; associativity : True
}.


Module CAT.
Structure Quiver : Type := dfCat
  { object : Type
  ; arrow : Type
  ; src : arrow → object
  ; trg : arrow → object
  ; id : object -> arrow
}.

Record Composition {q : Quiver} (f g : arrow q) := defComposition
  { _ : trg q f = src q g
  ; ra : arrow q
  ; _ : src q ra = src q f /\ trg q ra = trg q g
}.

Definition compose
             {q : Quiver}
             (f g : arrow q)
             {c : @Composition q f g} : arrow q := ra f g c.


Class Category_Axioms 
        {q : Quiver}
        {c : ∀ f g : arrow q, Composition f g } : Prop :=
{ id_src_cert : ∀ x : object q, src q (id q x) = x /\ trg q (id q x) = x
; id_law_cert : ∀ f : arrow q,
    @compose q f (id q (src q f)) (c f (id q (src q f))) = f /\
    @compose q (id q (trg q f)) f (c (id q (trg q f)) f) = f
; associativity_law : ∀ f g h : arrow q,
    let gf := @compose q f g (c f g) in
    let hg := @compose q g h (c g h) in
    @compose q gf h (c gf h) = @compose q f hg (c f hg)
}.
End CAT.

Notation Quiver := CAT.Quiver  (only parsing).

Definition nat_quiver := {f : nat * nat | fst f ≤ snd f}.
Definition nat_src (f : nat_arrow) : nat
:= match f with exist _ sf _ => fst sf end.
Definition nat_trg (f : nat_arrow) : nat
:= match f with exist _ sf _ => snd sf end.
Definition nat_id (n : nat) : nat_arrow
:= exist _ (n, n) (le_n n).

Lemma le_trans : ∀ n m k : nat, n≤ m → m ≤ k → n ≤ k.
Proof.
  intros * Hnm Hmk.
  induction Hmk as [ | m' nm'].
  - assumption.
  - inversion IHnm' as [| m'']; repeat constructor. assumption.
Qed.
Lemma nat_compose_cert : ∀ n m k l : nat, n ≤ m → m = k → k ≤ l → n ≤ l.
Proof.
  intros * H1 H2 H3. rewrite H2 in H1.
  now apply le_trans with k.
Qed.

Definition nat_compose (f g : nat_arrow) : nat_trg f = nat_src g -> nat_arrow.
Proof.
  intro.
  destruct f as [fv Hf]. destruct g as [gv Hg]. simpl in H.
  assert ( Hgf : fst fv ≤ snd gv). {
    now apply nat_compose_cert with (snd fv) (fst gv). }
  now exists (fst fv, snd gv).
Defined.

Definition Nat := {|
  object := nat;  arrow := nat_arrow;
  src := nat_src; trg := nat_trg;
  id := nat_id;   compose := nat_compose
|}.