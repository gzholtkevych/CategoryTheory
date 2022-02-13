Require Export Utf8.
Require Import Lists.List.
Import ListNotations.


Class Category_axiomatics
        (object : Type)
        (arrow : object → object → Type)
        (id : ∀ x : object, arrow x x)
        (compose : 
                 compose x y y f (id y) = f
  ; associativity : True
        compose x x y (id x) f = f ∧ compose x y y f (id y) = f
  ; associativity :
       ∀ (x y z u : object) (f : arrow x y) (g : arrow y z) (h : arrow z u),
        (compose x z u (compose x y z f g) h) =
          (compose x y u f (compose y z u g h))
}.

Structure Category : Type := defCategory
{ object : Type
; arrow : object → object → Type
; id : ∀ x : object, arrow x x
; compose : 
     ∀ (x y z : object) (f : arrow x y) (g : arrow y z), arrow x z
; cat_cert : Category_axiomatics object arrow id compose
}.


Lemma le_refl : ∀ n : nat, n ≤ n.
Proof. constructor. Qed.

Lemma le_trans : ∀ n m k : nat, n ≤ m → m ≤ k → n ≤ k.
Proof.
  intros * H1 H2.
  induction H2 as [| m' IH2].
  - assumption.
  - inversion H1; now constructor.
Qed.

Instance nat_category_axiomatics : Category_axiomatics
  nat (fun (n m : nat) => n ≤ m) le_refl le_trans.
Proof.
  constructor.
  - intros. split. 


Definition nat_object := {f : nat * nat | fst f ≤ snd f}.
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