From stdpp Require Import gmap gmultiset.
From iris.algebra Require Export big_op cmra.
From iris.prelude Require Import options.

(** Option *)
Lemma big_opL_None {M : cmra} {A} (f : nat → A → option M) l :
  ([^op list] k↦x ∈ l, f k x) = None ↔ ∀ k x, l !! k = Some x → f k x = None.
Proof.
  revert f. induction l as [|x l IH]=> f //=. rewrite op_None IH. split.
  - intros [??] [|k] y ?; naive_solver.
  - intros Hl. split; [by apply (Hl 0)|]. intros k. apply (Hl (S k)).
Qed.
Lemma big_opM_None {M : cmra} `{Countable K} {A} (f : K → A → option M) m :
  ([^op map] k↦x ∈ m, f k x) = None ↔ ∀ k x, m !! k = Some x → f k x = None.
Proof.
  induction m as [|i x m ? IH] using map_ind=> /=.
  { by rewrite big_opM_empty. }
  rewrite -None_equiv_eq big_opM_insert // None_equiv_eq op_None IH. split.
  { intros [??] k y. rewrite lookup_insert_Some; naive_solver. }
  intros Hm; split.
  - apply (Hm i). by simplify_map_eq.
  - intros k y ?. apply (Hm k). by simplify_map_eq.
Qed.
Lemma big_opS_None {M : cmra} `{Countable A} (f : A → option M) X :
  ([^op set] x ∈ X, f x) = None ↔ ∀ x, x ∈ X → f x = None.
Proof.
  induction X as [|x X ? IH] using set_ind_L.
  { by rewrite big_opS_empty. }
  rewrite -None_equiv_eq big_opS_insert // None_equiv_eq op_None IH. set_solver.
Qed.
Lemma big_opMS_None {M : cmra} `{Countable A} (f : A → option M) X :
  ([^op mset] x ∈ X, f x) = None ↔ ∀ x, x ∈ X → f x = None.
Proof.
  induction X as [|x X IH] using gmultiset_ind.
  { rewrite big_opMS_empty. multiset_solver. }
  rewrite -None_equiv_eq big_opMS_disj_union big_opMS_singleton None_equiv_eq op_None IH.
  multiset_solver.
Qed.
