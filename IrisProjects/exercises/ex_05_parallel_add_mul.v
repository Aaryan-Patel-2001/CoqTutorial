(**
In this exercise we consider a variant of the previous exercise. We have a
reference which is initially 0 and two threads running in parallel. One thread
increases the value of the reference by 2, whereas the other multiples the
value of the reference by two. An interesting aspect of this exercise is that
the outcome of this program is non-deterministic. Depending on which thread runs
first, the outcome is either 2 or 4.

There is no "fetch-and-multiply" operation in heap_lang, so we use the spin lock
from exercise 3 instead to make both the addition and the multiplication atomic.

Contrary to the earlier exercises, this exercise is nearly entirely open.
*)
From iris.algebra Require Import excl_auth frac_auth.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par.
From exercises Require Import ex_03_spinlock.

Definition parallel_add_mul : expr :=
  let: "r" := ref #0 in
  let: "l" := newlock #() in
  (
    (acquire "l";; "r" <- !"r" + #2;; release "l")
  |||
    (acquire "l";; "r" <- !"r" * #2;; release "l")
  );;
  acquire "l";;
  !"r".

(** In this proof we will make use of Boolean ghost variables. *)
Section proof.
  Context `{!heapGS Σ, !spawnG Σ, !inG Σ (excl_authR boolO)}.

  (** The same helping lemmas for ghost variables that we have already seen in
  the previous exercise. *)
  Lemma ghost_var_alloc b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %<-%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.

  (** *Difficult exercise*: come up with a suitable invariant and prove the spec
  of [parallel_add_mul]. In this proof, you should use Boolean ghost variables,
  and the rules for those as given above. You are allowed to use any number of
  Boolean ghost variables. *)
  Definition parallel_add_mul_inv (r : loc) (γ1 γ2 : gname) : iProp Σ :=
    True. (* exercise: replace [True] with something meaningful. *)

  Lemma parallel_add_mul_spec :
    {{{ True }}} parallel_add_mul {{{ z, RET #z; ⌜ z = 2%Z ∨ z = 4%Z ⌝ }}}.
  Proof.
    (* exercise *)
  Admitted.
End proof.
