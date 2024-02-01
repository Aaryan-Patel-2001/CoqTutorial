(**
In this exercise we implement the running example during the lecture of the
tutorial: proving that when two threads increase a reference that's initially
zero by two, the result is four.
*)
From iris.algebra Require Import excl_auth frac_auth numbers.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lib.par proofmode notation.

Local Open Scope Z.

(** The program as a heap-lang expression. We use the heap-lang [par] module for
parallel composition. *)
Definition parallel_add : expr :=
  let: "r" := ref #0 in
  ( FAA "r" #2 )
  |||
  ( FAA "r" #2 )
  ;;
  !"r".

(** 1st proof : we only prove that the return value is even.
No ghost state is involved in this proof. *)
Section proof1.
  Context `{!heapGS Σ, !spawnG Σ}.

  Definition parallel_add_inv_1 (r : loc) : iProp Σ :=
    ∃ n : Z, r ↦ #n ∗ ⌜ Zeven n ⌝.

  (** *Exercise*: finish the missing cases of this proof. *)
  Lemma parallel_add_spec_1 :
    {{{ True }}} parallel_add {{{ n, RET #n; ⌜Zeven n⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (inv_alloc nroot _ (parallel_add_inv_1 r) with "[Hr]") as "#Hinv".
    { (* exercise *) admit. }
    wp_smart_apply (wp_par (λ _, True%I) (λ _, True%I)).
    - iInv "Hinv" as (n) ">[Hr %]" "Hclose".
      wp_faa.
      iMod ("Hclose" with "[Hr]") as "_".
      { (* Re-establish invariant. *)
        iExists _. iFrame "Hr". iPureIntro. by apply Zeven_plus_Zeven. }
      (* Post-condition of this thread. *)
      done.
    - (* exercise *)
      admit.
    - (* exercise *)
      admit.
  Admitted.
End proof1.

(** 2nd proof : we prove that the program returns 4 exactly.
We need a piece of ghost state: integer ghost variables.

Whereas we previously abstracted over an arbitrary "ghost state" [Σ] in the
proofs, we now need to make sure that we can use integer ghost variables. For
this, we add the type class constraint:

  inG Σ (excl_authR ZO)

*)

Section proof2.
  Context `{!heapGS Σ, !spawnG Σ, !inG Σ (excl_authR ZO)}.

  Definition parallel_add_inv_2 (r : loc) (γ1 γ2 : gname) : iProp Σ :=
    ∃ n1 n2 : Z, r ↦ #(n1 + n2)
               ∗ own γ1 (●E n1) ∗ own γ2 (●E n2).

  (** Some helping lemmas for ghost state that we need in the proof. In actual
  proofs we tend to inline simple lemmas like these, but they are here to
  make things easier to understand. *)
  Lemma ghost_var_alloc n :
    ⊢ |==> ∃ γ, own γ (●E n) ∗ own γ (◯E n).
  Proof.
    iMod (own_alloc (●E n ⋅ ◯E n)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ n m :
    own γ (●E n) -∗ own γ (◯E m) -∗ ⌜ n = m ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %?%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update γ n' n m :
    own γ (●E n) -∗ own γ (◯E m) ==∗ own γ (●E n') ∗ own γ (◯E n').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E n' ⋅ ◯E n') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.

  (** *Exercise*: finish the missing cases of the proof. *)
  Lemma parallel_add_spec_2 :
    {{{ True }}} parallel_add {{{ RET #4; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hγ2● Hγ2◯]".
    iMod (inv_alloc nroot _ (parallel_add_inv_2 r γ1 γ2) with "[Hr Hγ1● Hγ2●]") as "#Hinv".
    { (* exercise *) admit. }
    wp_smart_apply (wp_par (λ _, own γ1 (◯E 2)) (λ _, own γ2 (◯E 2))
                with "[Hγ1◯] [Hγ2◯]").
    - iInv "Hinv" as (n1 n2) ">(Hr & Hγ1● & Hγ2●)" "Hclose".
      wp_faa.
      iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
      iMod (ghost_var_update γ1 2 with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
      iMod ("Hclose" with "[- Hγ1◯]"); [|by auto].
      iExists _, _. iFrame "Hγ1● Hγ2●". rewrite (_ : 2 + n2 = 0 + n2 + 2); [done|ring].
    - (* exercise *)
      admit.
    - (* exercise *)
      admit.
  Admitted.
End proof2.

(** 3rd proof (not shown in the talk) : we prove that the program returns 4
exactly, but using a fractional authoritative ghost state.  We need another kind
of ghost resource for this, but we only need one ghost variable no matter how
many threads there are. *)
Section proof3.
  Context `{!heapGS Σ, !spawnG Σ, !inG Σ (frac_authR ZR)}.

  Definition parallel_add_inv_3 (r : loc) (γ : gname) : iProp Σ :=
    ∃ n : Z, r ↦ #n ∗ own γ (●F n).

  (** *Exercise*: finish the missing cases of the proof. *)
  Lemma parallel_add_spec_3 :
    {{{ True }}} parallel_add {{{ RET #4; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (own_alloc (●F 0 ⋅ ◯F 0)) as (γ) "[Hγ● [Hγ1◯ Hγ2◯]]".
    { by apply auth_both_valid. }
    iMod (inv_alloc nroot _ (parallel_add_inv_3 r γ) with "[Hr Hγ●]") as "#Hinv".
    { (* exercise *) admit. }
    wp_smart_apply (wp_par (λ _, own γ (◯F{1/2} 2)) (λ _, own γ (◯F{1/2} 2))
                with "[Hγ1◯] [Hγ2◯]").
    - iInv "Hinv" as (n) ">[Hr Hγ●]" "Hclose".
      wp_faa.
      iMod (own_update_2 _ _ _ (●F (n+2) ⋅ ◯F{1/2}2) with "Hγ● Hγ1◯") as "[Hγ● Hγ1◯]".
      { apply frac_auth_update, Z_local_update. lia. }
      iMod ("Hclose" with "[Hr Hγ●]"); [|by auto].
      iExists _. iFrame.
    - (* exercise *)
      admit.
    - (* exercise *)
      admit.
  Admitted.
End proof3.
