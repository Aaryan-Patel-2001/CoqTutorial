From iris.heap_lang Require Import proofmode notation.
From iris.unstable.heap_lang Require Import interpreter. 
From stdpp Require Import sorting. 

Local Open Scope Z_scope.

(** Heaplang -> Imperative 
Coq -> Functional 

Linked List: (value, pointer), where pointer points to the next element 

l: Original list [v, l2] 
l2: None or l3
l3: Sub-list [y, l3]

ref ("i", ref ())
 *)

(*
match: "l2" with
   NONE => (if: ("x" ≤ "i")%E then "p" <- SOME ("x", ref ( SOME ("i", NONE)) ) else "p" <- SOME ("i", ref (SOME ("x", NONE))) )
   | SOME "l3" => 
    let: "y" := Fst !"l3" in  (* Second element *)
    (if: (("x" ≤ "i")%E  && ("i" ≤ "y"))%E then "p" <- SOME("x", ref(SOME("i", ref(SOME("y", NONE)))))
    else "p" <- SOME ("x",  "insert" "i" "l"))
   end
*)

(* list A := option (ref (A * list A)) *)

(* insert i into its sorted place in list l *)
Definition insert : val := 
 rec: "insert" "i" "l" := 
  match: "l" with           (* A list is either... *)
  NONE => SOME( ref( "i", NONE))             (* ... the empty list *)
  | SOME "p" => 
   let: "x" := Fst !"p" in  (* First element - !e means  Load e%E *)
   let: "l2" := Snd !"p" in  (* Rest of the list *)
   (if: ("i" ≤ "x")%E then  SOME(ref("i", "l"))
   else SOME(ref("x", "insert" "i" "l2")))
  end.

Definition sort : val := 
 rec: "sort" "l" := 
  match: "l" with 
  NONE => NONE
  | SOME "p" =>
  let: "x" := Fst !"p" in 
  let: "l" := Snd !"p" in 
  "insert" "x" "sort l"
  end. 

(* Definition EmptyList: Prop :=
  rec: "EmptyList" "l" := 
    match: "l" with 
    NONE => True 
    | SOME "p" => False
    end.  *)
 



(* Section Test. 

Theorem interpretTest : interpret 1000 ("l" = "EmptyList";; "insert" "l" "5") = ("5"). 
Proof. 
  reflexivity. Qed. 


End Test.  *)

Section proof.
Context `{!heapGS Σ}.

 (* l stores a linked list with head value of v *)
Fixpoint is_list (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => ⌜ v = NONEV ⌝
  | x :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                 ∃ v' : val, p ↦ (#x, v') ∗ is_list l' v'
  end.

(* l stores a sorted linked list with head value of v *)
Fixpoint sort_spec (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => True 
  | x :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
               ∃ (n : Z), ⌜ v = #n ⌝ ∗
                match l' with 
                | [] => True 
                | y :: l'' => ∃ v' : val, p ↦ (#x, v') ∗ 
                ∃ (n' : Z), ⌜ v' = #n' ⌝ ∗
                ⌜ (n ≤ n')%Z⌝ ∗ 
                sort_spec l' v' 
                end 
  end. 

(* Coq level functional program *)
Fixpoint insert_func (i : Z) (l : list Z) :=
  match l with
  | []  => [i]
  | h :: t  => if bool_decide (i <= h)%Z then i :: h :: t else h :: insert_func i t
  end.  



(* Definition sorted (l: list Z) := ∀ i j:nat,
    i < j < length l →
    (nth i l 0) ≤ (nth j l 0). *)

(* Coq-level definition of Sorted from standard library modified to support integers Z *)

Check Sorted.

About Sorted. 

(* list l is sorted. Insert i into the sorted list *)

Lemma insertTest l:
  {{{⌜ l = NONE ⌝}}}
  insert #2 NONE 
  {{{v',RET v'; is_list  [2]  v'  }}}.
Proof.
   iIntros (Φ) "Hl Post".
   unfold insert.
   wp_pures.

   wp_alloc g as "H".
   wp_pures. 
   iModIntro. 
   iApply "Post".
   simpl.
   iDestruct "Hl" as %->. 
   iExists _. 
   iSplit.
   - iPureIntro. reflexivity.
   - iExists NONEV. iFrame. iPureIntro.  reflexivity.
   Qed. 

Lemma insert_func_hdrel : forall (i x : Z) (l : list Z),
  HdRel Z.le x (insert_func i l).
Proof.
  intros i x l.
  (* Induction on l *)
  induction l as [| y l' IHl].
  - (* Base case: l = [] *)
    simpl.
    admit. 
    (* Prove the base case *)
    (* You may need additional lemmas or properties here *)
    (* It might involve proving that x is less than or equal to the inserted element *)
  - (* Inductive case: l = y :: l' *)
    simpl.
    admit. 
    (* Prove the inductive step *)
    (* Use properties of insert_func, HdRel, and Z.le here *)
    (* You may need to use transitivity of Z.le *)
Admitted.

Lemma insert_proof l v (i:Z): 
  {{{ ⌜Sorted (≤) l⌝ ∗  is_list l v }}}
  insert #i v
  {{{v',RET v'; is_list (insert_func i l) v' ∗ ⌜ Sorted (≤) (insert_func i l) ⌝}}}.  
Proof. 
  (* Proof *)
  iIntros (Φ) "Hl Post".
  iDestruct "Hl" as (Heq)  "Hl". 
  iInduction l as [|x l] "IH" forall (v Φ); simpl.
  - iDestruct "Hl" as %->.
    wp_rec. wp_let. wp_match.
    wp_alloc g as "H".
    wp_pures.
    iModIntro. 
    iApply "Post".
    iSplitL "H".
    {iExists g. iSplitR "H". {iPureIntro. reflexivity.} { iExists NONEV. iFrame. iPureIntro.  reflexivity.}}
    {iPureIntro. apply Sorted_cons. {apply Sorted_nil.} { auto. } }
  - iDestruct "Hl" as (p) "[-> Hl]". iDestruct "Hl" as (v) "[Hp Hl]".
    wp_rec. wp_let. wp_match. wp_load. wp_proj.
    wp_let. wp_load. wp_proj. wp_let.
    wp_pure.  case_bool_decide. 
    + wp_if_true. wp_alloc g as "list". wp_pures.
      iModIntro.
      iApply "Post".
      iSplit.
      { simpl. eauto 10 with iFrame. }
      { iPureIntro. apply Sorted_cons. {exact.} {apply HdRel_cons. exact. } }
    + wp_if_false.  wp_apply ("IH" with" [] [$Hl]").
      { iPureIntro. admit.  }
      { iIntros (v') "[islist %HS]". wp_alloc g as "list". wp_pures. iModIntro. iApply "Post". iSplit. { simpl. eauto 10 with iFrame.} {iPureIntro. apply Sorted_cons. { exact.
} {simpl. apply insert_func_hdrel.} }  }

Admitted. 



Lemma sort_proof l v:
  {{{is_list l v}}}
   sort v
  {{{RET #(); ⌜Sorted l⌝}}}. 
Proof. 
  iIntros (Φ) "Hl Post".
  iInduction l as [|x l] "IH" forall (v Φ); simpl.
  - iDestruct "Hl" as %->.
    wp_rec.
    wp_pures.
    iModIntro.  
    iApply "Post".
    iPureIntro.
    apply Sorted_nil.
  - iDestruct "Hl" as (p) "[-> Hl]". iDestruct "Hl" as (v) "[Hp Hl]".
    wp_rec.
    wp_match.
    wp_load. wp_proj. wp_let.
    wp_load. wp_proj. wp_let.
    wp_apply ("insert_proof" with )
    wp_apply ("IH" with "Hl"). 
    
    iApply insert_proof. 

Admitted. 

End proof. 
