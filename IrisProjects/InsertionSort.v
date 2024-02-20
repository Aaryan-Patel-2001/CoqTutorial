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

(* insert i into its sorted place in list l *)
Definition insert : val := 
 rec: "insert" "i" "l" := 
  match: "l" with           (* A list is either... *)
  NONE => ref (SOME( "i", NONE) )             (* ... the empty list *)
  | SOME "p" => 
   let: "x" := Fst !"p" in  (* First element - !e means  Load e%E *)
   let: "l2" := Snd !"p" in  (* Rest of the list *)
   match: "l2" with
   NONE => (if: ("x" ≤ "i")%E then "p" <- ref (SOME ("x", ("i", NONE))) else "p" <- ("i", ("x", NONE)) )
   | SOME "l3" => 
    let: "y" := Fst !"l3" in  (* Second element *)
    (if: (("x" ≤ "i")%E  && ("i" ≤ "y"))%E then "p" <- ("x",  ("i"  "l") )
    else "p" <- ("x",  "insert" "i" "l"))
   end 
  end.

Definition sort : val := 
 rec: "sort" "l" := 
  match: "l" with 
  NONE => #()
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
  | h :: t  => if (i <=? h)%Z then i :: h :: t else h :: insert_func i t
  end.  



(* Definition sorted (l: list Z) := ∀ i j:nat,
    i < j < length l →
    (nth i l 0) ≤ (nth j l 0). *)

(* Coq-level definition of Sorted from standard library modified to support integers Z *)
Variable R : Z -> Z -> Prop.

Inductive HdRel a : list Z -> Prop :=
    | HdRel_nil : HdRel a []
    | HdRel_cons b l : R a b -> HdRel a (b :: l).

Inductive Sorted : list Z -> Prop :=
    | Sorted_nil : Sorted []
    | Sorted_cons a l : Sorted l -> HdRel a l -> Sorted (a :: l).

(* list l is sorted. Insert i into the sorted list *)

Lemma insertTest l:
  {{{⌜ l = NONE ⌝}}}
  insert #2 NONE 
  {{{v',RET v'; is_list [2] v'}}}.
Proof.
   iIntros (Φ) "Hl Post".
   unfold insert.
   wp_pures.

   wp_alloc g as "H".
   iModIntro.
   iApply "Post".
   unfold is_list.
   iExists g.
   iSplitR "H".
   - iPureIntro. reflexivity.          


  Admitted. 

Lemma insert_proof l v (i:Z): 
  {{{is_list l v}}}
  insert #i v
  {{{v',RET v'; is_list (insert_func i l) v' ∗ ⌜ Sorted (insert_func i l) ⌝}}}.  
Proof. 
  (* Proof *)
  iIntros (Φ) "Hl Post".
  unfold insert.
  wp_rec.
  wp_let.
  unfold insert_func.

  iInduction l as [|x l] "IH" forall (v Φ); simpl.
  - iDestruct "Hl" as %->.
     wp_pures. 
     wp_alloc l as "H".
     iModIntro.  
     iApply "Post". 
  (* - iDestruct "Hl" as (p) "[-> Hl]". iDestruct "Hl" as (v) "[Hp Hl]".  *)
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
