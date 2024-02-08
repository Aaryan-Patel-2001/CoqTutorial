From iris.heap_lang Require Import proofmode notation.
From iris.unstable.heap_lang Require Import interpreter. 
From stdpp Require Import sorting. 

Local Open Scope Z_scope.

Definition comp : expr := 
 "x" ≤ "i". 


(* insert i into its sorted place in list l *)
Definition insert : val := 
 rec: "insert" "i" "l" := 
  match: "l" with           (* A list is either... *)
  NONE => ("i", NONE)              (* ... the empty list *)
  | SOME "p" => 
   let: "x" := Fst !"p" in  (* First element *)
   let: "l2" := Snd !"p" in  (* Rest of the list *)
   match: "l2" with
   NONE => (if: ("x" ≤ "i")%E then "p" <- ("i", ("x", NONE)) else "p" <- ("x", ("i", NONE)) )
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

Definition EmptyList : expr := 
  NONE. 



(* Section Test. 

Theorem interpretTest : interpret 1000 ("l" = "EmptyList";; "insert" "l" "5") = ("5"). 
Proof. 
  reflexivity. Qed. 


End Test.  *)

Section proof.
Context `{!heapGS Σ}.

 
Fixpoint is_list (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => ⌜ v = NONEV ⌝
  | x :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                 ∃ v' : val, p ↦ (#x, v') ∗ is_list l' v'
  end.

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


Fixpoint insert_func (i : Z) (l : list Z) :=
  match l with
  | []  => [i]
  | h :: t  => if (i <=? h)%Z then i :: h :: t else h :: insert_func i t
  end.  


(* Definition sorted (l: list Z) := ∀ i j:nat,
    i < j < length l →
    (nth i l 0) ≤ (nth j l 0). *)

Variable R : Z -> Z -> Prop.

Inductive HdRel a : list Z -> Prop :=
    | HdRel_nil : HdRel a []
    | HdRel_cons b l : R a b -> HdRel a (b :: l).


Inductive Sorted : list Z -> Prop :=
    | Sorted_nil : Sorted []
    | Sorted_cons a l : Sorted l -> HdRel a l -> Sorted (a :: l).

Lemma insert_proof l v (i:Z): 
  {{{is_list l v}}}
  insert v #i 
  {{{RET #(); is_list (insert_func i l) v ∗ ⌜ Sorted (insert_func i l) ⌝ }}}.  
Proof. 
  (* Proof *)
  iIntros (Φ) "Hl Post".
  wp_rec.
  wp_pures.   
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

Admitted. 

End proof. 
