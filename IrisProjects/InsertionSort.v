From iris.heap_lang Require Import proofmode notation.
From iris.unstable.heap_lang Require Import interpreter. 

Definition comp : expr := 
 "x" ≤ "i". 


(* insert i into its sorted place in list l *)
Definition insert : val := 
 rec: "insert" "i" "l" := 
  match: "l" with           (* A list is either... *)
  NONE => ("i", "NONE")              (* ... the empty list *)
  | SOME "p" => 
   let: "x" := Fst !"p" in  (* First element *)
   let: "l2" := Snd !"p" in  (* Rest of the list *)
   match: "l2" with
   NONE => (if: ("x" ≤ "i")%E then "p" <- ("i", ("x", "NONE")) else "p" <- ("x", ("i", "NONE")) )
   | SOME "l3" => 
    let: "y" := Fst !"l3" in  (* Second element *)
    (if: (("x" ≤ "i")%E  && ("i" ≤ "y"))%E then "p" <- ("x",  ("i"  "l") )
    else "p" <- ("x",  "insert" "i" "l"))
   end 
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

Definition EmptyList : expr := 
  NONE. 
 
Section Test. 

Theorem interpretTest : interpret 1000 ("l" = "EmptyList";; "insert" "l" "5") = ("5"). 
Proof. 
  reflexivity. Qed. 


End Test. 

Section proof.
Context `{!heapGS Σ}.

 
Fixpoint is_list (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => ⌜ v = NONEV ⌝
  | x :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                 ∃ v' : val, p ↦ (#x, v') ∗ is_list l' v'
  end.

Lemma sort_spec l v:
  (* Precondition: A valid array of length v *)
  {{{is_list l v}}}
  sort l
  {{{RET #();}}} 
Proof. 


End proof. 
