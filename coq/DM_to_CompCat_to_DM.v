(** 
 
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Definition of a Category with Display maps from a Comprehension Category
      (assumption of saturatedness needed for pullbacks forming hprop)
*)


Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCat.
Require Import Systems.DM.
Require Import Systems.DM_to_CompCat.
Require Import Systems.CompCat_to_DM.

(** * Construction of Comprehension precategory from Display map precategory *)

Section CompCat_to_DM.

Variable CC : precategory.
Variable H : is_category CC.  
Variable C : DM_structure CC.

Lemma DM_to_CompCat_to_DM : DM_structure_of_CompCat _ H (comp_cat_struct_from_DM _ C) = C.
Proof.
  apply DM_equal.
  - assumption.
  - intros. unfold DM_structure_of_CompCat in X.
    simpl in *.
    unfold DM_type in X. simpl in *.
    unfold dm_sub_struct_of_CompCat in X; simpl in X.
    unfold comp_cat_struct_from_DM in X. simpl in *.
    set (X' := hProppair (DM_type C f) (pr2 (pr2 C) _ _ _ )).
    apply (X X'). unfold X'; clear X' X.
    intro T. simpl in *.
    unfold iso_to_dpr in T. simpl.
    destruct T.
    destruct t.
    simpl in *.
    apply 
    
End CompCat_to_DM.