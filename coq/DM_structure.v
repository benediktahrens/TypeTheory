
(** * (Pre)categories with families *)
(**
  Contents:

    - Definition of a precategory with families

  The definition is based on Pitts, *Nominal Presentations of the Cubical Sets
  Model of Type Theory*, Def. 3.1: 
  http://www.cl.cam.ac.uk/~amp12/papers/nompcs/nompcs.pdf (page=9)
*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.
Require Export UniMath.RezkCompletion.precategories.
Require Export UniMath.RezkCompletion.limits.pullbacks.

Module Record_Preview.

Reserved Notation "C ⟨ Γ ⟩" (at level 60).
Reserved Notation "C ⟨ Γ ⊢ A ⟩" (at level 60).
Reserved Notation "A [ γ ]" (at level 40).
Reserved Notation "a ⟦ γ ⟧" (at level 40).
Reserved Notation "Γ ∙ A" (at level 20).
Reserved Notation "'π' A" (at level 20).
Reserved Notation "'ν' A" (at level 15).
Reserved Notation "γ ♯ a" (at level 25).

(* TODO *)

End Record_Preview.


Definition dm_sub_struct (CC : precategory)
  : UU
  := ∀ {Δ Γ : CC} , Δ ⇒ Γ → UU.

Definition DM_type {C : precategory} (H : dm_sub_struct C) {Δ Γ} (γ : Δ ⇒ Γ)
           := H Δ Γ γ.

Definition DM {C : precategory}(H : dm_sub_struct C) (Δ Γ : C) : UU :=
  Σ f : Δ ⇒ Γ, DM_type H f.

Coercion arrow_from_DM {C : precategory} (H : dm_sub_struct C)(Δ Γ : C) (δ : DM H Δ Γ) : Δ ⇒ Γ := pr1 δ.

Definition dm_sub_closed_under_iso {CC : precategory} (C : dm_sub_struct CC)
  : UU
  := ∀ Δ Γ (γ : DM C Δ Γ),
                          ∀ Δ' (δ : Δ' ⇒ Γ), 
                          ∀ (h : iso Δ Δ'), h ;; δ = γ → DM_type C δ.


(*

  __________Γ
 |          |
 |          | γ ∈ DM
 |__________|
 Δ    f     Γ'

*)


Definition pb_of_DM_struct {CC : precategory} (H : dm_sub_struct CC)
: UU
  := ∀ Δ Γ (γ : DM H Δ Γ), ∀ Γ' (f : Γ' ⇒ Γ),
       Σ P : Pullback _ γ f, DM_type H (pr2 (pr2 (pr1 P))).

(*
Definition pb_type_of_DM {CC : precategory} (H : dm_sub_struct CC)
           {Δ Γ} (γ : DM H Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
  : UU
  := 
    Σ (pfg : Σ Δ' : CC, Δ' ⇒ Δ × DM H Δ' Γ') (H : pr1 (pr2 pfg);; γ = pr2 (pr2 pfg);; f),
           isPullback _ _ _  (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H .
 *)

(*
Definition Pullback_of_pb_type {CC : precategory} (sat : is_category CC) (H : dm_sub_struct CC)
      {Δ Γ} (γ : DM H Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  pb_type_of_DM _ γ f → Pullback _ γ f.
Proof.
  intros [[P [f' g]] p]; simpl in *.
  refine (tpair _ _ _ ).
  - exists P.
    exists f'.
    exact g.
  - simpl. exact p.
Defined.  
*)
(*
Search (isofhlevel _ _ -> isofhlevel _ _ ).
*)

(*
Definition pb_type_of_DM_weq_Pb {CC : precategory} (sat : is_category CC) (H : dm_sub_struct CC)
      {Δ Γ} (γ : DM H Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  (∀ Γ Γ' (γ : Γ ⇒ Γ'), isaprop (DM_type H γ)) →
   isaprop (pb_type_of_DM _ γ f).
Proof.
  intros.
  apply invproofirrelevance.
  intros Pb Pb'.
  apply total2_paths_isaprop.
  - intro; apply isofhleveltotal2.
    + apply (pr2 sat).
    + intros; apply isaprop_isPullback.
  - apply (total2_paths (isotoid _ sat (iso_from_Pullback_to_Pullback _ Pb Pb' ))).
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in ×.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in ×.
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
 *)

(*
Definition pb_type_of_DM_weq_Pb {CC : precategory} (sat : is_category CC) (H : dm_sub_struct CC)
      {Δ Γ} (γ : DM H Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  (∀ Γ Γ' (γ : Γ ⇒ Γ'), isaprop (DM_type H γ)) →
   isaprop (pb_type_of_DM _ γ f).
Proof.
  intros.
  intros a b.
  apply (isofhlevelsninclb _ (Pullback_of_pb_type sat H γ f)).
  unfold isincl.
  unfold isofhlevelf.
  intro x.
  unfold hfiber.
  apply invproofirrelevance.
  intros P P'.
  apply total2_paths_second_isaprop.
  + apply isapropifcontr. apply isaprop_Pullback. assumption.
  + destruct P as [P PX]; destruct P' as [P' PX']. simpl in *.
    apply total2_paths_second_isaprop.
    * apply (isofhleveltotal2). apply (pr2 sat).
      intros. apply isaprop_isPullback.
    *  assert (A :  Pullback_of_pb_type sat H γ f P =  Pullback_of_pb_type sat H γ f P').
       { etrans. apply PX. sym. apply PX'. }
       clear PX. clear PX'.
       assert (T := maponpaths (pr1) A).
       clear X. clear x. clear A.
       simpl in *.
      destruct P as [P1 X1 ]. simpl.
      destruct P' as [P1' X1']. simpl in *.  
      refine (total2_paths _ _  ).
      apply (maponpaths).
      refine (total2_paths _ _ ).
      revert T.
      destruct P1 as [P1 P2].
      destruct P1' as [P1' P2']. simpl in *.
      apply (maponpaths _ T) .
      clear X1.
      clear PX. clear PX'.
  destruct P as [
  intros.
  intro H'.
  apply invproofirrelevance.
  intros Pb Pb'.
  apply total2_paths_isaprop.
  - intro; apply isofhleveltotal2.
    + apply (pr2 sat). 
    + intros; apply isaprop_isPullback.
  - apply (total2_paths (isotoid _ sat (iso_from_Pullback_to_Pullback _   Pb Pb' ))).
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in ×.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in ×.
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
Qed.
   pb_type_of_DM _ γ f ≃ Pullback _ γ f.
Proof.
  intro H'.
  unfold pb_type_of_DM, Pullback.
  refine (weqbandf _ _ _ _ ).
  - apply weqfibtototal.
    intro Δ'.
    apply weqfibtototal.
    intro.
    exists (pr1).
    Search (isweq pr1).
    apply isweqpr1.
    
  - 
  simpl.
  eapply weqcomp.
*)
(*
Definition pb_of_DM_struct {CC : precategory} (H : dm_sub_struct CC)
: UU
  := ∀ Δ Γ (γ : DM H Δ Γ) Γ' (f : Γ' ⇒ Γ), pb_type_of_DM H γ f.
*)
(*
    Σ (pfg : Σ Δ' : CC, Δ' ⇒ Δ × DM H Δ' Γ') (H : pr1 (pr2 pfg);; γ = pr2 (pr2 pfg);; f),
           isPullback _ _ _  (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H .
*)
Definition dm_sub_pb (CC : precategory) : UU :=
  Σ DM : dm_sub_struct CC, pb_of_DM_struct DM.

Coercion dm_sub_of_dm_sub_pb {CC : precategory} (C : dm_sub_pb CC) : dm_sub_struct CC := pr1 C.
Coercion pb_of_dm_sub_pb {CC : precategory} (C : dm_sub_pb CC) : pb_of_DM_struct C := pr2 C.


Definition pb_ob_of_DM {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: CC
  := pr1 (pr1 (pr1 (pr2 C _ _ γ _  f))).

Notation "γ ⋆ f" := (pb_ob_of_DM γ f) (at level 45, format "γ ⋆ f").
(* written "\st" in Agda input mode *)
                        
Definition pb_mor_of_DM {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  (γ⋆f) ⇒  Γ'
:=  pr2 (pr2 (pr1 (pr1 (pr2 C _ _ γ _ f)))).

Definition pb_mor_of_mor {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: γ⋆f ⇒ Δ
  := pr1 (pr2 (pr1 (pr1 (pr2 C _ _ γ _ f)))).

Definition sqr_comm_of_dm_sub_pb {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: _ ;; _ = _ ;; _
:= pr1 ((pr2 (pr1 (pr2 C _ _ γ _ f )))).

Definition isPullback_of_dm_sub_pb {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: isPullback _ _ _ _ _ _
:=  pr2 (pr2 (pr1 (pr2 C _ _ γ _ f ))).

(*
Definition dm_closed_under_pb {CC : precategory} (C : dm_sub_pb CC)
: UU
    := ∀ Δ Γ (γ : DM C Δ Γ) Γ' (f : Γ' ⇒ Γ), DM_type C (pb_mor_of_DM γ f).
*)

Definition DM_structure (CC : precategory) : UU
  := Σ C : dm_sub_pb CC,
   (*        dm_closed_under_pb C *)
          dm_sub_closed_under_iso C
        ×  ∀ Γ Γ' (γ : Γ ⇒ Γ'), isaprop (DM_type C γ).

Coercion dm_sub_pb_from_DM_structure CC (C : DM_structure CC) : dm_sub_pb CC := pr1 C.


Definition pb_DM_of_DM {CC} {C : DM_structure CC}  {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: DM C (γ⋆f) Γ'.
Proof.
  exists (pb_mor_of_DM γ f).
  apply ( pr2 (pr2 (pr1 C) _ _ γ _ f)). 
Defined.


Definition pb_arrow_of_arrow {CC} {C : DM_structure CC}  {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: γ⋆f ⇒ Δ.
Proof.
  apply pb_mor_of_mor.
Defined.

Definition sqr_comm_of_DM {CC} {C : DM_structure CC}  {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  pb_arrow_of_arrow _ _  ;; γ = pb_DM_of_DM γ f  ;; f.
Proof. 
  apply sqr_comm_of_dm_sub_pb.
Defined.

Definition isPullback_of_DM {CC} {C : DM_structure CC} {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: isPullback CC _ _ _ _ (sqr_comm_of_DM γ f).
Proof.
  apply isPullback_of_dm_sub_pb.
Defined.
