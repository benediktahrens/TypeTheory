(**
Limits
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations. 


Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Section Auxiliary.

(* TODO: upstream into definition of cone in UniMath. *)
Definition forms_cone 
    {C : precategory} {g : graph} (d : diagram g C)
    (c : C) (f : ∏ (v : vertex g), C⟦c, dob d v⟧)
  : UU
:= ∏ (u v : vertex g) (e : edge u v),
     f u · dmor d e = f v.

Coercion coneOut : cone >-> Funclass.

End Auxiliary.

Section Creates_Limits.

(* TODO: consider implicitness of argument *)
Definition creates_limit
  {C : Precategory}
  (D : disp_precat C)
  {J : graph} (F : diagram J (total_precat D))
  {x : C} (L : cone (mapdiagram (pr1_precat D) F)  x)
  (isL : isLimCone _ x L) : UU
:= 
  ∑ (CC : iscontr 
      ( ∑ (d : D x)
          (δ : ∏ j : vertex J, d -->[L j] (pr2 (dob F j))),
          forms_cone F (x,,d)  (λ j, (L j ,, δ j))))
  , isLimCone _ _ (mk_cone _ (pr2 (pr2 (iscontrpr1 CC)))).
         
Definition creates_limits {C : Precategory} (D : disp_precat C) : UU
:= 
  ∏ {J : graph} (F : diagram J (total_precat D))
    {x : C} (L : cone (mapdiagram (pr1_precat D) F)  x)
    (isL : isLimCone _ x L),
  creates_limit _ _ _ isL.

End Creates_Limits.

Section creates_preserves.

Context {C : Precategory}
        (D : disp_precat C)
        (H : creates_limits D)
        (J : graph)
        (X : Lims_of_shape J C).

Notation π := (pr1_precat D).

Definition total_limits : Lims_of_shape J (total_precat D).
Proof.
  intro d.
  set (πd := mapdiagram π d).
  set (LL := X πd).
  set (L := pr1 LL).
  set (c := pr1 L).
  set (isL := pr2 LL). cbn in isL.
  set (XR := H _ d _ _ isL).
  unfold creates_limit in XR.
  cbn.
  use (mk_LimCone _ _ _ (pr2 XR)).
Defined.

Lemma pr1_preserves_limit (d : diagram J (total_precat D)) 
  (x : total_precat D) (CC : cone d x) : preserves_limit π _ x CC. 
Proof.
  intro H1.
  set (XR := X (mapdiagram π d)).
  set (L := pr1 XR).
  set (isL := pr2 XR). cbn in isL.
  set (foo := H _ _ _ _ isL).
  unfold creates_limit in foo.
  cbn in foo.
  unfold Lims_of_shape in X.
  set (R := mapdiagram π d).
  specialize (X R).
  destruct X as [[c L] LL]. cbn in *.
  set (XR:= H
  cbn.
  


           

Section classical_def_of_creating_limits.

Context {A C : Precategory}
        (F : functor A C).

Definition c_creates_limit (J : graph) (D : diagram J A) 
           (c : C) (L : cone (mapdiagram F D) c) (isL : isLimCone _ _ L) : UU
  := ∑ (CC : iscontr
               (∑ (a : A) (δ : ∏ j : vertex J, a --> dob D j), 
               forms_cone D _ δ
               × ∑ (e : F a = c), 
                   ∏ j, (#F)%cat (δ j) =  transportb (fun x => x --> _ ) e (L j) )
       ),
     isLimCone _ _ (mk_cone _ (pr1 (pr2 (pr2 (iscontrpr1 CC)))))              
.



End classical_def_of_creating_limits.

(*
Lemma impl (C : Precategory) (D : disp_precat C) 
      {J : graph} (F : diagram J (total_precat D))
      {c : C} 
      (L : cone (mapdiagram (pr1_precat D) F) c)
      (isL : isLimCone _ c L) : 
  creates_limit D F L isL → c_creates_limit (pr1_precat D) J F c L isL.
Proof.
  transparent assert (LL : (LimCone (mapdiagram (pr1_precat D) F))).
  { use mk_LimCone. apply c. apply L. apply isL. }
  intro H.
  destruct H as [H1 H2].
  set (XR := iscontrpr1 H1).
  destruct XR as [d [δ Hδ]].
  mkpair.
  - mkpair.
    + {
        mkpair.
        - exact  (c,,d).
        - cbn.  mkpair.
          +  intro j. cbn. exists (L j). apply (δ j).
          +  { mkpair.
               - intros i j e. cbn.
            use total2_paths_f.
            { cbn. apply (limOutCommutes LL). }
            cbn. unfold forms_cone in Hδ. cbn in Hδ.
            assert (Hδ' := Hδ i j e).
            assert (H44 := fiber_paths Hδ').
            cbn in H44.
            etrans. Focus 2. apply H44.
            Search (transportf _ _ _ = transportf _ _ _ ).
            apply transportf_ext.
            apply homset_property.
          - exists (idpath c).
            intro. apply idpath.
             }
             } 
    + intro x. 
      use total2_paths_f.
      * destruct x as [a [dd [H43 [H38 H4]]]]. cbn in *.
        { use total2_paths_f.
          - apply H38.
          - admit.
        } 
      * idtac.
        simpl.
        apply subtypeEquality.
        { admit.


  }
        apply subtypeEquality.
        
      simpl.
      cbn.
*)




    (* *)