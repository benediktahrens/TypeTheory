(**
  [TypeTheory.ALV1.CwF_SplitTypeCat_Defs]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

In this file, we give the definitions of _split type-categories_ (originally due to Cartmell, here following a version given by Pitts) and _categories with families_ (originally due to Dybjer, here following a formulation given by Fiore).

To facilitate comparing them afterwards, we split up their definitions in a slightly unusual way, starting with the part they share.  The key definitions of this file are therefore (all over a fixed base (pre)category [C]):  

- _object-extension structures_, [obj_ext_structure], the common core of CwF’s and split type-categories;
- (_functional) term structures_, [term_fun_structure], the rest of the structure of a CwF on [C];
- _cwf-structures_, [cwf_structure], the full structure of a CwF on a precategory [C]; 
- _CwF’s_, [cwf]; 
- _q-morphism structures_, [qq_morphism_structure], for rest of the structure of a split type-category on [C];
- _split type-cat structures_, [split_typecat_structure], the full structure of a split type-category on [C].
- _split type-categories_, [split_typecat].

NB: for now, we follow the literature in saying e.g. _category_ with families and split type-_category_, but these definitions do not include saturation, so are really _precategories_ with families, etc.
*)



Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.OtherDefs.TypeCat_alt.

Set Automatic Introduction.


Section SplitTypeCat_from_ObjExtqmor.

Variable C : Precategory.

Variables (X : obj_ext_structure C) (Y : qq_morphism_structure X).

Definition type_cat_from_qq : type_cat_struct C.
Proof.
  mkpair.
  - mkpair.
    + exact (fun Γ => (TY X : functor _ _ ) Γ : hSet).
    + cbn. mkpair. 
      * exact (fun Γ A => comp_ext _ Γ A).
      * intros G A G' f. apply (# (TY X : functor _ _ ) f A).
  - repeat mkpair; cbn.
    + intros G A. exact (π _ ).
    + intros G A G' f. exact (qq Y _ _ ).
    + intros. cbn. exact (qq_π Y _ _ ).
    + intros; cbn. apply qq_π_Pb.
Defined.

Definition is_split_type_cat_from_qq : is_split_type_cat type_cat_from_qq.
Proof.
  repeat mkpair.
  - intro. apply setproperty.
  - intros. apply (toforallpaths _ _ _ (functor_id (TY X) _ )).
  - cbn. intros. apply (qq_id Y).
  - intros. apply (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _ )).
  - intros. apply (qq_comp Y).
Qed.

End SplitTypeCat_from_ObjExtqmor.

Section ObjExtqmor_from_SplitTypeCat.

Variable C : Precategory.

Variable T : type_cat_struct C.
Variable H : is_split_type_cat T.

Definition obj_ext_from_split_type_cat : obj_ext_structure C.
Proof.
  repeat mkpair.
  - intro G. mkpair. + apply (T G). +  apply (isaset_types_typecat H).
  - cbn. intros G G' f A. apply (reind_type_cat A f).
  - intro G. apply funextsec. cbn. intro A.
    apply (reind_id_type_typecat H).
  - cbn. intros G G' G'' f f'.
    apply funextsec; cbn; intro A. 
    apply (reind_comp_type_typecat H).
  - cbn. intros. mkpair. apply (ext_type_cat _ A).
                         apply (dpr_type_cat  _ ).
Defined.

Definition qq_mor_from_split_type_cat 
  : qq_morphism_structure obj_ext_from_split_type_cat.                       
Proof.
  repeat mkpair.
  - cbn. intros. apply (q_type_cat).
  - cbn. intros. mkpair. 
    + apply dpr_q_type_cat.
    + apply reind_pb_type_cat.
  - cbn; intros.
    assert (XR := reind_id_term_typecat H).
    etrans. apply XR. unfold comp_ext_compare. 
    apply maponpaths. apply maponpaths. apply maponpaths.
    apply (isaset_types_typecat H).
  - cbn; intros.
    assert (XR := reind_comp_term_typecat H).
    etrans. apply XR. unfold comp_ext_compare. 
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply maponpaths. apply maponpaths. apply maponpaths.
    apply (isaset_types_typecat H).
Defined.

End ObjExtqmor_from_SplitTypeCat.

Lemma foo (C : Precategory) (X : obj_ext_structure C) (Y : qq_morphism_structure X) 
  : obj_ext_from_split_type_cat _ (type_cat_from_qq _ X Y) 
                                (is_split_type_cat_from_qq _ X Y)= X.
Proof.
  cbn.
  use total2_paths; cbn.
  - destruct X as [Ty b ]; cbn. 
Abort.

Lemma foo (C : Precategory) (T : type_cat_struct C) (H : is_split_type_cat T)
  : type_cat_from_qq _ (obj_ext_from_split_type_cat _ T H) ( qq_mor_from_split_type_cat _ T H) = T.
Proof.
  use total2_paths.
  - cbn. destruct T as [R RT]. cbn. 
    clear H. clear RT.
    use total2_paths.
    + apply idpath.
    + cbn. destruct R as [X XR]. cbn.
      use total2_paths.
      * cbn.  apply idpath.
      * cbn. apply idpath.
