import Mathlib.Algebra.Homology.AlternatingConst
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Topology.Connected.Clopen
import DifferentialGeometry.Topology.SphereSeparation.AlexanderDuality

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject
open scoped Simplicial

namespace Poincare.Topology.SphereSeparation

section ContinuousMapsToSum

variable (D X Y : Type*) [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y]
  [ConnectedSpace D] [Inhabited D] [Inhabited X] [Inhabited Y]

private def continuousMapSumToLeft : C(D, X ⊕ Y) → C(D, X) := fun f ↦
  ⟨fun d ↦ Sum.elim id (fun _ ↦ default) (f d), by fun_prop⟩

private def continuousMapSumToRight : C(D, X ⊕ Y) → C(D, Y) := fun f ↦
  ⟨fun d ↦ Sum.elim (fun _ ↦ default) id (f d), by fun_prop⟩

private def continuousMapInl : C(D, X) → C(D, X ⊕ Y) := fun f ↦
  ⟨fun d ↦ Sum.inl (f d), continuous_inl.comp f.continuous⟩

private def continuousMapInr : C(D, Y) → C(D, X ⊕ Y) := fun f ↦
  ⟨fun d ↦ Sum.inr (f d), continuous_inr.comp f.continuous⟩

omit [Inhabited X] [Inhabited Y] in
private theorem continuousMap_range_inl_of_default_eq_inl
    (f : C(D, X ⊕ Y)) {x : X} (h : f default = Sum.inl x) :
    Set.range f ⊆ Set.range (Sum.inl : X → X ⊕ Y) := by
  have hclopen : IsClopen (f ⁻¹' Set.range (Sum.inl : X → X ⊕ Y)) :=
    isClopen_range_inl.preimage f.continuous
  have hnonempty : (f ⁻¹' Set.range (Sum.inl : X → X ⊕ Y)).Nonempty :=
    ⟨default, x, h.symm⟩
  have hall := hclopen.eq_univ hnonempty
  rintro _ ⟨d, rfl⟩
  exact hall.ge (Set.mem_univ d)

omit [Inhabited X] [Inhabited Y] in
private theorem continuousMap_range_inr_of_default_eq_inr
    (f : C(D, X ⊕ Y)) {y : Y} (h : f default = Sum.inr y) :
    Set.range f ⊆ Set.range (Sum.inr : Y → X ⊕ Y) := by
  have hclopen : IsClopen (f ⁻¹' Set.range (Sum.inr : Y → X ⊕ Y)) :=
    isClopen_range_inr.preimage f.continuous
  have hnonempty : (f ⁻¹' Set.range (Sum.inr : Y → X ⊕ Y)).Nonempty :=
    ⟨default, y, h.symm⟩
  have hall := hclopen.eq_univ hnonempty
  rintro _ ⟨d, rfl⟩
  exact hall.ge (Set.mem_univ d)

noncomputable def continuousMapSumEquiv : C(D, X ⊕ Y) ≃ C(D, X) ⊕ C(D, Y) where
  toFun f := match f default with
    | Sum.inl _ => Sum.inl (continuousMapSumToLeft D X Y f)
    | Sum.inr _ => Sum.inr (continuousMapSumToRight D X Y f)
  invFun := Sum.elim (continuousMapInl D X Y) (continuousMapInr D X Y)
  left_inv f := by
    ext d
    cases h : f default with
    | inl x =>
      have hd := continuousMap_range_inl_of_default_eq_inl D X Y f h
        (Set.mem_range_self d)
      rcases hd with ⟨z, hz⟩
      simp only [h, Sum.elim_inl]
      dsimp only [continuousMapInl, continuousMapSumToLeft]
      have hdz : Sum.elim id (fun _ ↦ default) (f d) = z := by
        rw [← hz]
        rfl
      exact (congrArg Sum.inl hdz).trans hz
    | inr y =>
      have hd := continuousMap_range_inr_of_default_eq_inr D X Y f h
        (Set.mem_range_self d)
      rcases hd with ⟨z, hz⟩
      simp only [h, Sum.elim_inr]
      dsimp only [continuousMapInr, continuousMapSumToRight]
      have hdz : Sum.elim (fun _ ↦ default) id (f d) = z := by
        rw [← hz]
        rfl
      exact (congrArg Sum.inr hdz).trans hz
  right_inv f := by
    rcases f with f | f
    · change Sum.inl _ = Sum.inl f
      congr 1
    · change Sum.inr _ = Sum.inr f
      congr 1

end ContinuousMapsToSum

noncomputable def singularSimplexSumEquiv
    (X Y : TopCat) [Inhabited X] [Inhabited Y] (n : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj (TopCat.of (X ⊕ Y))).obj n ≃
      (TopCat.toSSet.obj X).obj n ⊕ (TopCat.toSSet.obj Y).obj n := by
  letI : Inhabited (stdSimplex ℝ (Fin (n.unop.len + 1))) :=
    ⟨stdSimplex.vertex ⟨0, Nat.zero_lt_succ _⟩⟩
  exact (TopCat.toSSetObjEquiv (TopCat.of (X ⊕ Y)) n).trans
    ((continuousMapSumEquiv
      (stdSimplex ℝ (Fin (n.unop.len + 1))) X Y).trans
      (Equiv.sumCongr (TopCat.toSSetObjEquiv X n).symm
        (TopCat.toSSetObjEquiv Y n).symm))

private def topCatSumInl (X Y : TopCat) : X ⟶ TopCat.of (X ⊕ Y) :=
  TopCat.ofHom ⟨Sum.inl, continuous_inl⟩

private def topCatSumInr (X Y : TopCat) : Y ⟶ TopCat.of (X ⊕ Y) :=
  TopCat.ofHom ⟨Sum.inr, continuous_inr⟩

@[simp]
private theorem singularSimplexSumEquiv_map_inl
    (X Y : TopCat) [Inhabited X] [Inhabited Y]
    (n : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj X).obj n) :
    singularSimplexSumEquiv X Y n
        ((TopCat.toSSet.map (topCatSumInl X Y)).app n x) = Sum.inl x := by
  apply (Equiv.sumCongr (TopCat.toSSetObjEquiv X n)
    (TopCat.toSSetObjEquiv Y n)).injective
  change Sum.inl _ = Sum.inl _
  congr 1

@[simp]
private theorem singularSimplexSumEquiv_map_inr
    (X Y : TopCat) [Inhabited X] [Inhabited Y]
    (n : SimplexCategoryᵒᵖ) (y : (TopCat.toSSet.obj Y).obj n) :
    singularSimplexSumEquiv X Y n
        ((TopCat.toSSet.map (topCatSumInr X Y)).app n y) = Sum.inr y := by
  apply (Equiv.sumCongr (TopCat.toSSetObjEquiv X n)
    (TopCat.toSSetObjEquiv Y n)).injective
  change Sum.inr _ = Sum.inr _
  congr 1

private noncomputable abbrev integerSingularChainComplex (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)

private noncomputable def singularChainSumInl
    (X Y : TopCat) :
    integerSingularChainComplex X ⟶
      integerSingularChainComplex (TopCat.of (X ⊕ Y)) :=
  SSet.chainComplexMap (TopCat.toSSet.map (topCatSumInl X Y))
    (ModuleCat.of ℤ ℤ)

private noncomputable def singularChainSumInr
    (X Y : TopCat) :
    integerSingularChainComplex Y ⟶
      integerSingularChainComplex (TopCat.of (X ⊕ Y)) :=
  SSet.chainComplexMap (TopCat.toSSet.map (topCatSumInr X Y))
    (ModuleCat.of ℤ ℤ)

private noncomputable def singularChainSumToBiprodDegree
    (X Y : TopCat) [Inhabited X] [Inhabited Y] (n : ℕ) :
    (integerSingularChainComplex (TopCat.of (X ⊕ Y))).X n ⟶
      (integerSingularChainComplex X ⊞ integerSingularChainComplex Y).X n :=
  Sigma.desc fun simplex ↦
    match singularSimplexSumEquiv X Y (.op ⦋n⦌) simplex with
    | Sum.inl x =>
        (TopCat.toSSet.obj X).ιChainComplex x ≫
          (biprod.inl : integerSingularChainComplex X ⟶
            integerSingularChainComplex X ⊞ integerSingularChainComplex Y).f n
    | Sum.inr y =>
        (TopCat.toSSet.obj Y).ιChainComplex y ≫
          (biprod.inr : integerSingularChainComplex Y ⟶
            integerSingularChainComplex X ⊞ integerSingularChainComplex Y).f n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem ι_singularChainSumToBiprodDegree
    (X Y : TopCat) [Inhabited X] [Inhabited Y] (n : ℕ)
    (simplex : (TopCat.toSSet.obj (TopCat.of (X ⊕ Y))).obj (.op ⦋n⦌)) :
    (TopCat.toSSet.obj (TopCat.of (X ⊕ Y))).ιChainComplex simplex ≫
        singularChainSumToBiprodDegree X Y n =
      match singularSimplexSumEquiv X Y (.op ⦋n⦌) simplex with
      | Sum.inl x =>
          (TopCat.toSSet.obj X).ιChainComplex x ≫
            (biprod.inl : integerSingularChainComplex X ⟶
              integerSingularChainComplex X ⊞ integerSingularChainComplex Y).f n
      | Sum.inr y =>
          (TopCat.toSSet.obj Y).ιChainComplex y ≫
            (biprod.inr : integerSingularChainComplex Y ⟶
              integerSingularChainComplex X ⊞ integerSingularChainComplex Y).f n := by
  rw [SSet.ιChainComplex, singularChainSumToBiprodDegree, Sigma.ι_desc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem singularChainSumInl_f_comp_toBiprodDegree
    (X Y : TopCat) [Inhabited X] [Inhabited Y] (n : ℕ) :
    (singularChainSumInl X Y).f n ≫
        singularChainSumToBiprodDegree X Y n =
      (biprod.inl : integerSingularChainComplex X ⟶
        integerSingularChainComplex X ⊞ integerSingularChainComplex Y).f n := by
  apply SSet.chainComplex_hom_ext
  intro x
  dsimp only [singularChainSumInl]
  rw [SSet.ι_chainComplexMap_f_assoc]
  rw [ι_singularChainSumToBiprodDegree,
    singularSimplexSumEquiv_map_inl]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem singularChainSumInr_f_comp_toBiprodDegree
    (X Y : TopCat) [Inhabited X] [Inhabited Y] (n : ℕ) :
    (singularChainSumInr X Y).f n ≫
        singularChainSumToBiprodDegree X Y n =
      (biprod.inr : integerSingularChainComplex Y ⟶
        integerSingularChainComplex X ⊞ integerSingularChainComplex Y).f n := by
  apply SSet.chainComplex_hom_ext
  intro y
  dsimp only [singularChainSumInr]
  rw [SSet.ι_chainComplexMap_f_assoc]
  rw [ι_singularChainSumToBiprodDegree,
    singularSimplexSumEquiv_map_inr]

private noncomputable def singularChainBiprodToSum
    (X Y : TopCat) :
    integerSingularChainComplex X ⊞ integerSingularChainComplex Y ⟶
      integerSingularChainComplex (TopCat.of (X ⊕ Y)) :=
  biprod.desc (singularChainSumInl X Y) (singularChainSumInr X Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem singularChainBiprodToSum_f_comp_toBiprodDegree
    (X Y : TopCat) [Inhabited X] [Inhabited Y] (n : ℕ) :
    (singularChainBiprodToSum X Y).f n ≫
        singularChainSumToBiprodDegree X Y n = 𝟙 _ := by
  apply HomologicalComplex.biprodX_ext_from
  · dsimp only [singularChainBiprodToSum]
    rw [HomologicalComplex.biprod_inl_desc_f_assoc, Category.comp_id]
    exact singularChainSumInl_f_comp_toBiprodDegree X Y n
  · dsimp only [singularChainBiprodToSum]
    rw [HomologicalComplex.biprod_inr_desc_f_assoc, Category.comp_id]
    exact singularChainSumInr_f_comp_toBiprodDegree X Y n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem singularChainSumToBiprodDegree_comp_biprodToSum_f
    (X Y : TopCat) [Inhabited X] [Inhabited Y] (n : ℕ) :
    singularChainSumToBiprodDegree X Y n ≫
        (singularChainBiprodToSum X Y).f n = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rcases h : singularSimplexSumEquiv X Y (.op ⦋n⦌) simplex with x | y
  · have hx : simplex =
        (TopCat.toSSet.map (topCatSumInl X Y)).app (.op ⦋n⦌) x := by
      apply (singularSimplexSumEquiv X Y (.op ⦋n⦌)).injective
      rw [h, singularSimplexSumEquiv_map_inl]
    rw [ι_singularChainSumToBiprodDegree_assoc, h]
    dsimp only [singularChainBiprodToSum]
    rw [Category.assoc, HomologicalComplex.biprod_inl_desc_f,
      Category.comp_id, hx]
    exact (SSet.ι_chainComplexMap_f
      (X := TopCat.toSSet.obj X)
      (Y := TopCat.toSSet.obj (TopCat.of (X ⊕ Y)))
      (f := TopCat.toSSet.map (topCatSumInl X Y))
      (R := ModuleCat.of ℤ ℤ) x)
  · have hy : simplex =
        (TopCat.toSSet.map (topCatSumInr X Y)).app (.op ⦋n⦌) y := by
      apply (singularSimplexSumEquiv X Y (.op ⦋n⦌)).injective
      rw [h, singularSimplexSumEquiv_map_inr]
    rw [ι_singularChainSumToBiprodDegree_assoc, h]
    dsimp only [singularChainBiprodToSum]
    rw [Category.assoc, HomologicalComplex.biprod_inr_desc_f,
      Category.comp_id, hy]
    exact (SSet.ι_chainComplexMap_f
      (X := TopCat.toSSet.obj Y)
      (Y := TopCat.toSSet.obj (TopCat.of (X ⊕ Y)))
      (f := TopCat.toSSet.map (topCatSumInr X Y))
      (R := ModuleCat.of ℤ ℤ) y)

private noncomputable def singularChainSumDegreeIso
    (X Y : TopCat) [Inhabited X] [Inhabited Y] (n : ℕ) :
    (integerSingularChainComplex (TopCat.of (X ⊕ Y))).X n ≅
      (integerSingularChainComplex X ⊞ integerSingularChainComplex Y).X n where
  hom := singularChainSumToBiprodDegree X Y n
  inv := (singularChainBiprodToSum X Y).f n
  hom_inv_id := singularChainSumToBiprodDegree_comp_biprodToSum_f X Y n
  inv_hom_id := singularChainBiprodToSum_f_comp_toBiprodDegree X Y n

noncomputable def singularChainComplexSumIso
    (X Y : TopCat) [Inhabited X] [Inhabited Y] :
    integerSingularChainComplex (TopCat.of (X ⊕ Y)) ≅
      integerSingularChainComplex X ⊞ integerSingularChainComplex Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ singularChainSumDegreeIso X Y n) (by
      intro i j hij
      rw [← cancel_epi (singularChainSumDegreeIso X Y i).inv]
      simp only [Iso.inv_hom_id_assoc]
      dsimp only [singularChainSumDegreeIso]
      rw [← Category.assoc, (singularChainBiprodToSum X Y).comm i j,
        Category.assoc,
        singularChainBiprodToSum_f_comp_toBiprodDegree, Category.comp_id])

@[simp]
private theorem dualCochainMap_zero
    {C D : ChainComplex (ModuleCat ℤ) ℕ} :
    dualCochainMap (0 : C ⟶ D) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  ext φ
  apply LinearMap.ext
  intro x
  simp [dualCochainMap, dualDifferential]
  rfl

private theorem dualCochainMap_add
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (f g : C ⟶ D) :
    dualCochainMap (f + g) = dualCochainMap f + dualCochainMap g := by
  apply HomologicalComplex.hom_ext
  intro n
  ext φ
  apply LinearMap.ext
  intro x
  simp [dualCochainMap, dualDifferential]
  rfl

noncomputable def dualCochainComplexBiprodIso
    (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    dualCochainComplex (C ⊞ D) ≅
      dualCochainComplex C ⊞ dualCochainComplex D where
  hom := biprod.lift
    (dualCochainMap (biprod.inl : C ⟶ C ⊞ D))
    (dualCochainMap (biprod.inr : D ⟶ C ⊞ D))
  inv := biprod.desc
    (dualCochainMap (biprod.fst : C ⊞ D ⟶ C))
    (dualCochainMap (biprod.snd : C ⊞ D ⟶ D))
  hom_inv_id := by
    rw [biprod.lift_desc, ← dualCochainMap_comp, ← dualCochainMap_comp,
      ← dualCochainMap_add, biprod.total, dualCochainMap_id]
  inv_hom_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp [← dualCochainMap_comp]
      · simp [← dualCochainMap_comp]
    · apply biprod.hom_ext'
      · simp [← dualCochainMap_comp]
      · simp [← dualCochainMap_comp]

noncomputable def singularCochainComplexSumIso
    (X Y : TopCat) [Inhabited X] [Inhabited Y] :
    singularCochainComplex (TopCat.of (X ⊕ Y)) ≅
      singularCochainComplex X ⊞ singularCochainComplex Y :=
  dualCochainIso (singularChainComplexSumIso X Y).symm ≪≫
    dualCochainComplexBiprodIso
      (integerSingularChainComplex X) (integerSingularChainComplex Y)

noncomputable def singularCohomologySumIso
    (X Y : TopCat) [Inhabited X] [Inhabited Y] (n : ℕ) :
    singularCohomology (TopCat.of (X ⊕ Y)) n ≅
      singularCohomology X n ⊞ singularCohomology Y n := by
  let H := HomologicalComplex.homologyFunctor
    (ModuleCat ℤ) (ComplexShape.up ℕ) n
  letI : H.Additive := inferInstance
  letI : PreservesFiniteBiproducts H :=
    Functor.preservesFiniteBiproductsOfAdditive H
  letI : PreservesBinaryBiproduct
      (singularCochainComplex X) (singularCochainComplex Y) H :=
    preservesBinaryBiproduct_of_preservesBiproduct H _ _
  exact H.mapIso (singularCochainComplexSumIso X Y) ≪≫
    H.mapBiprod (singularCochainComplex X) (singularCochainComplex Y)

noncomputable def singularCochainComplexPUnitIsoDualAlternatingConst :
    singularCochainComplex (TopCat.of PUnit) ≅
      dualCochainComplex (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ)) :=
  (dualCochainIso
    ((AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of PUnit)) ≪≫
      ChainComplex.alternatingConst.mapIso
        (coproductUniqueIso (fun _ : PUnit ↦ ModuleCat.of ℤ ℤ)))).symm

private theorem dualAlternatingConst_d_one_two :
    (dualCochainComplex
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))).d 1 2 =
        𝟙 (ModuleCat.of ℤ (integerDual (ModuleCat.of ℤ ℤ))) := by
  ext f
  rfl

private theorem dualAlternatingConst_d_two_three :
    (dualCochainComplex
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))).d 2 3 = 0 := by
  change ModuleCat.ofHom (dualDifferential
    ((ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ)).d 3 2)) = 0
  rw [show
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ)).d 3 2 = 0 by
        rw [ChainComplex.alternatingConst]
        rw [HomologicalComplex.alternatingConst_d]
        simp [show ¬ Even 3 by rintro ⟨k, h⟩; omega]
        rfl]
  ext f
  simp [dualDifferential]

private theorem dualAlternatingConst_sc_two_f :
    ((dualCochainComplex
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))).sc 2).f = 𝟙 _ := by
  rw [HomologicalComplex.shortComplexFunctor_obj_f]
  rw [CochainComplex.prev_nat_succ 1]
  exact dualAlternatingConst_d_one_two

private theorem dualAlternatingConst_sc_two_g :
    ((dualCochainComplex
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))).sc 2).g = 0 := by
  rw [HomologicalComplex.shortComplexFunctor_obj_g]
  rw [CochainComplex.next ℕ 2]
  exact dualAlternatingConst_d_two_three

private theorem dualAlternatingConst_exactAt_two :
    (dualCochainComplex
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))).ExactAt 2 := by
  let K := dualCochainComplex
    (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))
  rw [K.exactAt_iff' 1 2 3 (CochainComplex.prev_nat_succ 1)
    (CochainComplex.next ℕ 2)]
  have hg : (K.sc' 1 2 3).g = 0 := by
    change K.d 2 3 = 0
    exact dualAlternatingConst_d_two_three
  exact (ShortComplex.exact_iff_epi _ hg).2 (by
    change Epi (K.d 1 2)
    apply (ModuleCat.epi_iff_surjective _).2
    intro y
    refine ⟨y, ?_⟩
    change dualDifferential
      ((ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ)).d 2 1) y = y
    rw [show
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ)).d 2 1 = 𝟙 _ by
        change (if (ComplexShape.down ℕ).Rel 2 1 then
          if Even 2 then 𝟙 _ else 0 else 0) = 𝟙 _
        simp [show Even 2 by exact ⟨1, by norm_num⟩]]
    rfl)


theorem isZero_singularCohomology_punit_two :
    IsZero (singularCohomology (TopCat.of PUnit) 2) := by
  have hexact : (singularCochainComplex (TopCat.of PUnit)).ExactAt 2 :=
    dualAlternatingConst_exactAt_two.of_iso
      singularCochainComplexPUnitIsoDualAlternatingConst.symm
  exact hexact.isZero_homology

noncomputable def singularCohomologyPUnitTwoIsoZero :
    singularCohomology (TopCat.of PUnit) 2 ≅ 0 :=
  isZero_singularCohomology_punit_two.isoZero

noncomputable def singularCohomologySumPUnitTwoIso
    (X : TopCat) [Inhabited X] :
    singularCohomology (TopCat.of (X ⊕ PUnit)) 2 ≅
      singularCohomology X 2 :=
  singularCohomologySumIso X (TopCat.of PUnit) 2 ≪≫
    biprod.mapIso (Iso.refl _) singularCohomologyPUnitTwoIsoZero ≪≫
    (isoBiprodZero (isZero_zero (ModuleCat ℤ))).symm

private noncomputable def sphereTwoBasepoint : SphereTwo :=
  ⟨EuclideanSpace.single 0 1, by
    simp [SphereTwo]⟩

noncomputable def sphereTwoSumPUnitCohomologyIsoSphereTwo :
    singularCohomology (TopCat.of (SphereTwo ⊕ PUnit)) 2 ≅
      singularCohomology (TopCat.of SphereTwo) 2 := by
  letI : Inhabited SphereTwo := ⟨sphereTwoBasepoint⟩
  exact singularCohomologySumPUnitTwoIso (TopCat.of SphereTwo)



noncomputable def sphereTwoCellularCochainComplex :
    CochainComplex (ModuleCat ℤ) ℕ :=
  ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℕ) 0).obj
      (ModuleCat.of ℤ ℤ)) ⊞
    ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℕ) 2).obj
      (ModuleCat.of ℤ ℤ))

noncomputable def sphereTwoCellularCohomologyTwoIsoInt :
    (sphereTwoCellularCochainComplex.homology 2) ≅ ModuleCat.of ℤ ℤ := by
  let C0 := (HomologicalComplex.single (ModuleCat ℤ)
    (ComplexShape.up ℕ) 0).obj (ModuleCat.of ℤ ℤ)
  let C2 := (HomologicalComplex.single (ModuleCat ℤ)
    (ComplexShape.up ℕ) 2).obj (ModuleCat.of ℤ ℤ)
  let H := HomologicalComplex.homologyFunctor
    (ModuleCat ℤ) (ComplexShape.up ℕ) 2
  letI : H.Additive := inferInstance
  letI : PreservesFiniteBiproducts H :=
    Functor.preservesFiniteBiproductsOfAdditive H
  letI : PreservesBinaryBiproduct C0 C2 H :=
    preservesBinaryBiproduct_of_preservesBiproduct H _ _
  let h0 : IsZero (C0.homology 2) :=
    HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℕ) 0 (ModuleCat.of ℤ ℤ) 2 (by norm_num)
  exact H.mapBiprod C0 C2 ≪≫
    biprod.mapIso h0.isoZero
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℕ) 2 (ModuleCat.of ℤ ℤ)) ≪≫
    (isoZeroBiprod (isZero_zero (ModuleCat ℤ))).symm

noncomputable def sphereTwoCohomologyTwoIsoIntOfCellularComparison
    (comparison : HomotopyEquiv
      (singularCochainComplex (TopCat.of SphereTwo))
      sphereTwoCellularCochainComplex) :
    singularCohomology (TopCat.of SphereTwo) 2 ≅ ModuleCat.of ℤ ℤ :=
  comparison.toHomologyIso 2 ≪≫ sphereTwoCellularCohomologyTwoIsoInt

end Poincare.Topology.SphereSeparation
