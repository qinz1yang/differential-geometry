import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import DifferentialGeometry.Topology.SphereSeparation.CircleComparison
import DifferentialGeometry.Topology.SphereSeparation.TopologicalRelativeUnion

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open unitInterval

namespace Poincare.Topology.SphereSeparation

universe u v




abbrev EuclideanLine := EuclideanSpace ℝ (Fin 1)


abbrev CircleZero := Metric.sphere (0 : EuclideanLine) 1


abbrev PuncturedLine := ({0}ᶜ : Set EuclideanLine)

private theorem euclideanLine_norm_eq_abs_coord (x : EuclideanLine) :
    ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

private theorem circleZero_coord_eq_one_or_neg_one (x : CircleZero) :
    x.1 0 = 1 ∨ x.1 0 = -1 := by
  have hx : ‖(x.1 : EuclideanLine)‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using x.2
  rw [euclideanLine_norm_eq_abs_coord] at hx
  exact (abs_eq (by norm_num)).mp hx


noncomputable def boolToCircleZero : Bool → CircleZero
  | false => ⟨EuclideanSpace.single 0 (-1), by
      rw [mem_sphere_zero_iff_norm, PiLp.norm_single]
      norm_num⟩
  | true => ⟨EuclideanSpace.single 0 1, by
      rw [mem_sphere_zero_iff_norm, PiLp.norm_single]
      norm_num⟩

noncomputable def circleZeroEquivBool : CircleZero ≃ Bool where
  toFun x := decide (0 < x.1 0)
  invFun := boolToCircleZero
  left_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i
    rcases circleZero_coord_eq_one_or_neg_one x with hx | hx
    · simp [hx, boolToCircleZero]
    · norm_num [hx, boolToCircleZero]
  right_inv b := by
    cases b <;> simp [boolToCircleZero]

private theorem circleZero_coord_ne_zero (x : CircleZero) : x.1 0 ≠ 0 := by
  rcases circleZero_coord_eq_one_or_neg_one x with hx | hx <;> simp [hx]

private theorem isClopen_circleZero_positive :
    IsClopen {x : CircleZero | 0 < x.1 0} := by
  have hcoord : Continuous (fun x : CircleZero ↦ x.1 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 1 ↦ ℝ) 0).comp
      continuous_subtype_val
  constructor
  · apply isOpen_compl_iff.mp
    have heq : {x : CircleZero | 0 < x.1 0}ᶜ =
        {x : CircleZero | x.1 0 < 0} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact lt_of_le_of_ne (le_of_not_gt h) (circleZero_coord_ne_zero x)
      · exact fun h ↦ not_lt_of_ge h.le
    rw [heq]
    exact isOpen_lt hcoord continuous_const
  · exact isOpen_lt continuous_const hcoord

private theorem continuous_circleZeroEquivBool :
    Continuous circleZeroEquivBool := by
  rw [continuous_bool_rng true]
  convert isClopen_circleZero_positive using 1
  ext x
  simp [circleZeroEquivBool]


noncomputable def circleZeroHomeomorphBool : CircleZero ≃ₜ Bool where
  toEquiv := circleZeroEquivBool
  continuous_toFun := continuous_circleZeroEquivBool
  continuous_invFun := continuous_of_discreteTopology


noncomputable def puncturedLineRadialProjection : C(PuncturedLine, CircleZero) where
  toFun x := ⟨NormedSpace.normalize x.1, by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun x ↦ norm_ne_zero_iff.mpr x.2)).smul continuous_subtype_val


def circleZeroInclusionPuncturedLine : C(CircleZero, PuncturedLine) where
  toFun x := ⟨x.1, by
    intro hx
    have hnorm : ‖(x.1 : EuclideanLine)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using x.2
    rw [hx, norm_zero] at hnorm
    norm_num at hnorm⟩
  continuous_toFun := continuous_induced_rng.mpr continuous_subtype_val

@[simp]
theorem puncturedLineRadialProjection_circleZeroInclusion (x : CircleZero) :
    puncturedLineRadialProjection (circleZeroInclusionPuncturedLine x) = x := by
  apply Subtype.ext
  change NormedSpace.normalize x.1 = x.1
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (by simpa only [mem_sphere_zero_iff_norm] using x.2)

private theorem lineRadialHomotopyCoefficient_pos
    (t : unitInterval) (x : PuncturedLine) :
    0 < (1 - (t : ℝ)) * ‖(x.1 : EuclideanLine)‖⁻¹ + (t : ℝ) := by
  have hnorm : 0 < ‖(x.1 : EuclideanLine)‖ := norm_pos_iff.mpr x.2
  by_cases ht : (t : ℝ) = 1
  · simp [ht]
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr htlt) (inv_pos.mpr hnorm)) t.2.1

noncomputable def puncturedLineRadialHomotopy :
    ContinuousMap.Homotopy
      (circleZeroInclusionPuncturedLine.comp puncturedLineRadialProjection)
      (ContinuousMap.id PuncturedLine) where
  toFun tx :=
    ⟨((1 - (tx.1 : ℝ)) * ‖(tx.2.1 : EuclideanLine)‖⁻¹ + (tx.1 : ℝ)) • tx.2.1,
      by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        apply norm_ne_zero_iff.mp
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (lineRadialHomotopyCoefficient_pos tx.1 tx.2)]
        exact mul_ne_zero (lineRadialHomotopyCoefficient_pos tx.1 tx.2).ne'
          (norm_ne_zero_iff.mpr tx.2.2)⟩
  continuous_toFun := by
    have ht : Continuous (fun tx : unitInterval × PuncturedLine ↦ (tx.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous
        (fun tx : unitInterval × PuncturedLine ↦ (tx.2.1 : EuclideanLine)) :=
      continuous_subtype_val.comp continuous_snd
    have hnorm : Continuous
        (fun tx : unitInterval × PuncturedLine ↦ ‖(tx.2.1 : EuclideanLine)‖) :=
      hx.norm
    have hinv : Continuous
        (fun tx : unitInterval × PuncturedLine ↦ ‖(tx.2.1 : EuclideanLine)‖⁻¹) :=
      hnorm.inv₀ (fun tx ↦ norm_ne_zero_iff.mpr tx.2.2)
    apply Continuous.subtype_mk
    exact ((continuous_const.sub ht).mul hinv |>.add ht).smul hx
  map_zero_left x := by
    apply Subtype.ext
    dsimp [puncturedLineRadialProjection, circleZeroInclusionPuncturedLine,
      NormedSpace.normalize]
    change ((1 - (0 : ℝ)) * ‖(x.1 : EuclideanLine)‖⁻¹ + 0) • x.1 =
      ‖(x.1 : EuclideanLine)‖⁻¹ • x.1
    simp
  map_one_left x := by
    apply Subtype.ext
    simp


noncomputable def puncturedLineHomotopyEquivCircleZero :
    ContinuousMap.HomotopyEquiv PuncturedLine CircleZero where
  toFun := puncturedLineRadialProjection
  invFun := circleZeroInclusionPuncturedLine
  left_inv := ⟨puncturedLineRadialHomotopy⟩
  right_inv := by
    rw [show puncturedLineRadialProjection.comp circleZeroInclusionPuncturedLine =
      ContinuousMap.id CircleZero by
        apply ContinuousMap.ext
        exact puncturedLineRadialProjection_circleZeroInclusion]



noncomputable def circleOnePunctureHomeomorph (p : CircleOne) :
    ({p}ᶜ : Set CircleOne) ≃ₜ EuclideanLine := by
  letI : Fact (Module.finrank ℝ EuclideanPlane = 1 + 1) := ⟨by
    norm_num [EuclideanPlane, Module.finrank_fin_fun]⟩
  exact
    (Homeomorph.setCongr (stereographic'_source (n := 1) p).symm).trans
      ((stereographic' 1 p).toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target (n := 1) p)).trans
          (Homeomorph.Set.univ _)))


theorem circleOnePuncture_contractible (p : CircleOne) :
    ContractibleSpace ({p}ᶜ : Set CircleOne) :=
  (circleOnePunctureHomeomorph p).contractibleSpace

noncomputable def euclideanLinePunctureHomotopyEquivCircleZero
    (a : EuclideanLine) :
    ContinuousMap.HomotopyEquiv ({a}ᶜ : Set EuclideanLine) CircleZero :=
  ((Homeomorph.subRight a).subtype (by
    intro x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
      Homeomorph.coe_subRight, sub_ne_zero])).toHomotopyEquiv.trans
    puncturedLineHomotopyEquivCircleZero

noncomputable def circleOneTwoPointComplHomotopyEquivCircleZero
    (p q : CircleOne) (hpq : p ≠ q) :
    ContinuousMap.HomotopyEquiv ({p, q}ᶜ : Set CircleOne) CircleZero := by
  let qp : ({p}ᶜ : Set CircleOne) := ⟨q, by simp [hpq.symm]⟩
  let e := circleOnePunctureHomeomorph p
  let a : EuclideanLine := e qp
  let er : ({qp}ᶜ : Set ({p}ᶜ : Set CircleOne)) ≃ₜ
      ({a}ᶜ : Set EuclideanLine) :=
    e.subtype (by
      intro x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · intro hx h
        exact hx (e.injective h)
      · intro hx h
        exact hx (congr_arg e h))
  exact ((twoPointComplHomeomorphNestedCompl p q hpq).trans er).toHomotopyEquiv.trans
    (euclideanLinePunctureHomotopyEquivCircleZero a)

noncomputable def singularChainsCircleOneTwoPointComplHomotopyEquivCircleZero
    (p q : CircleOne) (hpq : p ≠ q) :
    HomotopyEquiv
      (integerSingularChains (TopCat.of ({p, q}ᶜ : Set CircleOne)))
      (integerSingularChains (TopCat.of CircleZero)) :=
  singularChainHomotopyEquivOfHomotopyEquiv
    (circleOneTwoPointComplHomotopyEquivCircleZero p q hpq)


theorem circleOnePunctureCover {p q : CircleOne} (hpq : p ≠ q) :
    ({p}ᶜ : Set CircleOne) ∪ {q}ᶜ = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  by_cases hxp : x = p
  · exact Or.inr (by simpa [hxp] using hpq)
  · exact Or.inl hxp

theorem circleOnePuncture_inter (p q : CircleOne) :
    ({p}ᶜ : Set CircleOne) ∩ {q}ᶜ = ({p, q} : Set CircleOne)ᶜ := by
  ext x
  simp


theorem isOpen_circleOnePuncture (p : CircleOne) :
    IsOpen ({p}ᶜ : Set CircleOne) :=
  isClosed_singleton.isOpen_compl




noncomputable abbrev circleSingleZero : ChainComplex (ModuleCat ℤ) ℕ :=
  (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj
    (ModuleCat.of ℤ ℤ)


noncomputable abbrev circleSingleOne : ChainComplex (ModuleCat ℤ) ℕ :=
  (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj
    (ModuleCat.of ℤ ℤ)

noncomputable def circleCellularChainComplex :
    ChainComplex (ModuleCat ℤ) ℕ :=
  circleSingleZero ⊞ circleSingleOne

noncomputable abbrev circleTwoSingleZero :
    ChainComplex (ModuleCat ℤ) ℕ :=
  circleSingleZero ⊞ circleSingleZero


noncomputable def circleTwoSingleZeroFold :
    circleTwoSingleZero ⟶ circleSingleZero :=
  biprod.fst + biprod.snd

noncomputable def circleTwoPointCellularAttachingMap :
    circleTwoSingleZero ⟶ circleTwoSingleZero :=
  biprod.lift circleTwoSingleZeroFold (-circleTwoSingleZeroFold)

noncomputable def coproductBoolIsoBiprod
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts C] [HasBinaryBiproducts C] (X : C) :
    (∐ fun _ : Bool ↦ X) ≅ X ⊞ X where
  hom := Sigma.desc fun b ↦ if b then biprod.inr else biprod.inl
  inv := biprod.desc (Sigma.ι (fun _ : Bool ↦ X) false)
    (Sigma.ι (fun _ : Bool ↦ X) true)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro b
    cases b <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> simp

set_option backward.isDefEq.respectTransparency false in
lemma totallyDisconnectedComparison_hom_f_zero_ι
    (X : TopCat) [TotallyDisconnectedSpace X]
    (sigma : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ) sigma ≫
        (AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
          (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) X).hom.f 0 =
      Sigma.ι (fun _ : X ↦ ModuleCat.of ℤ ℤ)
        ((TopCat.toSSetIsoConst X).hom.app
          (Opposite.op (SimplexCategory.mk 0)) sigma) := by
  dsimp [AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace,
    AlgebraicTopology.singularChainComplexFunctor]
  change Sigma.ι _ sigma ≫
      Limits.Sigma.map'
        (f := fun _ : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk 0)) => ModuleCat.of ℤ ℤ)
        (g := fun _ : X => ModuleCat.of ℤ ℤ)
        (fun x => (TopCat.toSSetIsoConst X).hom.app
          (Opposite.op (SimplexCategory.mk 0)) x)
        (fun _ => 𝟙 (ModuleCat.of ℤ ℤ)) ≫
      𝟙 _ ≫ 𝟙 _ = _
  simp

noncomputable def singularChainsBoolHomotopyEquivTwoSingleZero :
    HomotopyEquiv
      (integerSingularChains (TopCat.of Bool)) circleTwoSingleZero := by
  let e₁ := HomotopyEquiv.ofIso
    ((AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of Bool)) ≪≫
      ChainComplex.alternatingConst.mapIso
        (coproductBoolIsoBiprod (ModuleCat.of ℤ ℤ)))
  let e₂ := ChainComplex.alternatingConstHomotopyEquiv
    ((ModuleCat.of ℤ ℤ) ⊞ (ModuleCat.of ℤ ℤ))
  let _ := preservesBinaryBiproducts_of_preservesBinaryProducts
    (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0)
  let e₃ := HomotopyEquiv.ofIso
    (((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0)).mapBiprod
      (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ))
  exact (e₁.trans e₂).trans e₃

section FiniteComparisonFormula

local instance singleZeroPreservesBinaryBiproducts :
    PreservesBinaryBiproducts
      (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

set_option backward.isDefEq.respectTransparency false in
lemma singularChainsBoolHomotopyEquivTwoSingleZero_hom_f_zero_ι
    (sigma : (TopCat.toSSet.obj (TopCat.of Bool)).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of Bool)).obj
      (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ) sigma ≫
      singularChainsBoolHomotopyEquivTwoSingleZero.hom.f 0 =
    Sigma.ι (fun _ : Bool => ModuleCat.of ℤ ℤ)
      ((TopCat.toSSetIsoConst (TopCat.of Bool)).hom.app
        (Opposite.op (SimplexCategory.mk 0)) sigma) ≫
      (coproductBoolIsoBiprod (ModuleCat.of ℤ ℤ)).hom ≫
      (((HomologicalComplex.single (ModuleCat ℤ)
        (ComplexShape.down ℕ) 0)).mapBiprod
          (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ)).hom.f 0 := by
  classical
  dsimp [singularChainsBoolHomotopyEquivTwoSingleZero]
  simp only [HomotopyEquiv.trans_hom, HomologicalComplex.comp_f,
    Category.assoc]
  dsimp only [HomotopyEquiv.ofIso]
  rw [Iso.trans_hom, HomologicalComplex.comp_f]
  simp only [← Category.assoc]
  rw [totallyDisconnectedComparison_hom_f_zero_ι]
  have hc : (AlgebraicTopology.alternatingFaceMapComplexConst.app
      ((ModuleCat.of ℤ ℤ) ⊞ (ModuleCat.of ℤ ℤ))).symm.hom.f 0 = 𝟙 _ := rfl
  simp only [ChainComplex.alternatingConstHomotopyEquiv,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero,
    coproductBoolIsoBiprod, HomotopyEquiv.trans_hom,
    HomologicalComplex.comp_f]
  dsimp only [HomotopyEquiv.ofIso]
  rw [hc]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma singularChainsBool_fold_hom_f_zero_ι
    (sigma : (TopCat.toSSet.obj (TopCat.of Bool)).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of Bool)).obj
      (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ) sigma ≫
      singularChainsBoolHomotopyEquivTwoSingleZero.hom.f 0 ≫
        circleTwoSingleZeroFold.f 0 =
    Sigma.ι (fun _ : PUnit.{1} => ModuleCat.of ℤ ℤ) PUnit.unit ≫
      (coproductUniqueIso (fun _ : PUnit.{1} => ModuleCat.of ℤ ℤ)).hom := by
  rw [← Category.assoc,
    singularChainsBoolHomotopyEquivTwoSingleZero_hom_f_zero_ι]
  let b : Bool := (TopCat.toSSetIsoConst (TopCat.of Bool)).hom.app
    (Opposite.op (SimplexCategory.mk 0)) sigma
  change Sigma.ι (fun _ : Bool => ModuleCat.of ℤ ℤ) b ≫
      (coproductBoolIsoBiprod (ModuleCat.of ℤ ℤ)).hom ≫
      (((HomologicalComplex.single (ModuleCat ℤ)
        (ComplexShape.down ℕ) 0)).mapBiprod
          (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ)).hom.f 0 ≫
        circleTwoSingleZeroFold.f 0 = _
  cases b <;>
    simp [coproductBoolIsoBiprod, circleTwoSingleZeroFold,
      HomologicalComplex.single_map_f_self]

end FiniteComparisonFormula

set_option backward.isDefEq.respectTransparency false in
lemma singularChainsPUnitHomotopyEquivSingleZero_hom_f_zero_ι
    (sigma : (TopCat.toSSet.obj (TopCat.of PUnit.{1})).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of PUnit.{1})).obj
      (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ) sigma ≫
      singularChainsPUnitHomotopyEquivSingleZero.hom.f 0 =
    Sigma.ι (fun _ : PUnit.{1} => ModuleCat.of ℤ ℤ)
      ((TopCat.toSSetIsoConst (TopCat.of PUnit.{1})).hom.app
        (Opposite.op (SimplexCategory.mk 0)) sigma) ≫
      (coproductUniqueIso (fun _ : PUnit.{1} => ModuleCat.of ℤ ℤ)).hom := by
  classical
  dsimp [singularChainsPUnitHomotopyEquivSingleZero]
  simp only [HomotopyEquiv.trans_hom, HomologicalComplex.comp_f]
  dsimp only [HomotopyEquiv.ofIso]
  rw [Iso.trans_hom, HomologicalComplex.comp_f]
  simp only [← Category.assoc]
  rw [totallyDisconnectedComparison_hom_f_zero_ι]
  have hc : (AlgebraicTopology.alternatingFaceMapComplexConst.app
      (ModuleCat.of ℤ ℤ)).symm.hom.f 0 = 𝟙 _ := rfl
  simp only [ChainComplex.alternatingConstHomotopyEquiv,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero,
    HomotopyEquiv.trans_hom, HomologicalComplex.comp_f]
  dsimp only [HomotopyEquiv.ofIso]
  rw [hc]
  simp

noncomputable def singularChainsCircleZeroHomotopyEquivTwoSingleZero :
    HomotopyEquiv
      (integerSingularChains (TopCat.of CircleZero))
      (circleSingleZero ⊞ circleSingleZero) := by
  let e₀ := singularChainHomotopyEquivOfHomotopyEquiv
    circleZeroHomeomorphBool.toHomotopyEquiv
  let e₁ := HomotopyEquiv.ofIso
    ((AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of Bool)) ≪≫
      ChainComplex.alternatingConst.mapIso
        (coproductBoolIsoBiprod (ModuleCat.of ℤ ℤ)))
  let e₂ := ChainComplex.alternatingConstHomotopyEquiv
    ((ModuleCat.of ℤ ℤ) ⊞ (ModuleCat.of ℤ ℤ))
  let _ := preservesBinaryBiproducts_of_preservesBinaryProducts
    (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0)
  let e₃ := HomotopyEquiv.ofIso
    (((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0)).mapBiprod
      (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ))
  exact ((e₀.trans e₁).trans e₂).trans e₃

noncomputable def singularChainsCircleOnePunctureHomotopyEquivSingleZero
    (p : CircleOne) :
    HomotopyEquiv
      (integerSingularChains (TopCat.of ({p}ᶜ : Set CircleOne)))
      circleSingleZero := by
  let _ := circleOnePuncture_contractible p
  exact singularChainsHomotopyEquivSingleZeroOfContractible _

noncomputable def singularChainsCircleOneTwoPointComplHomotopyEquivTwoSingleZero
    (p q : CircleOne) (hpq : p ≠ q) :
    HomotopyEquiv
      (integerSingularChains (TopCat.of ({p, q}ᶜ : Set CircleOne)))
      (circleSingleZero ⊞ circleSingleZero) :=
  (singularChainsCircleOneTwoPointComplHomotopyEquivCircleZero p q hpq).trans
    singularChainsCircleZeroHomotopyEquivTwoSingleZero



def circleOneArcOverlapHomeomorphTwoPointCompl (p q : CircleOne) :
    ({p}ᶜ ∩ {q}ᶜ : Set CircleOne) ≃ₜ
      ({p, q}ᶜ : Set CircleOne) :=
  Homeomorph.setCongr (circleOnePuncture_inter p q)

noncomputable def circleOneArcOverlapHomotopyEquivBool
    (p q : CircleOne) (hpq : p ≠ q) :
    ContinuousMap.HomotopyEquiv
      ({p}ᶜ ∩ {q}ᶜ : Set CircleOne) Bool :=
  (circleOneArcOverlapHomeomorphTwoPointCompl p q).toHomotopyEquiv.trans
    ((circleOneTwoPointComplHomotopyEquivCircleZero p q hpq).trans
      circleZeroHomeomorphBool.toHomotopyEquiv)


noncomputable def circleOnePunctureHomotopyEquivPUnit (p : CircleOne) :
    ContinuousMap.HomotopyEquiv ({p}ᶜ : Set CircleOne) PUnit.{1} := by
  let _ := circleOnePuncture_contractible p
  exact (Classical.choice
      (ContractibleSpace.hequiv_unit ({p}ᶜ : Set CircleOne))).trans
    (Homeomorph.homeomorphOfUnique Unit PUnit.{1}).toHomotopyEquiv


def circleOneArcOverlapToLeft (p q : CircleOne) :
    C(({p}ᶜ ∩ {q}ᶜ : Set CircleOne), ({p}ᶜ : Set CircleOne)) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := by fun_prop


def circleOneArcOverlapToRight (p q : CircleOne) :
    C(({p}ᶜ ∩ {q}ᶜ : Set CircleOne), ({q}ᶜ : Set CircleOne)) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := by fun_prop


def boolToPUnit : C(Bool, PUnit.{1}) :=
  ⟨fun _ ↦ PUnit.unit, continuous_of_discreteTopology⟩

theorem circleOneArcOverlap_collapse_left
    (p q : CircleOne) (hpq : p ≠ q) :
    (circleOnePunctureHomotopyEquivPUnit p).toFun.comp
        (circleOneArcOverlapToLeft p q) =
      boolToPUnit.comp
        (circleOneArcOverlapHomotopyEquivBool p q hpq).toFun := by
  apply ContinuousMap.ext
  intro x
  exact Subsingleton.elim _ _


theorem circleOneArcOverlap_collapse_right
    (p q : CircleOne) (hpq : p ≠ q) :
    (circleOnePunctureHomotopyEquivPUnit q).toFun.comp
        (circleOneArcOverlapToRight p q) =
      boolToPUnit.comp
        (circleOneArcOverlapHomotopyEquivBool p q hpq).toFun := by
  apply ContinuousMap.ext
  intro x
  exact Subsingleton.elim _ _

noncomputable def circleArcCoverAttachingMap (p q : CircleOne) :
    integerSingularChains
        (TopCat.of ({p}ᶜ ∩ {q}ᶜ : Set CircleOne)) ⟶
      integerSingularChains (TopCat.of ({p}ᶜ : Set CircleOne)) ⊞
        integerSingularChains (TopCat.of ({q}ᶜ : Set CircleOne)) :=
  biprod.lift
    (integerSingularChainMap (TopCat.ofHom (circleOneArcOverlapToLeft p q)))
    (-integerSingularChainMap (TopCat.ofHom (circleOneArcOverlapToRight p q)))

noncomputable def twoPointsToTwoPointsAttachingMap :
    integerSingularChains (TopCat.of Bool) ⟶
      integerSingularChains (TopCat.of PUnit.{1}) ⊞
        integerSingularChains (TopCat.of PUnit.{1}) :=
  biprod.lift
    (integerSingularChainMap (TopCat.ofHom boolToPUnit))
    (-integerSingularChainMap (TopCat.ofHom boolToPUnit))

set_option backward.isDefEq.respectTransparency false in
lemma singularChainsBoolCollapse_compatible :
    integerSingularChainMap (TopCat.ofHom boolToPUnit) ≫
        singularChainsPUnitHomotopyEquivSingleZero.hom =
      singularChainsBoolHomotopyEquivTwoSingleZero.hom ≫
        circleTwoSingleZeroFold := by
  change SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom boolToPUnit)) (ModuleCat.of ℤ ℤ) ≫
        singularChainsPUnitHomotopyEquivSingleZero.hom = _
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      simp only [HomologicalComplex.comp_f]
      apply Sigma.hom_ext
      intro sigma
      simp only [← Category.assoc]
      rw [show Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of Bool)).obj
          (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ) sigma =
          (TopCat.toSSet.obj (TopCat.of Bool)).ιChainComplex sigma by rfl]
      rw [SSet.ι_chainComplexMap_f]
      change Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of PUnit.{1})).obj
          (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.map (TopCat.ofHom boolToPUnit)).app _ sigma) ≫
          singularChainsPUnitHomotopyEquivSingleZero.hom.f 0 =
        Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of Bool)).obj
          (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ) sigma ≫
          singularChainsBoolHomotopyEquivTwoSingleZero.hom.f 0 ≫
            circleTwoSingleZeroFold.f 0
      rw [singularChainsPUnitHomotopyEquivSingleZero_hom_f_zero_ι]
      rw [singularChainsBool_fold_hom_f_zero_ι]
      congr 2
  | succ n =>
      apply (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 (ModuleCat.of ℤ ℤ) (n + 1) (by omega)).eq_of_tgt


noncomputable def circleArcOverlapChainsHomotopyEquivBool
    (p q : CircleOne) (hpq : p ≠ q) :
    HomotopyEquiv
      (integerSingularChains
        (TopCat.of ({p}ᶜ ∩ {q}ᶜ : Set CircleOne)))
      (integerSingularChains (TopCat.of Bool)) :=
  singularChainHomotopyEquivOfHomotopyEquiv
    (circleOneArcOverlapHomotopyEquivBool p q hpq)


noncomputable def circleArcPairChainsComparisonMap
    (p q : CircleOne) :
    (integerSingularChains (TopCat.of ({p}ᶜ : Set CircleOne)) ⊞
        integerSingularChains (TopCat.of ({q}ᶜ : Set CircleOne)))
      ⟶ (integerSingularChains (TopCat.of PUnit.{1}) ⊞
        integerSingularChains (TopCat.of PUnit.{1})) :=
  biprod.map
    (singularChainHomotopyEquivOfHomotopyEquiv
      (circleOnePunctureHomotopyEquivPUnit p)).hom
    (singularChainHomotopyEquivOfHomotopyEquiv
      (circleOnePunctureHomotopyEquivPUnit q)).hom

private theorem circleArcOverlap_chain_collapse_left
    (p q : CircleOne) (hpq : p ≠ q) :
    (circleArcOverlapChainsHomotopyEquivBool p q hpq).hom ≫
        integerSingularChainMap (TopCat.ofHom boolToPUnit) =
      integerSingularChainMap
          (TopCat.ofHom (circleOneArcOverlapToLeft p q)) ≫
        (singularChainHomotopyEquivOfHomotopyEquiv
          (circleOnePunctureHomotopyEquivPUnit p)).hom := by
  change integerSingularChainMap
        (TopCat.ofHom (circleOneArcOverlapHomotopyEquivBool p q hpq).toFun) ≫
      integerSingularChainMap (TopCat.ofHom boolToPUnit) =
    integerSingularChainMap
        (TopCat.ofHom (circleOneArcOverlapToLeft p q)) ≫
      integerSingularChainMap
        (TopCat.ofHom (circleOnePunctureHomotopyEquivPUnit p).toFun)
  rw [← integerSingularChainMap_comp, ← integerSingularChainMap_comp]
  congr 1

private theorem circleArcOverlap_chain_collapse_right
    (p q : CircleOne) (hpq : p ≠ q) :
    (circleArcOverlapChainsHomotopyEquivBool p q hpq).hom ≫
        integerSingularChainMap (TopCat.ofHom boolToPUnit) =
      integerSingularChainMap
          (TopCat.ofHom (circleOneArcOverlapToRight p q)) ≫
        (singularChainHomotopyEquivOfHomotopyEquiv
          (circleOnePunctureHomotopyEquivPUnit q)).hom := by
  change integerSingularChainMap
        (TopCat.ofHom (circleOneArcOverlapHomotopyEquivBool p q hpq).toFun) ≫
      integerSingularChainMap (TopCat.ofHom boolToPUnit) =
    integerSingularChainMap
        (TopCat.ofHom (circleOneArcOverlapToRight p q)) ≫
      integerSingularChainMap
        (TopCat.ofHom (circleOnePunctureHomotopyEquivPUnit q).toFun)
  rw [← integerSingularChainMap_comp, ← integerSingularChainMap_comp]
  congr 1

noncomputable def circleArcAttachingArrowHom
    (p q : CircleOne) (hpq : p ≠ q) :
    Arrow.mk (circleArcCoverAttachingMap p q) ⟶
      Arrow.mk twoPointsToTwoPointsAttachingMap where
  left := (circleArcOverlapChainsHomotopyEquivBool p q hpq).hom
  right := circleArcPairChainsComparisonMap p q
  w := by
    change (circleArcOverlapChainsHomotopyEquivBool p q hpq).hom ≫
        twoPointsToTwoPointsAttachingMap =
      circleArcCoverAttachingMap p q ≫
        circleArcPairChainsComparisonMap p q
    apply biprod.hom_ext
    · simpa [circleArcCoverAttachingMap, circleArcPairChainsComparisonMap,
        twoPointsToTwoPointsAttachingMap] using
        circleArcOverlap_chain_collapse_left p q hpq
    · simpa [circleArcCoverAttachingMap, circleArcPairChainsComparisonMap,
        twoPointsToTwoPointsAttachingMap] using
        congrArg Neg.neg (circleArcOverlap_chain_collapse_right p q hpq)



private theorem projective_coprod_integer (ι : Type) :
    Projective (∐ fun _ : ι ↦ ModuleCat.of ℤ ℤ) := by
  classical
  let Z : ι → ModuleCat ℤ := fun _ ↦ ModuleCat.of ℤ ℤ
  have hZ : ∀ i, Module.Projective ℤ (Z i) := by
    intro i
    dsimp [Z]
    exact Module.Projective.of_free
  let _ : ∀ i, Module.Projective ℤ (Z i) := hZ
  have hDirectSum :
      Module.Projective ℤ (DirectSum ι fun i ↦ Z i) :=
    Module.Projective.directSum
  have hCategorical :
      Projective (ModuleCat.of ℤ (DirectSum ι fun i ↦ Z i)) :=
    ModuleCat.projective_of_categoryTheory_projective
      (ModuleCat.of ℤ (DirectSum ι fun i ↦ Z i))
  exact Projective.of_iso (ModuleCat.coprodIsoDirectSum Z).symm hCategorical

theorem projective_integerSingularChains_degree (X : TopCat) (n : ℕ) :
    Projective ((integerSingularChains X).X n) := by
  dsimp [integerSingularChains]
  change Projective
    (∐ fun _ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) ↦ ModuleCat.of ℤ ℤ)
  exact projective_coprod_integer _

theorem projective_smallSingularChainComplex_degree
    (X : TopCat) (V W : Set X) (n : ℕ) :
    Projective ((smallSingularChainComplex X V W).X n) := by
  change Projective
    (∐ fun _ : (smallSingularSubcomplex X V W : SSet).obj
      (Opposite.op (SimplexCategory.mk n)) ↦ ModuleCat.of ℤ ℤ)
  exact projective_coprod_integer _

noncomputable def smallSingularChainsHomotopyEquivOfOpenCover
    (X : TopCat) (V W : Set X)
    (hV : IsOpen V) (hW : IsOpen W) (hcover : V ∪ W = Set.univ) :
    HomotopyEquiv (smallSingularChainComplex X V W)
      (integerSingularChains X) := by
  letI (n : ℕ) : Projective ((smallSingularChainComplex X V W).X n) :=
    projective_smallSingularChainComplex_degree X V W n
  letI (n : ℕ) : Projective ((integerSingularChains X).X n) :=
    projective_integerSingularChains_degree X n
  have hq : QuasiIso (smallSingularChainInclusion X V W) :=
    quasiIso_smallSingularChainInclusion_of_openCover_refines X
      hV hW hcover (fun _ h ↦ h) (fun _ h ↦ h)
  have hh := (ChainComplex.quasiIso_iff_of_projective
    (smallSingularChainInclusion X V W)).mp hq
  let e := Classical.choose hh
  have he := Classical.choose_spec hh
  exact e.copy (_root_.Homotopy.ofEq he)

noncomputable def circleArcSmallChainsHomotopyEquiv
    (p q : CircleOne) (hpq : p ≠ q) :
    HomotopyEquiv
      (smallSingularChainComplex (TopCat.of CircleOne)
        ({p}ᶜ : Set CircleOne) {q}ᶜ)
      (integerSingularChains (TopCat.of CircleOne)) :=
  smallSingularChainsHomotopyEquivOfOpenCover
    (TopCat.of CircleOne) ({p}ᶜ : Set CircleOne) {q}ᶜ
    (isOpen_circleOnePuncture p) (isOpen_circleOnePuncture q)
    (circleOnePunctureCover hpq)




noncomputable def homotopyEquivBiprod
    {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
    {ι : Type*} {c : ComplexShape ι}
    {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (K₁ ⊞ K₂) (L₁ ⊞ L₂) where
  hom := biprod.map e₁.hom e₂.hom
  inv := biprod.map e₁.inv e₂.inv
  homotopyHomInvId := by
    refine ((Homotopy.ofEq ?_).trans
      (((e₁.homotopyHomInvId.compLeft biprod.fst).compRight biprod.inl).add
        ((e₂.homotopyHomInvId.compLeft biprod.snd).compRight biprod.inr))).trans
      (Homotopy.ofEq ?_)
    · apply biprod.hom_ext <;> simp
    · simp only [Category.comp_id, biprod.total]

  homotopyInvHomId := by
    refine ((Homotopy.ofEq ?_).trans
      (((e₁.homotopyInvHomId.compLeft biprod.fst).compRight biprod.inl).add
        ((e₂.homotopyInvHomId.compLeft biprod.snd).compRight biprod.inr))).trans
      (Homotopy.ofEq ?_)
    · apply biprod.hom_ext <;> simp
    · simp only [Category.comp_id, biprod.total]

noncomputable def singularChainsPUnitPairHomotopyEquivTwoSingleZero :
    HomotopyEquiv
      (integerSingularChains (TopCat.of PUnit.{1}) ⊞
        integerSingularChains (TopCat.of PUnit.{1}))
      circleTwoSingleZero :=
  homotopyEquivBiprod singularChainsPUnitHomotopyEquivSingleZero
    singularChainsPUnitHomotopyEquivSingleZero

theorem twoPointsAttachingMap_cellular_square :
    twoPointsToTwoPointsAttachingMap ≫
        singularChainsPUnitPairHomotopyEquivTwoSingleZero.hom =
      singularChainsBoolHomotopyEquivTwoSingleZero.hom ≫
        circleTwoPointCellularAttachingMap := by
  apply biprod.hom_ext
  · simpa [twoPointsToTwoPointsAttachingMap,
      singularChainsPUnitPairHomotopyEquivTwoSingleZero,
      circleTwoPointCellularAttachingMap, homotopyEquivBiprod] using
        singularChainsBoolCollapse_compatible
  · simpa [twoPointsToTwoPointsAttachingMap,
      singularChainsPUnitPairHomotopyEquivTwoSingleZero,
      circleTwoPointCellularAttachingMap, homotopyEquivBiprod] using
        congrArg Neg.neg singularChainsBoolCollapse_compatible

noncomputable def HomotopyEquiv.extend
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {K L : HomologicalComplex C c} (h : HomotopyEquiv K L)
    (e : ComplexShape.Embedding c c') [e.IsRelIff] :
    HomotopyEquiv (K.extend e) (L.extend e) where
  hom := HomologicalComplex.extendMap h.hom e
  inv := HomologicalComplex.extendMap h.inv e
  homotopyHomInvId := by
    rw [← HomologicalComplex.extendMap_comp,
      ← HomologicalComplex.extendMap_id]
    exact h.homotopyHomInvId.extend e
  homotopyInvHomId := by
    rw [← HomologicalComplex.extendMap_comp,
      ← HomologicalComplex.extendMap_id]
    exact h.homotopyInvHomId.extend e

noncomputable def cochainMappingConeHomotopyEquivOfHomotopyEquivs
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
    (eK : HomotopyEquiv K₁ K₂) (eL : HomotopyEquiv L₁ L₂)
    (H : Homotopy (φ₁ ≫ eL.hom) (eK.hom ≫ φ₂)) :
    HomotopyEquiv (CochainComplex.mappingCone φ₁)
      (CochainComplex.mappingCone φ₂) := by
  let τ := CochainComplex.mappingCone.trianglehMapOfHomotopy H
  letI hK : IsIso τ.hom₁ := by
    dsimp [τ]
    exact HomotopyCategory.quotient_inverts_homotopyEquivalences
      C (ComplexShape.up ℤ) eK.hom eK.homotopyEquivalences_hom
  letI hL : IsIso τ.hom₂ := by
    dsimp [τ]
    exact HomotopyCategory.quotient_inverts_homotopyEquivalences
      C (ComplexShape.up ℤ) eL.hom eL.homotopyEquivalences_hom
  have hCone : IsIso τ.hom₃ :=
    CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ τ
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₁)
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₂)
      hK hL
  haveI : IsIso τ.hom₃ := hCone
  exact HomotopyCategory.homotopyEquivOfIso
    (@asIso _ _ _ _ τ.hom₃ hCone)

private noncomputable def isoBiprodOfIsZeroLeft
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} [HasBinaryBiproduct X Y] (hX : IsZero X) :
    Y ≅ X ⊞ Y where
  hom := biprod.inr
  inv := biprod.snd
  hom_inv_id := by simp
  inv_hom_id := by
    rw [← biprod.total]
    rw [hX.eq_of_src biprod.inl 0, comp_zero, zero_add]

noncomputable def extendDownNatHomotopyCofiberXIsoAt
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) (n : ℕ) :
    (HomologicalComplex.homotopyCofiber φ).X n ≅
      (HomologicalComplex.homotopyCofiber
        (HomologicalComplex.extendMap φ
          ComplexShape.embeddingDownNat)).X (-(n : ℤ)) := by
  cases n with
  | zero =>
      have hrel : ¬ (ComplexShape.down ℕ).Rel 0
          ((ComplexShape.down ℕ).next 0) := by simp
      have hFzero : IsZero
          ((F.extend ComplexShape.embeddingDownNat).X (1 : ℤ)) := by
        apply F.isZero_extend_X ComplexShape.embeddingDownNat
        intro n hn
        simp only [ComplexShape.embeddingDownNat_f] at hn
        omega
      have hzero : ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) := by
        norm_num [ComplexShape.embeddingDownNat_f]
      exact
        (HomologicalComplex.homotopyCofiber.XIso φ 0 hrel) ≪≫
          (G.extendXIso ComplexShape.embeddingDownNat hzero).symm ≪≫
          isoBiprodOfIsZeroLeft hFzero ≪≫
          (HomologicalComplex.homotopyCofiber.XIsoBiprod
            (HomologicalComplex.extendMap φ
              ComplexShape.embeddingDownNat)
            (0 : ℤ) (1 : ℤ) (by norm_num [ComplexShape.up_Rel])).symm
  | succ n =>
      have hdown : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
      have hup : (ComplexShape.up ℤ).Rel (-(n + 1 : ℕ) : ℤ)
          (-(n : ℕ) : ℤ) := by
        simp only [ComplexShape.up_Rel]
        omega
      exact
        (HomologicalComplex.homotopyCofiber.XIsoBiprod φ
            (n + 1) n hdown) ≪≫
          biprod.mapIso
            (F.extendXIso ComplexShape.embeddingDownNat rfl).symm
            (G.extendXIso ComplexShape.embeddingDownNat rfl).symm ≪≫
          (HomologicalComplex.homotopyCofiber.XIsoBiprod
            (HomologicalComplex.extendMap φ
              ComplexShape.embeddingDownNat)
            (-(n + 1 : ℕ) : ℤ) (-(n : ℕ) : ℤ) hup).symm

noncomputable def extendDownNatHomotopyCofiberXIso
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) (i : ℤ) :
    ((HomologicalComplex.homotopyCofiber φ).extend
        ComplexShape.embeddingDownNat).X i ≅
      (HomologicalComplex.homotopyCofiber
        (HomologicalComplex.extendMap φ
          ComplexShape.embeddingDownNat)).X i := by
  classical
  by_cases hi : ∃ n : ℕ, -(n : ℤ) = i
  · let n := Classical.choose hi
    have hn : -(n : ℤ) = i := Classical.choose_spec hi
    rw [← hn]
    cases n with
    | zero =>
        have hrel : ¬ (ComplexShape.down ℕ).Rel 0
            ((ComplexShape.down ℕ).next 0) := by simp
        have hFzero : IsZero
            ((F.extend ComplexShape.embeddingDownNat).X (1 : ℤ)) := by
          apply F.isZero_extend_X ComplexShape.embeddingDownNat
          intro n hn
          simp only [ComplexShape.embeddingDownNat_f] at hn
          omega
        exact
          ((HomologicalComplex.homotopyCofiber φ).extendXIso
              ComplexShape.embeddingDownNat rfl) ≪≫
            (HomologicalComplex.homotopyCofiber.XIso φ 0 hrel) ≪≫
            (G.extendXIso ComplexShape.embeddingDownNat rfl).symm ≪≫
            isoBiprodOfIsZeroLeft hFzero ≪≫
            (HomologicalComplex.homotopyCofiber.XIsoBiprod
              (HomologicalComplex.extendMap φ
                ComplexShape.embeddingDownNat)
              (0 : ℤ) (1 : ℤ) rfl).symm
    | succ n =>
        have hdown : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
        have hup : (ComplexShape.up ℤ).Rel (-(n + 1 : ℕ) : ℤ)
            (-(n : ℕ) : ℤ) := by
          simp only [ComplexShape.up_Rel]
          omega
        exact
          ((HomologicalComplex.homotopyCofiber φ).extendXIso
              ComplexShape.embeddingDownNat rfl) ≪≫
            (HomologicalComplex.homotopyCofiber.XIsoBiprod φ
              (n + 1) n hdown) ≪≫
            biprod.mapIso
              (F.extendXIso ComplexShape.embeddingDownNat rfl).symm
              (G.extendXIso ComplexShape.embeddingDownNat rfl).symm ≪≫
            (HomologicalComplex.homotopyCofiber.XIsoBiprod
              (HomologicalComplex.extendMap φ
                ComplexShape.embeddingDownNat)
              (-(n + 1 : ℕ) : ℤ) (-(n : ℕ) : ℤ) hup).symm
  · have hLeft : IsZero
        (((HomologicalComplex.homotopyCofiber φ).extend
          ComplexShape.embeddingDownNat).X i) :=
      (HomologicalComplex.homotopyCofiber φ).isZero_extend_X
        ComplexShape.embeddingDownNat i (by
          intro n hn
          apply hi
          exact ⟨n, by simpa only [ComplexShape.embeddingDownNat_f] using hn⟩)
    have hG : IsZero ((G.extend ComplexShape.embeddingDownNat).X i) :=
      G.isZero_extend_X ComplexShape.embeddingDownNat i (by
        intro n hn
        apply hi
        exact ⟨n, by simpa only [ComplexShape.embeddingDownNat_f] using hn⟩)
    have hF : IsZero
        ((F.extend ComplexShape.embeddingDownNat).X (i + 1)) := by
      apply F.isZero_extend_X ComplexShape.embeddingDownNat
      intro n hn
      apply hi
      refine ⟨n + 1, ?_⟩
      simp only [ComplexShape.embeddingDownNat_f] at hn ⊢
      omega
    have hRight : IsZero
        ((HomologicalComplex.homotopyCofiber
          (HomologicalComplex.extendMap φ
            ComplexShape.embeddingDownNat)).X i) := by
      apply HomologicalComplex.homotopyCofiber.isZero_X
        (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) i
      · exact hG
      · intro j hij
        have hj : i + 1 = j := by
          simpa only [ComplexShape.up_Rel] using hij
        subst j
        exact hF
    exact hLeft.isoZero ≪≫ hRight.isoZero.symm

noncomputable def extendDownNatHomotopyCofiberXIsoAtEmbedding
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) (n : ℕ) :
    (HomologicalComplex.homotopyCofiber φ).X n ≅
      (HomologicalComplex.homotopyCofiber
        (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)).X
          (ComplexShape.embeddingDownNat.f n) := by
  cases n with
  | zero =>
      have hrel : ¬ (ComplexShape.down ℕ).Rel 0
          ((ComplexShape.down ℕ).next 0) := by simp
      have hFzero : IsZero
          ((F.extend ComplexShape.embeddingDownNat).X (1 : ℤ)) := by
        apply F.isZero_extend_X ComplexShape.embeddingDownNat
        intro n hn
        simp only [ComplexShape.embeddingDownNat_f] at hn
        omega
      have hup : (ComplexShape.up ℤ).Rel
          (ComplexShape.embeddingDownNat.f 0) 1 := by
        norm_num [ComplexShape.up_Rel, ComplexShape.embeddingDownNat_f]
      exact
        (HomologicalComplex.homotopyCofiber.XIso φ 0 hrel) ≪≫
          (G.extendXIso ComplexShape.embeddingDownNat rfl).symm ≪≫
          isoBiprodOfIsZeroLeft hFzero ≪≫
          (HomologicalComplex.homotopyCofiber.XIsoBiprod
            (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
            (ComplexShape.embeddingDownNat.f 0) (1 : ℤ) hup).symm
  | succ n =>
      have hdown : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
      exact
        (HomologicalComplex.homotopyCofiber.XIsoBiprod φ
            (n + 1) n hdown) ≪≫
          biprod.mapIso
            (F.extendXIso ComplexShape.embeddingDownNat rfl).symm
            (G.extendXIso ComplexShape.embeddingDownNat rfl).symm ≪≫
          (HomologicalComplex.homotopyCofiber.XIsoBiprod
            (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
            (ComplexShape.embeddingDownNat.f (n + 1))
            (ComplexShape.embeddingDownNat.f n)
            (ComplexShape.embeddingDownNat.rel hdown)).symm

set_option backward.isDefEq.respectTransparency false in
private lemma extendDownNatHomotopyCofiberXIsoAtEmbedding_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) :
    extendDownNatHomotopyCofiberXIsoAtEmbedding φ 0 =
      (HomologicalComplex.homotopyCofiber.XIso φ 0 (by simp)) ≪≫
        (G.extendXIso ComplexShape.embeddingDownNat rfl).symm ≪≫
        isoBiprodOfIsZeroLeft (by
          apply F.isZero_extend_X ComplexShape.embeddingDownNat
          intro n hn
          simp only [ComplexShape.embeddingDownNat_f] at hn
          omega) ≪≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod
          (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
          (ComplexShape.embeddingDownNat.f 0) (1 : ℤ)
          (by norm_num [ComplexShape.up_Rel,
            ComplexShape.embeddingDownNat_f])).symm := rfl

set_option backward.isDefEq.respectTransparency false in
lemma extendDownNatHomotopyCofiberXIsoAtEmbedding_inl
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homotopyCofiber.inlX φ n (n + 1) (by simp) ≫
        (extendDownNatHomotopyCofiberXIsoAtEmbedding φ (n + 1)).hom =
      (F.extendXIso ComplexShape.embeddingDownNat (by rfl)).inv ≫
        HomologicalComplex.homotopyCofiber.inlX
          (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
          (ComplexShape.embeddingDownNat.f n)
          (ComplexShape.embeddingDownNat.f (n + 1))
          (ComplexShape.embeddingDownNat.rel (by simp)) := by
  simp only [extendDownNatHomotopyCofiberXIsoAtEmbedding,
    Iso.trans_hom, Iso.symm_hom]
  rw [HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
  simp only [Limits.biprod.mapIso_hom]
  rw [Limits.biprod.inl_map_assoc]
  rw [HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma extendDownNatHomotopyCofiberXIsoAtEmbedding_inr
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homotopyCofiber.inrX φ (n + 1) ≫
        (extendDownNatHomotopyCofiberXIsoAtEmbedding φ (n + 1)).hom =
      (G.extendXIso ComplexShape.embeddingDownNat (by rfl)).inv ≫
        HomologicalComplex.homotopyCofiber.inrX
          (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
          (ComplexShape.embeddingDownNat.f (n + 1)) := by
  simp only [extendDownNatHomotopyCofiberXIsoAtEmbedding,
    Iso.trans_hom, Iso.symm_hom]
  rw [HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc]
  simp only [Limits.biprod.mapIso_hom]
  rw [Limits.biprod.inr_map_assoc]
  rw [HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma extendDownNatHomotopyCofiberXIsoAtEmbedding_fst
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) (n : ℕ) :
    (extendDownNatHomotopyCofiberXIsoAtEmbedding φ (n + 1)).hom ≫
        HomologicalComplex.homotopyCofiber.fstX
          (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
          (ComplexShape.embeddingDownNat.f (n + 1))
          (ComplexShape.embeddingDownNat.f n)
          (ComplexShape.embeddingDownNat.rel (by simp)) =
      HomologicalComplex.homotopyCofiber.fstX φ (n + 1) n (by simp) ≫
        (F.extendXIso ComplexShape.embeddingDownNat (by rfl)).inv := by
  simp only [extendDownNatHomotopyCofiberXIsoAtEmbedding,
    Iso.trans_hom, Iso.symm_hom,
    Category.assoc, HomologicalComplex.homotopyCofiber.fstX]
  rw [Iso.inv_hom_id_assoc]
  simp only [Limits.biprod.mapIso_hom]
  rw [Limits.biprod.map_fst]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma extendDownNatHomotopyCofiberXIsoAtEmbedding_snd
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) (n : ℕ) :
    (extendDownNatHomotopyCofiberXIsoAtEmbedding φ (n + 1)).hom ≫
        HomologicalComplex.homotopyCofiber.sndX
          (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
          (ComplexShape.embeddingDownNat.f (n + 1)) =
      HomologicalComplex.homotopyCofiber.sndX φ (n + 1) ≫
        (G.extendXIso ComplexShape.embeddingDownNat (by rfl)).inv := by
  have hdown : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
  apply HomologicalComplex.homotopyCofiber.ext_from_X φ n (n + 1) hdown
  · rw [← Category.assoc,
      extendDownNatHomotopyCofiberXIsoAtEmbedding_inl,
      Category.assoc]
    simp
  · rw [← Category.assoc,
      extendDownNatHomotopyCofiberXIsoAtEmbedding_inr,
      Category.assoc]
    simp

set_option backward.isDefEq.respectTransparency false in
lemma extendDownNatHomotopyCofiberXIsoAtEmbedding_zero_snd
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) :
    (extendDownNatHomotopyCofiberXIsoAtEmbedding φ 0).hom ≫
        HomologicalComplex.homotopyCofiber.sndX
          (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
          (ComplexShape.embeddingDownNat.f 0) =
      HomologicalComplex.homotopyCofiber.sndX φ 0 ≫
        (G.extendXIso ComplexShape.embeddingDownNat (by rfl)).inv := by
  have hrel : ¬ (ComplexShape.down ℕ).Rel 0
      ((ComplexShape.down ℕ).next 0) := by simp
  apply HomologicalComplex.homotopyCofiber.ext_from_X' φ 0 hrel
  rw [extendDownNatHomotopyCofiberXIsoAtEmbedding_zero]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [HomologicalComplex.homotopyCofiber.inrX_sndX_assoc]
  simp only [isoBiprodOfIsZeroLeft]
  have hup : (ComplexShape.up ℤ).Rel
      (ComplexShape.embeddingDownNat.f 0) 1 := by
    norm_num [ComplexShape.up_Rel, ComplexShape.embeddingDownNat_f]
  simp only [HomologicalComplex.homotopyCofiber.inrX, dif_neg hrel]
  rw [Iso.inv_hom_id_assoc]
  rw [HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv_assoc
    (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
    (1 : ℤ) (ComplexShape.embeddingDownNat.f 0) hup]
  simp

set_option backward.isDefEq.respectTransparency false in
noncomputable def extendDownNatHomotopyCofiberRestrictionIso
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) :
    HomologicalComplex.homotopyCofiber φ ≅
      (HomologicalComplex.homotopyCofiber
        (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)).restriction
          ComplexShape.embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents
    (extendDownNatHomotopyCofiberXIsoAtEmbedding φ) (by
      intro i j hij
      have hi : j + 1 = i := by
        simpa only [ComplexShape.down_Rel] using hij
      subst i
      cases j with
      | zero =>
          change
            (extendDownNatHomotopyCofiberXIsoAtEmbedding φ 1).hom ≫
                (HomologicalComplex.homotopyCofiber
                  (HomologicalComplex.extendMap φ
                    ComplexShape.embeddingDownNat)).d
                    (ComplexShape.embeddingDownNat.f 1)
                    (ComplexShape.embeddingDownNat.f 0) =
              (HomologicalComplex.homotopyCofiber φ).d 1 0 ≫
                (extendDownNatHomotopyCofiberXIsoAtEmbedding φ 0).hom
          apply HomologicalComplex.homotopyCofiber.ext_to_X
            (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
            (ComplexShape.embeddingDownNat.f 0) (1 : ℤ) (by
              norm_num [ComplexShape.up_Rel,
                ComplexShape.embeddingDownNat_f])
          · apply (F.isZero_extend_X ComplexShape.embeddingDownNat
              (1 : ℤ) (by
                intro n hn
                simp only [ComplexShape.embeddingDownNat_f] at hn
                omega)).eq_of_tgt
          · have he : (ComplexShape.up ℤ).Rel
                (ComplexShape.embeddingDownNat.f 1)
                (ComplexShape.embeddingDownNat.f 0) :=
              ComplexShape.embeddingDownNat.rel (by simp)
            simp only [HomologicalComplex.homotopyCofiber_d]
            rw [Category.assoc,
              HomologicalComplex.homotopyCofiber.d_sndX
                (HomologicalComplex.extendMap φ
                  ComplexShape.embeddingDownNat) _ _ he]
            simp only [Preadditive.comp_add, ← Category.assoc,
              extendDownNatHomotopyCofiberXIsoAtEmbedding_snd,
              extendDownNatHomotopyCofiberXIsoAtEmbedding_fst]
            rw [HomologicalComplex.extendMap_f φ
              ComplexShape.embeddingDownNat (i := 0) rfl]
            rw [G.extend_d_eq ComplexShape.embeddingDownNat
              (i := 1) (j := 0) rfl rfl]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            rw [extendDownNatHomotopyCofiberXIsoAtEmbedding_zero_snd]
            rw [HomologicalComplex.homotopyCofiber.d_sndX_assoc
              φ 1 0 (by simp)]
            simp [Preadditive.add_comp, Category.assoc]
      | succ n =>
          change
            (extendDownNatHomotopyCofiberXIsoAtEmbedding φ (n + 2)).hom ≫
                (HomologicalComplex.homotopyCofiber
                  (HomologicalComplex.extendMap φ
                    ComplexShape.embeddingDownNat)).d
                    (ComplexShape.embeddingDownNat.f (n + 2))
                    (ComplexShape.embeddingDownNat.f (n + 1)) =
              (HomologicalComplex.homotopyCofiber φ).d
                  (n + 2) (n + 1) ≫
                (extendDownNatHomotopyCofiberXIsoAtEmbedding
                  φ (n + 1)).hom
          apply HomologicalComplex.homotopyCofiber.ext_to_X
            (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
            (ComplexShape.embeddingDownNat.f (n + 1))
            (ComplexShape.embeddingDownNat.f n)
            (ComplexShape.embeddingDownNat.rel (by simp))
          · have he₁ : (ComplexShape.up ℤ).Rel
                (ComplexShape.embeddingDownNat.f (n + 2))
                (ComplexShape.embeddingDownNat.f (n + 1)) :=
              ComplexShape.embeddingDownNat.rel (by simp)
            have he₂ : (ComplexShape.up ℤ).Rel
                (ComplexShape.embeddingDownNat.f (n + 1))
                (ComplexShape.embeddingDownNat.f n) :=
              ComplexShape.embeddingDownNat.rel (by simp)
            simp only [HomologicalComplex.homotopyCofiber_d]
            rw [Category.assoc,
              HomologicalComplex.homotopyCofiber.d_fstX
                (HomologicalComplex.extendMap φ
                  ComplexShape.embeddingDownNat) _ _ _ he₁ he₂]
            simp only [Preadditive.comp_neg, ← Category.assoc,
              extendDownNatHomotopyCofiberXIsoAtEmbedding_fst]
            rw [F.extend_d_eq ComplexShape.embeddingDownNat
              (i := n + 1) (j := n) rfl rfl]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            rw [extendDownNatHomotopyCofiberXIsoAtEmbedding_fst]
            rw [HomologicalComplex.homotopyCofiber.d_fstX_assoc φ
              (n + 2) (n + 1) n (by simp) (by simp)]
            simp [Category.assoc]
          · have he : (ComplexShape.up ℤ).Rel
                (ComplexShape.embeddingDownNat.f (n + 2))
                (ComplexShape.embeddingDownNat.f (n + 1)) :=
              ComplexShape.embeddingDownNat.rel (by simp)
            simp only [HomologicalComplex.homotopyCofiber_d]
            rw [Category.assoc,
              HomologicalComplex.homotopyCofiber.d_sndX
                (HomologicalComplex.extendMap φ
                  ComplexShape.embeddingDownNat) _ _ he]
            simp only [Preadditive.comp_add, ← Category.assoc,
              extendDownNatHomotopyCofiberXIsoAtEmbedding_fst,
              extendDownNatHomotopyCofiberXIsoAtEmbedding_snd]
            rw [HomologicalComplex.extendMap_f φ
              ComplexShape.embeddingDownNat (i := n + 1) rfl]
            rw [G.extend_d_eq ComplexShape.embeddingDownNat
              (i := n + 2) (j := n + 1) rfl rfl]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            rw [extendDownNatHomotopyCofiberXIsoAtEmbedding_snd]
            rw [HomologicalComplex.homotopyCofiber.d_sndX_assoc φ
              (n + 2) (n + 1) (by simp)]
            simp [Preadditive.add_comp, Category.assoc])

set_option backward.isDefEq.respectTransparency false in
noncomputable def Homotopy.restrictionDownNat
    {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V]
    {C D : CochainComplex V ℤ} {f g : C ⟶ D}
    (h : Homotopy f g) (hC : IsZero (C.X 1)) :
    Homotopy
      (HomologicalComplex.restrictionMap f ComplexShape.embeddingDownNat)
      (HomologicalComplex.restrictionMap g ComplexShape.embeddingDownNat) where
  hom i j := h.hom (ComplexShape.embeddingDownNat.f i)
    (ComplexShape.embeddingDownNat.f j)
  zero i j hij := by
    apply h.zero
    intro hrel
    exact hij ((ComplexShape.embeddingDownNat.rel_iff j i).mp hrel)
  comm i := by
    let hr : ∀ i j : ℕ,
        (C.restriction ComplexShape.embeddingDownNat).X i ⟶
          (D.restriction ComplexShape.embeddingDownNat).X j :=
      fun i j => h.hom (ComplexShape.embeddingDownNat.f i)
        (ComplexShape.embeddingDownNat.f j)
    change (HomologicalComplex.restrictionMap f
      ComplexShape.embeddingDownNat).f i =
        dNext i hr + prevD i hr +
          (HomologicalComplex.restrictionMap g
            ComplexShape.embeddingDownNat).f i
    cases i with
    | zero =>
        have htarget : (ComplexShape.up ℤ).Rel
            (ComplexShape.embeddingDownNat.f 1)
            (ComplexShape.embeddingDownNat.f 0) :=
          ComplexShape.embeddingDownNat.rel (by simp)
        rw [dNext_eq_zero hr 0 (by simp)]
        rw [prevD_eq hr (show (ComplexShape.down ℕ).Rel 1 0 by simp)]
        dsimp only [hr, HomologicalComplex.restrictionMap,
          HomologicalComplex.restriction]
        rw [h.comm (ComplexShape.embeddingDownNat.f 0)]
        rw [dNext_eq h.hom
          (show (ComplexShape.up ℤ).Rel
            (ComplexShape.embeddingDownNat.f 0) 1 by
              norm_num [ComplexShape.up_Rel,
                ComplexShape.embeddingDownNat_f])]
        rw [prevD_eq h.hom htarget]
        rw [hC.eq_of_tgt
          (C.d (ComplexShape.embeddingDownNat.f 0) 1) 0,
          zero_comp, zero_add]
    | succ n =>
        have hsource : (ComplexShape.up ℤ).Rel
            (ComplexShape.embeddingDownNat.f (n + 1))
            (ComplexShape.embeddingDownNat.f n) :=
          ComplexShape.embeddingDownNat.rel (by simp)
        have htarget : (ComplexShape.up ℤ).Rel
            (ComplexShape.embeddingDownNat.f (n + 2))
            (ComplexShape.embeddingDownNat.f (n + 1)) :=
          ComplexShape.embeddingDownNat.rel (by simp)
        rw [dNext_eq hr
          (show (ComplexShape.down ℕ).Rel (n + 1) n by simp)]
        rw [prevD_eq hr
          (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) by simp)]
        dsimp only [hr, HomologicalComplex.restrictionMap,
          HomologicalComplex.restriction]
        rw [h.comm (ComplexShape.embeddingDownNat.f (n + 1))]
        rw [dNext_eq h.hom hsource]
        rw [prevD_eq h.hom htarget]

noncomputable def HomotopyEquiv.restrictionDownNat
    {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V]
    {C D : CochainComplex V ℤ} (e : HomotopyEquiv C D)
    (hC : IsZero (C.X 1)) (hD : IsZero (D.X 1)) :
    HomotopyEquiv
      (C.restriction ComplexShape.embeddingDownNat)
      (D.restriction ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.restrictionMap e.hom
    ComplexShape.embeddingDownNat
  inv := HomologicalComplex.restrictionMap e.inv
    ComplexShape.embeddingDownNat
  homotopyHomInvId := by
    rw [← HomologicalComplex.restrictionMap_comp,
      ← HomologicalComplex.restrictionMap_id]
    exact Homotopy.restrictionDownNat e.homotopyHomInvId hC
  homotopyInvHomId := by
    rw [← HomologicalComplex.restrictionMap_comp,
      ← HomologicalComplex.restrictionMap_id]
    exact Homotopy.restrictionDownNat e.homotopyInvHomId hD

noncomputable def circleArcPairChainsHomotopyEquivPUnit
    (p q : CircleOne) :
    HomotopyEquiv
      (integerSingularChains (TopCat.of ({p}ᶜ : Set CircleOne)) ⊞
        integerSingularChains (TopCat.of ({q}ᶜ : Set CircleOne)))
      (integerSingularChains (TopCat.of PUnit.{1}) ⊞
        integerSingularChains (TopCat.of PUnit.{1})) :=
  homotopyEquivBiprod
    (singularChainHomotopyEquivOfHomotopyEquiv
      (circleOnePunctureHomotopyEquivPUnit p))
    (singularChainHomotopyEquivOfHomotopyEquiv
      (circleOnePunctureHomotopyEquivPUnit q))

@[simp]
theorem circleArcPairChainsHomotopyEquivPUnit_hom
    (p q : CircleOne) :
    (circleArcPairChainsHomotopyEquivPUnit p q).hom =
      circleArcPairChainsComparisonMap p q := rfl

noncomputable def circleArcExtendedMappingConeHomotopyEquiv
    (p q : CircleOne) (hpq : p ≠ q) :
    HomotopyEquiv
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap (circleArcCoverAttachingMap p q)
          ComplexShape.embeddingDownNat))
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap twoPointsToTwoPointsAttachingMap
          ComplexShape.embeddingDownNat)) := by
  let eK := Poincare.Topology.SphereSeparation.HomotopyEquiv.extend
    (circleArcOverlapChainsHomotopyEquivBool p q hpq)
    ComplexShape.embeddingDownNat
  let eL := Poincare.Topology.SphereSeparation.HomotopyEquiv.extend
    (circleArcPairChainsHomotopyEquivPUnit p q)
    ComplexShape.embeddingDownNat
  apply cochainMappingConeHomotopyEquivOfHomotopyEquivs eK eL
  apply Homotopy.ofEq
  dsimp [eK, eL, HomotopyEquiv.extend]
  rw [← HomologicalComplex.extendMap_comp,
    ← HomologicalComplex.extendMap_comp]
  exact congrArg
    (fun f ↦ HomologicalComplex.extendMap f
      ComplexShape.embeddingDownNat)
    (circleArcAttachingArrowHom p q hpq).w.symm

lemma extendedHomotopyCofiberIsZeroOne
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    {F G : ChainComplex C ℕ} (φ : F ⟶ G) :
    IsZero ((HomologicalComplex.homotopyCofiber
      (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)).X 1) := by
  apply HomologicalComplex.homotopyCofiber.isZero_X
    (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) 1
  · apply G.isZero_extend_X ComplexShape.embeddingDownNat
    intro n hn
    simp only [ComplexShape.embeddingDownNat_f] at hn
    omega
  · intro j hj
    apply F.isZero_extend_X ComplexShape.embeddingDownNat
    intro n hn
    simp only [ComplexShape.embeddingDownNat_f, ComplexShape.up_Rel] at hn hj
    omega

noncomputable def circleArcHomotopyCofiberHomotopyEquivTwoPoints
    (p q : CircleOne) (hpq : p ≠ q) :
    HomotopyEquiv
      (HomologicalComplex.homotopyCofiber (circleArcCoverAttachingMap p q))
      (HomologicalComplex.homotopyCofiber
        twoPointsToTwoPointsAttachingMap) := by
  let e := Poincare.Topology.SphereSeparation.HomotopyEquiv.restrictionDownNat
    (circleArcExtendedMappingConeHomotopyEquiv p q hpq)
    (extendedHomotopyCofiberIsZeroOne
      (circleArcCoverAttachingMap p q))
    (extendedHomotopyCofiberIsZeroOne
      twoPointsToTwoPointsAttachingMap)
  exact ((HomotopyEquiv.ofIso
    (extendDownNatHomotopyCofiberRestrictionIso
      (circleArcCoverAttachingMap p q))).trans e).trans
        (HomotopyEquiv.ofIso
          (extendDownNatHomotopyCofiberRestrictionIso
            twoPointsToTwoPointsAttachingMap).symm)

noncomputable def twoPointsHomotopyCofiberHomotopyEquivCellularAttaching :
    HomotopyEquiv
      (HomologicalComplex.homotopyCofiber
        twoPointsToTwoPointsAttachingMap)
      (HomologicalComplex.homotopyCofiber
        circleTwoPointCellularAttachingMap) := by
  let eK := Poincare.Topology.SphereSeparation.HomotopyEquiv.extend
    singularChainsBoolHomotopyEquivTwoSingleZero
    ComplexShape.embeddingDownNat
  let eL := Poincare.Topology.SphereSeparation.HomotopyEquiv.extend
    singularChainsPUnitPairHomotopyEquivTwoSingleZero
    ComplexShape.embeddingDownNat
  let eCone := cochainMappingConeHomotopyEquivOfHomotopyEquivs eK eL
    (Homotopy.ofEq (by
      dsimp [eK, eL, HomotopyEquiv.extend]
      rw [← HomologicalComplex.extendMap_comp,
        ← HomologicalComplex.extendMap_comp]
      exact congrArg
        (fun f ↦ HomologicalComplex.extendMap f
          ComplexShape.embeddingDownNat)
        twoPointsAttachingMap_cellular_square))
  let e := Poincare.Topology.SphereSeparation.HomotopyEquiv.restrictionDownNat
    eCone
    (extendedHomotopyCofiberIsZeroOne
      twoPointsToTwoPointsAttachingMap)
    (extendedHomotopyCofiberIsZeroOne
      circleTwoPointCellularAttachingMap)
  exact ((HomotopyEquiv.ofIso
    (extendDownNatHomotopyCofiberRestrictionIso
      twoPointsToTwoPointsAttachingMap)).trans e).trans
        (HomotopyEquiv.ofIso
          (extendDownNatHomotopyCofiberRestrictionIso
            circleTwoPointCellularAttachingMap).symm)

end Poincare.Topology.SphereSeparation
