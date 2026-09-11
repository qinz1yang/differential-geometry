import DifferentialGeometry.Tensor.Exterior.Descent
import DifferentialGeometry.Geometry.Metric.Cylinder.TangentFraming
import DifferentialGeometry.Tensor.Alternating.Determinant
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace ContinuousAlternatingMap

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [Finite ι]

private theorem eq_smul_of_basis (b : Module.Basis ι Real V)
    (α β : V [⋀^ι]→L[Real] Real) (hα : α ≠ 0) :
    β = (β b / α b) • α := by
  classical
  let _ := Fintype.ofFinite ι
  have ha : α b ≠ 0 := by
    apply (α.toAlternatingMap.map_basis_ne_zero_iff b).mpr
    intro h
    apply hα
    ext v
    exact congrArg (fun γ : V [⋀^ι]→ₗ[Real] Real => γ v) h
  have hβ := β.toAlternatingMap.eq_smul_basis_det b
  have hα' := α.toAlternatingMap.eq_smul_basis_det b
  ext v
  have hb := congrArg (fun γ : V [⋀^ι]→ₗ[Real] Real => γ v) hβ
  have ha' := congrArg (fun γ : V [⋀^ι]→ₗ[Real] Real => γ v) hα'
  change β v = β b * b.det v at hb
  change α v = α b * b.det v at ha'
  change β v = β b / α b * α v
  rw [hb, ha']
  field_simp

end ContinuousAlternatingMap

section

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

private theorem exists_eq_zero_of_continuous_eq_neg {f : X → Real}
    (hf : Continuous f) (x y : X) (hxy : f y = -f x) :
    ∃ z, f z = 0 := by
  rcases le_total (f x) 0 with hx | hx
  · exact intermediate_value_univ x y hf ⟨hx, by rw [hxy]; exact neg_nonneg.mpr hx⟩
  · exact intermediate_value_univ y x hf ⟨by rw [hxy]; exact neg_nonpos.mpr hx, hx⟩

private theorem ne_neg_of_continuous_ne_zero {f : X → Real}
    (hf : Continuous f) (hne : ∀ z, f z ≠ 0) (x y : X) :
    f y ≠ -f x := by
  intro hxy
  obtain ⟨z, hz⟩ := exists_eq_zero_of_continuous_eq_neg hf x y hxy
  exact hne z hz

end

namespace DifferentialGeometry.Geometry

private instance euclideanThreeFinrank :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem alternating_three_apply_neg
    (α : EuclideanSpace Real (Fin 3) [⋀^Fin 3]→L[Real] Real)
    (v : Fin 3 → EuclideanSpace Real (Fin 3)) : α (fun i => -v i) = -α v := by
  simpa [show (-1 : Real) ^ 3 = -1 by norm_num] using
    α.map_smul_univ (fun _ => (-1 : Real)) v

private theorem alternating_three_apply_reflection
    (α : EuclideanSpace Real (Fin 3) [⋀^Fin 3]→L[Real] Real)
    {y : EuclideanSpace Real (Fin 3)} (hy : y ≠ 0)
    (v : Fin 3 → EuclideanSpace Real (Fin 3)) :
    α (fun i => (Real ∙ y).reflection (v i)) = α v := by
  have h := α.toAlternatingMap.map_linearMap_eq_det_mul
    (EuclideanSpace.basisFun (Fin 3) Real).toBasis (Real ∙ y).reflection.toLinearMap v
  rw [Submodule.det_reflection, Submodule.finrank_orthogonal_span_singleton (n := 2) hy] at h
  simpa [Function.comp_def] using h

private theorem exists_nonzero_alternating_three :
    ∃ α : EuclideanSpace Real (Fin 3) [⋀^Fin 3]→L[Real] Real, α ≠ 0 := by
  let b := (EuclideanSpace.basisFun (Fin 3) Real).toBasis
  let α : EuclideanSpace Real (Fin 3) [⋀^Fin 3]→L[Real] Real :=
    { b.det with cont := b.continuous_toMatrix.matrix_det }
  refine ⟨α, ?_⟩
  intro h
  have hv := congrArg (fun β : EuclideanSpace Real (Fin 3) [⋀^Fin 3]→L[Real] Real => β b) h
  change b.det b = 0 at hv
  exact one_ne_zero (b.det_self.symm.trans hv)



theorem cylinderTangentFraming_antipodal
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    cylinderTangentFraming (cylinderAntipodalDiffeomorph x)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        cylinderAntipodalDiffeomorph x v) = -cylinderTangentFraming x v := by
  change cylinderTangentFraming
    ((sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)).prodCongr
      (Diffeomorph.refl 𝓘(Real, Real) Real ∞) x)
    (mfderiv _ _ ((sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)).prodCongr
      (Diffeomorph.refl 𝓘(Real, Real) Real ∞)) x v) = _
  rw [cylinderTangentFraming_prodCongr]
  change -(dIncl (n := 2) x.1 v.1 + (show Real from mfderiv 𝓘(Real, Real) 𝓘(Real, Real) id x.2 v.2) • (x.1 : _)) = _
  rw [mfderiv_id, cylinderTangentFraming_apply]
  rfl

theorem cylinderTangentFraming_diagonal
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    cylinderTangentFraming (cylinderDiagonalDiffeomorph x)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        cylinderDiagonalDiffeomorph x v) =
      -dIncl (n := 2) x.1 v.1 + v.2 • (x.1 : EuclideanSpace Real (Fin 3)) := by
  change cylinderTangentFraming
    ((sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)).prodCongr
      (ContinuousLinearEquiv.neg Real).toDiffeomorph x)
    (mfderiv _ _ ((sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)).prodCongr
      (ContinuousLinearEquiv.neg Real).toDiffeomorph) x v) = _
  rw [cylinderTangentFraming_prodCongr]
  change -(dIncl (n := 2) x.1 v.1 +
    (show Real from mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (fun t : Real => -t) x.2 v.2) • (x.1 : _)) = _
  have hneg : mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (fun t : Real => -t) x.2 =
      -(ContinuousLinearMap.id Real Real) := by
    rw [mfderiv_eq_fderiv]
    change fderiv Real (-id) x.2 = _
    rw [fderiv_neg, fderiv_id]
  erw [hneg]
  change -(dIncl (n := 2) x.1 v.1 + (-v.2) • (x.1 : EuclideanSpace Real (Fin 3))) = _
  rw [neg_smul, neg_add, neg_neg]


theorem cylinderTangentFraming_diagonal_reflection
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    cylinderTangentFraming (cylinderDiagonalDiffeomorph x)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        cylinderDiagonalDiffeomorph x v) =
      (Real ∙ (x.1 : EuclideanSpace Real (Fin 3))).reflection (cylinderTangentFraming x v) := by
  rw [cylinderTangentFraming_diagonal, cylinderTangentFraming_apply, map_add, map_smul]
  have hh : dIncl (n := 2) x.1 v.1 ∈ (Real ∙ (x.1 : EuclideanSpace Real (Fin 3)))ᗮ := by
    erw [← dInclEquiv_coe (n := 2) x.1]
    exact (dInclEquiv (n := 2) x.1 v.1).property
  rw [Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hh,
    Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self _)]

theorem cylinderDifferentialForm_antipodal
    (α : EuclideanSpace Real (Fin 3) [⋀^Fin 3]→L[Real] Real)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (v : Fin 3 → TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    cylinderDifferentialForm α (cylinderAntipodalDiffeomorph x)
      (fun i => mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        cylinderAntipodalDiffeomorph x (v i)) = -cylinderDifferentialForm α x v := by
  simp only [cylinderDifferentialForm_apply, cylinderTangentFraming_antipodal]
  exact alternating_three_apply_neg α _

theorem cylinderDifferentialForm_diagonal
    (α : EuclideanSpace Real (Fin 3) [⋀^Fin 3]→L[Real] Real)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (v : Fin 3 → TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    cylinderDifferentialForm α (cylinderDiagonalDiffeomorph x)
      (fun i => mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        cylinderDiagonalDiffeomorph x (v i)) = cylinderDifferentialForm α x v := by
  simp only [cylinderDifferentialForm_apply, cylinderTangentFraming_diagonal_reflection]
  have hx : (x.1 : EuclideanSpace Real (Fin 3)) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [mem_sphere_zero_iff_norm.mp x.1.2]; norm_num)
  exact alternating_three_apply_reflection α hx _


private abbrev Cylinder := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real
private abbrev CylinderModel := (𝓡 2).prod 𝓘(Real, Real)
private abbrev CylinderModelSpace := EuclideanSpace Real (Fin 2) × Real
private abbrev Ambient := EuclideanSpace Real (Fin 3)
private abbrev CylinderTopForm := DifferentialForm CylinderModel Cylinder 3

private theorem cylinder_inverse_framing_contMDiff :
    ContMDiff CylinderModel (CylinderModel.prod 𝓘(Real, Ambient →L[Real] CylinderModelSpace)) ∞
      (fun x : Cylinder => (⟨x, (cylinderTangentFraming x).symm.toContinuousLinearMap⟩ :
        TotalSpace (Ambient →L[Real] CylinderModelSpace)
          (fun x => Bundle.Trivial Cylinder Ambient x →L[Real] TangentSpace CylinderModel x))) := by
  simpa only [ContinuousLinearMap.inverse_equiv] using
    cylinderTangentFraming_hom_contMDiff.clm_bundle_inverse
      (fun _ => ContinuousLinearMap.isInvertible_equiv)

private theorem cylinder_form_ambient_continuous (β : CylinderTopForm) :
    Continuous (fun x : Cylinder => (show Ambient [⋀^Fin 3]→L[Real] Real from
      (β x).compContinuousLinearMap (cylinderTangentFraming x).symm.toContinuousLinearMap)) := by
  have h := β.contMDiff_toFun.alternating_bundle_comp cylinder_inverse_framing_contMDiff
  have hsmooth : ContMDiff CylinderModel 𝓘(Real, Ambient [⋀^Fin 3]→L[Real] Real) ∞
      (fun x : Cylinder => (show Ambient [⋀^Fin 3]→L[Real] Real from
        (β x).compContinuousLinearMap (cylinderTangentFraming x).symm.toContinuousLinearMap)) := by
    intro x
    have hx := (contMDiffAt_totalSpace.mp (h x)).2
    apply hx.congr_of_eventuallyEq
    filter_upwards [] with y
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
    ext v
    simp [ContinuousAlternatingMap.inCoordinates]
    rfl
  exact hsmooth.continuous

private def cylinderFormCoefficient (α : Ambient [⋀^Fin 3]→L[Real] Real) (β : CylinderTopForm)
    (x : Cylinder) : Real :=
  (β x) (fun i => (cylinderTangentFraming x).symm ((EuclideanSpace.basisFun (Fin 3) Real) i)) /
    α (EuclideanSpace.basisFun (Fin 3) Real)

private theorem cylinderFormCoefficient_continuous
    (α : Ambient [⋀^Fin 3]→L[Real] Real) (β : CylinderTopForm) :
    Continuous (cylinderFormCoefficient α β) := by
  have hfield := cylinder_form_ambient_continuous β
  have heval : Continuous (fun x =>
      ((β x).compContinuousLinearMap (cylinderTangentFraming x).symm.toContinuousLinearMap)
        (EuclideanSpace.basisFun (Fin 3) Real)) :=
    hfield.eval continuous_const
  exact heval.div_const _

private theorem cylinder_top_form_eq_coefficient_smul
    (α : Ambient [⋀^Fin 3]→L[Real] Real) (hα : α ≠ 0) (β : CylinderTopForm) (x : Cylinder) :
    β x = cylinderFormCoefficient α β x • cylinderDifferentialForm α x := by
  have h := ContinuousAlternatingMap.eq_smul_of_basis (EuclideanSpace.basisFun (Fin 3) Real).toBasis
    α ((β x).compContinuousLinearMap (cylinderTangentFraming x).symm.toContinuousLinearMap) hα
  ext v
  have hv := congrArg (fun γ : Ambient [⋀^Fin 3]→L[Real] Real =>
    γ (fun i => cylinderTangentFraming x (v i))) h
  simpa only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    cylinderFormCoefficient, cylinderDifferentialForm_apply, Function.comp_def,
    OrthonormalBasis.coe_toBasis] using hv

private theorem cylinderFormCoefficient_ne_zero
    (α : Ambient [⋀^Fin 3]→L[Real] Real) (hα : α ≠ 0) (β : CylinderTopForm)
    (hβ : ∀ x, β x ≠ 0) (x : Cylinder) : cylinderFormCoefficient α β x ≠ 0 := by
  intro hzero
  apply hβ x
  rw [cylinder_top_form_eq_coefficient_smul α hα β x, hzero, zero_smul]

private theorem cylinderFormCoefficient_antipodal
    (α : Ambient [⋀^Fin 3]→L[Real] Real) (hα : α ≠ 0) (β : CylinderTopForm)
    (hinv : ∀ (x : Cylinder) (v : Fin 3 → TangentSpace CylinderModel x),
      β (cylinderAntipodalDiffeomorph x)
        (fun i => mfderiv CylinderModel CylinderModel cylinderAntipodalDiffeomorph x (v i)) = β x v)
    (x : Cylinder) :
    cylinderFormCoefficient α β (cylinderAntipodalDiffeomorph x) =
      -cylinderFormCoefficient α β x := by
  let b := (EuclideanSpace.basisFun (Fin 3) Real).toBasis
  have hb : α b ≠ 0 := by
    apply (α.toAlternatingMap.map_basis_ne_zero_iff b).mpr
    intro h
    apply hα
    ext v
    exact congrArg (fun γ : Ambient [⋀^Fin 3]→ₗ[Real] Real => γ v) h
  let v : Fin 3 → TangentSpace CylinderModel x :=
    fun i => (cylinderTangentFraming x).symm (b i)
  have h := hinv x v
  rw [cylinder_top_form_eq_coefficient_smul α hα β (cylinderAntipodalDiffeomorph x),
    cylinder_top_form_eq_coefficient_smul α hα β x,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
    cylinderDifferentialForm_antipodal] at h
  have hv : cylinderDifferentialForm α x v = α b := by
    simp only [cylinderDifferentialForm_apply, v, ContinuousLinearEquiv.apply_symm_apply]
  rw [hv] at h
  change cylinderFormCoefficient α β (cylinderAntipodalDiffeomorph x) * -(α b) =
    cylinderFormCoefficient α β x * α b at h
  apply mul_right_cancel₀ hb
  calc
    cylinderFormCoefficient α β (cylinderAntipodalDiffeomorph x) * α b =
        -(cylinderFormCoefficient α β (cylinderAntipodalDiffeomorph x) * -(α b)) := by ring
    _ = -(cylinderFormCoefficient α β x * α b) := congrArg Neg.neg h
    _ = -cylinderFormCoefficient α β x * α b := by ring

private theorem not_exists_cylinder_antipodal_invariant_nonvanishing_top_form :
    ¬ ∃ β : DifferentialForm ((𝓡 2).prod 𝓘(Real, Real))
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) 3,
      (∀ x, β x ≠ 0) ∧
        ∀ (x : Cylinder) (v : Fin 3 → TangentSpace CylinderModel x),
          β (cylinderAntipodalDiffeomorph x)
            (fun i => mfderiv CylinderModel CylinderModel cylinderAntipodalDiffeomorph x (v i)) =
              β x v := by
  rintro ⟨β, hβ, hinv⟩
  obtain ⟨α, hα⟩ := exists_nonzero_alternating_three
  let _ : PreconnectedSpace (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 1)
  let x : Cylinder := (⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩, 0)
  exact ne_neg_of_continuous_ne_zero (cylinderFormCoefficient_continuous α β)
    (cylinderFormCoefficient_ne_zero α hα β hβ) x (cylinderAntipodalDiffeomorph x)
      (cylinderFormCoefficient_antipodal α hα β hinv x)


theorem not_exists_nonvanishing_cylinderAntipodalQuotient_top_form :
    ¬ ∃ β : DifferentialForm ((𝓡 2).prod 𝓘(Real, Real)) CylinderAntipodalQuotient 3,
      ∀ x, β x ≠ 0 := by
  rintro ⟨β, hβ⟩
  let q := cylinderAntipodalQuotientMap
  have hq := cylinderAntipodalQuotientMap_isLocalDiffeomorph
  let η := DifferentialForm.pullback q hq.contMDiff β
  apply not_exists_cylinder_antipodal_invariant_nonvanishing_top_form
  refine ⟨η, ?_, ?_⟩
  · intro x
    exact DifferentialForm.pullback_ne_zero β q hq.contMDiff x (hβ _)
      (hq.mfderivToContinuousLinearEquiv (by simp) x).surjective
  · intro x v
    have hcomp : q ∘ (cylinderAntipodalDiffeomorph : Cylinder → Cylinder) = q := by
      funext y
      exact cylinderAntipodalQuotientMap_eq_iff.mpr (Or.inr rfl)
    have hp := DifferentialForm.pullback_comp
      (cylinderAntipodalDiffeomorph : Cylinder → Cylinder) cylinderAntipodalDiffeomorph.contMDiff
      q hq.contMDiff β
    have heq : DifferentialForm.pullback
        (cylinderAntipodalDiffeomorph : Cylinder → Cylinder) cylinderAntipodalDiffeomorph.contMDiff η = η := by
      simpa only [hcomp] using hp.symm
    have hv := congrArg (fun η : DifferentialForm CylinderModel Cylinder 3 => η x v) heq
    exact hv

theorem not_exists_nonvanishing_realProjectivePlane_prod_real_top_form :
    ¬ ∃ β : DifferentialForm ((𝓡 2).prod 𝓘(Real, Real)) (RealProjectivePlane × Real) 3,
      ∀ x, β x ≠ 0 := by
  rintro ⟨β, hβ⟩
  apply not_exists_nonvanishing_cylinderAntipodalQuotient_top_form
  refine ⟨DifferentialForm.pullback cylinderAntipodalQuotientDiffeomorph
    cylinderAntipodalQuotientDiffeomorph.contMDiff β, ?_⟩
  intro x
  exact DifferentialForm.pullback_ne_zero β cylinderAntipodalQuotientDiffeomorph
    cylinderAntipodalQuotientDiffeomorph.contMDiff x (hβ _)
      (cylinderAntipodalQuotientDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).surjective


set_option backward.isDefEq.respectTransparency false in
theorem exists_cylinderDiagonalQuotient_top_form
    (α : EuclideanSpace Real (Fin 3) [⋀^Fin 3]→L[Real] Real) (hα : α ≠ 0) :
    ∃ Ω : DifferentialForm ((𝓡 2).prod 𝓘(Real, Real)) CylinderDiagonalQuotient 3,
      (∀ x, Ω x ≠ 0) ∧ DifferentialForm.pullback cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff Ω = cylinderDifferentialForm α := by
  let β := cylinderDifferentialForm (n := 2) α
  let q := cylinderDiagonalQuotientMap
  have hq := cylinderDiagonalQuotientMap_isLocalDiffeomorph
  have hs := cylinderDiagonalQuotientMap_surjective
  have hβ : ∀ x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real,
      ∀ h : cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y,
        h ▸ (β x).compContinuousLinearMap
          (hq.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap =
        (β y).compContinuousLinearMap
          (hq.mfderivToContinuousLinearEquiv (by simp) y).symm.toContinuousLinearMap := by
    intro x y hxy
    rcases cylinderDiagonalQuotientMap_eq_iff.mp hxy with h | h
    · subst x
      cases hxy
      rfl
    · subst x
      have hcomp : q ∘ (cylinderDiagonalDiffeomorph : _ → _) = q := by
        funext z
        exact cylinderDiagonalQuotientMap_eq_iff.mpr (Or.inr rfl)
      exact DifferentialForm.comp_inverse_mfderiv_eq_of_fiber_preserving β hq
        cylinderDiagonalDiffeomorph hcomp (cylinderDifferentialForm_diagonal α) y
  refine ⟨DifferentialForm.descend β hq hs hβ, ?_, ?_⟩
  · exact DifferentialForm.descend_ne_zero β hq hs hβ (cylinderDifferentialForm_ne_zero α hα)
  · exact DifferentialForm.descend_pullback β hq hs hβ

set_option backward.isDefEq.respectTransparency false in
theorem exists_nonvanishing_cylinderDiagonalQuotient_top_form :
    ∃ Ω : DifferentialForm ((𝓡 2).prod 𝓘(Real, Real)) CylinderDiagonalQuotient 3,
      ∀ x, Ω x ≠ 0 := by
  obtain ⟨α, hα⟩ := exists_nonzero_alternating_three
  obtain ⟨Ω, hΩ, _⟩ := exists_cylinderDiagonalQuotient_top_form α hα
  exact ⟨Ω, hΩ⟩


theorem exists_nonvanishing_puncturedRealProjectiveThreeSpace_top_form :
    ∃ Ω : DifferentialForm (𝓡 3) PuncturedRealProjectiveThreeSpace 3,
      ∀ x, Ω x ≠ 0 := by
  obtain ⟨Ω, hΩ⟩ := exists_nonvanishing_cylinderDiagonalQuotient_top_form
  let e := cylinderDiagonalQuotientDiffeomorph.symm
  refine ⟨DifferentialForm.pullback e e.contMDiff Ω, fun x => ?_⟩
  exact DifferentialForm.pullback_ne_zero Ω e e.contMDiff x (hΩ (e x))
    (e.mfderivToContinuousLinearEquiv (by simp) x).surjective


end DifferentialGeometry.Geometry
