import DifferentialGeometry.Geometry.Comparison.LinearDimensionIdentity
import DifferentialGeometry.Geometry.Metric.OpenTangentCone

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem linearDimension_open_eq_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + ε))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω)
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    letI : ∀ q : X, HasAnglesAt q := fun q => by
      obtain ⟨Ω, hΩ, hc, hq⟩ := hlocal q
      exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hc hq
    letI : ∀ q : U, HasAnglesAt q := fun _ =>
      hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
    linearDimension U = linearDimension X ∧ linearDimension U = dimH U := by
  let : ∀ q : X, HasAnglesAt q := fun q => by
    obtain ⟨Ω, hΩ, hc, hq⟩ := hlocal q
    exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hc hq
  let : ∀ q : U, HasAnglesAt q := fun _ =>
    hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
  have hlinear := linearDimension_eq_dimH_of_local_comparison_and_dimH hcurves hdim hlocal
  obtain ⟨m, _, hglobal, hopen, S, _, hS, hregular⟩ :=
    exists_dense_euclidean_tangents_of_local_comparison_and_dimH hcurves hdim hlocal
  have hupper : linearDimension U ≤ linearDimension X := by
    apply linearDimension_le_iff.mpr
    intro q k f hf
    let e := TangentCone.openIsometryEquiv hU q
    exact linearDimension_le_iff.mp (le_refl (linearDimension X)) q.val k
      (e ∘ f) (e.isometry.comp hf)
  obtain ⟨q, hqS, hqU⟩ := hS.exists_mem_open hU hne
  obtain ⟨e, _⟩ := hregular q hqS
  let qU : U := ⟨q, hqU⟩
  let f := (TangentCone.openIsometryEquiv hU qU).trans e
  have hlower : (m : ℝ≥0∞) ≤ linearDimension U :=
    linearDimension_le_iff.mp (le_refl (linearDimension U)) qU m f.symm f.symm.isometry
  have heq : linearDimension U = linearDimension X :=
    le_antisymm hupper (by rw [hlinear, hglobal]; exact hlower)
  exact ⟨heq, heq.trans (hlinear.trans (hglobal.trans (hopen U hU hne).symm))⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
