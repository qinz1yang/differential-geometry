import DifferentialGeometry.Geometry.Metric.RetainedMarkerRadii
import DifferentialGeometry.Analysis.InnerProductSpace.FiniteNormalReduction
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
open scoped BigOperators
open Set Metric

namespace GC.MetricGeometry.X81Sol

variable {ι P : Type*} [Fintype ι]

theorem radius_control_of_orthogonal_scalar_markers (f : P → EuclideanSpace ℝ ι)
    (ρ : P → ℝ) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hfull : ∀ p, ∃ i, f p i = R i)
    (hsupport : ∀ i p, 0 < f p i → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (p q : P) :
    |σ * ρ q - σ * ρ p| ≤ 2 * (dist (f p) (f q) + σ * ρ p) := by
  apply radius_control_of_retained_markers f ρ (fun i x => x i) R hR _ hfull hsupport hσ hσhalf p q
  intro i
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul] using PiLp.dist_apply_le x y i

end GC.MetricGeometry.X81Sol

namespace Submodule.X81Sol

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem finite_affine_family_high_spectral_reduction
    (S : Finset A) (L : A → Submodule ℝ H) (x : A → H) (w : A → ℝ)
    (hw : ∑ i ∈ S, w i = 1) {k : ℕ} (hdim : ∀ i ∈ S, Module.finrank ℝ (L i) ≤ k) (z : H) :
    let V := S.sup (fun i => ℝ ∙ x i ⊔ L i)
    let O : H →L[ℝ] H := ∑ i ∈ S, w i • (L i)ᗮ.starProjection
    let Q := (⨆ a ∈ Ici (1 / 2 : ℝ), Module.End.eigenspace O.toLinearMap a).starProjection
    Module.finrank ℝ V ≤ S.card * (k + 1) ∧
      Module.finrank ℝ (ContinuousLinearMap.id ℝ H - O).range ≤ S.card * k ∧
      Set.MapsTo O V V ∧ (∀ v ∈ Vᗮ, O v = v) ∧ (∀ v ∈ Vᗮ, Q v = v) ∧
      Vᗮ.starProjection (∑ i ∈ S, w i • Q (z - x i)) = Vᗮ.starProjection z := by
  exact finite_affine_family_normal_reduction S L x w hw hdim (Ici (1 / 2 : ℝ)) (by norm_num) z

end Submodule.X81Sol
