import DifferentialGeometry.Geometry.Comparison.LocalPolynomialPacking
import DifferentialGeometry.Topology.MetricSpace.RoughDimension
import DifferentialGeometry.Topology.MetricSpace.LocalCurveDimension

set_option autoImplicit false

open Set Filter Real
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem exists_local_roughDim_le_of_fourPointComparison
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω : Set X} (hΩ : IsOpen Ω) (hcomp : fourPointComparison 1 Ω)
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (Metric.closedBall z R))
    {n : ℕ} (hdim : dimH Ω ≤ n) {p : X} (hp : p ∈ Ω) :
    ∃ h : ℝ, 0 < h ∧ Metric.ball p h ⊆ Ω ∧ ∃ m : ℕ, m ≤ n ∧
      Metric.roughDim (Metric.ball p h) ≤ m ∧
      ∀ b : ℝ, (m : ℝ) < b → Metric.roughVolume b (Metric.ball p h) = 0 := by
  rcases subsingleton_or_nontrivial X with hsub | hnontriv
  · obtain ⟨h, hh, hB⟩ := Metric.isOpen_iff.mp hΩ p hp
    have hS : (Metric.ball p h).Subsingleton := fun _ _ _ _ => Subsingleton.elim _ _
    refine ⟨h, hh, hB, 0, Nat.zero_le n, ?_, ?_⟩
    · simp only [Nat.cast_zero, Metric.roughDim_eq_zero_of_subsingleton hS, le_refl]
    · intro b hb
      apply Metric.roughVolume_eq_zero_of_polynomial_bound (m := 0) (C := 0) le_rfl hb
      intro ε _
      simpa using Metric.finitePackingNumber_le_one_of_subsingleton hS ε
  · have hn : 1 ≤ n := by
      obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
      obtain ⟨u, hup⟩ := exists_ne p
      obtain ⟨c, hc, hc0, hc1, _⟩ := hcurves p u 1 zero_lt_one
      have hl := Metric.one_le_dimH_ball_of_continuous_curve hR c hc hc0
        (by simpa only [hc1] using hup)
      have hbound := hl.trans ((dimH_mono hRΩ).trans hdim)
      exact_mod_cast hbound
    obtain ⟨h, hh, hB, m, _, hmn, C, hC, hpack⟩ :=
      exists_local_polynomial_packing_of_fourPointComparison hcurves hΩ hcomp hcomplete hn hdim hp
    exact ⟨h, hh, hB, m, hmn, Metric.roughDim_le_of_polynomial_bound hC.le hpack,
      fun _ hb => Metric.roughVolume_eq_zero_of_polynomial_bound hC.le hb hpack⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
