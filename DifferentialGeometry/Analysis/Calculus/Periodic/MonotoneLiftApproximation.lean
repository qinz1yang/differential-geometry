import DifferentialGeometry.Analysis.Calculus.Periodic.MonotoneConvolution
import DifferentialGeometry.Analysis.Calculus.Periodic.Derivative







noncomputable section

open Function MeasureTheory Metric
open scoped ContDiff NNReal

namespace DifferentialGeometry.Analysis



theorem exists_smooth_affinePeriodic_approximation {ψ : ℝ → ℝ}
    (hc : Continuous ψ) (hm : Monotone ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℝ → ℝ) (τ : ℝ) (K : ℝ≥0),
      ContDiff ℝ ∞ f ∧ (∀ t, f (t + 1) = f t + 1) ∧ 0 < τ ∧
      (∀ x y, x ≤ y → τ * (y - x) ≤ f y - f x) ∧ LipschitzWith K f ∧
      (∀ x, dist (f x) (ψ x) < ε) := by
  obtain ⟨B, hB, hb⟩ := exists_bound_of_continuous_unit_periodic
    (hc.sub continuous_id) (affinePeriodic_sub_id hp)
  let τ : ℝ := min (1 / 2) (ε / (4 * (B + 1)))
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτone : τ ≤ 1 / 2 := min_le_left _ _
  have hτB : τ * B ≤ ε / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (B + 1))).mp
      (min_le_right (1 / 2) (ε / (4 * (B + 1))))
    change τ * (4 * (B + 1)) ≤ ε at h
    nlinarith
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (uniformContinuous_affinePeriodic hc hp) (ε / 4) (by positivity)
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let S := smoothPeriodic φ ψ
  have hS : ContDiff ℝ ∞ S := smoothPeriodic_contDiff φ hc
  have hSm : Monotone S := smoothPeriodic_monotone φ hc hm
  have hSp : ∀ t, S (t + 1) = S t + 1 := smoothPeriodic_affinePeriodic φ hc hp
  have hSerr (x : ℝ) : dist (S x) (ψ x) ≤ ε / 4 := by
    apply dist_smoothPeriodic_le φ hc
    intro y hy
    apply (hmod ?_).le
    exact hy.trans (by change δ / 2 < δ; linarith)
  let f : ℝ → ℝ := fun x => (1 - τ) * S x + τ * x
  have hfc : ContDiff ℝ ∞ f := (contDiff_const.mul hS).add (contDiff_const.mul contDiff_id)
  have hfp (t : ℝ) : f (t + 1) = f t + 1 := by
    dsimp only [f]
    rw [hSp]
    ring
  obtain ⟨K, hK⟩ := exists_lipschitz_affinePeriodic (hfc.of_le (by simp)) hfp
  refine ⟨f, τ, K, hfc, hfp, hτ, ?_, hK, ?_⟩
  · intro x y hxy
    have h := mul_nonneg (by linarith : 0 ≤ 1 - τ) (sub_nonneg.mpr (hSm hxy))
    dsimp only [f]
    nlinarith
  · intro x
    have hτ' : 0 ≤ 1 - τ := by linarith
    have hx : |x - ψ x| ≤ B := by
      simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_sub_comm] using hb x
    calc
      dist (f x) (ψ x) = |(1 - τ) * (S x - ψ x) + τ * (x - ψ x)| := by
        rw [Real.dist_eq]
        congr 1
        dsimp only [f]
        ring
      _ ≤ |(1 - τ) * (S x - ψ x)| + |τ * (x - ψ x)| := abs_add_le _ _
      _ = (1 - τ) * dist (S x) (ψ x) + τ * |x - ψ x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hτ', abs_of_pos hτ, Real.dist_eq]
      _ ≤ (1 - τ) * (ε / 4) + τ * B :=
        add_le_add (mul_le_mul_of_nonneg_left (hSerr x) hτ')
          (mul_le_mul_of_nonneg_left hx hτ.le)
      _ < ε := by nlinarith

end DifferentialGeometry.Analysis
