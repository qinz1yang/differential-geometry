import DifferentialGeometry.Geometry.Metric.CloudSmoothingModulusRow

/-!
# Consumers of the threshold modulus (CFS15)

* `exists_modulus_le_self`: for the trivial predicate `Γ ≤ ε` the modulus dominates the quality,
  `Γ ≤ Ξ(Γ)`, and still tends to zero.
* `cfs15_modulus_le_sixteenth`: the CFS15 modulus has values at most `1/16`.
-/

set_option autoImplicit false

open Filter Topology

namespace GC.MetricGeometry

/-- The modulus for the predicate `Γ ≤ ε`. -/
theorem exists_modulus_le_self :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → Γ ≤ Ξ Γ := by
  obtain ⟨θ₁, hθ, Ξ, hlim, hΞ⟩ :=
    DifferentialGeometry.Analysis.ParameterSelection.exists_modulus_of_thresholds
      (P := fun ε Γ => Γ ≤ ε) (fun m => ⟨(1 / 2 : ℝ) ^ (m + 4), by positivity,
        fun _ _ hΓ => hΓ⟩)
  exact ⟨θ₁, hθ, Ξ, hlim, fun Γ hΓ hΓθ => (hΞ Γ hΓ hΓθ).2⟩

/-- The CFS15 modulus takes values in `(0, 1/16]`. -/
theorem cfs15_modulus_le_sixteenth (k K : ℕ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → 0 < Ξ Γ ∧ Ξ Γ ≤ 1 / 16 := by
  obtain ⟨θ₁, hθ, Ξ, hlim, hΞ⟩ := cfs15_modulus_row.{0} k K 1 le_rfl
  refine ⟨θ₁, hθ, Ξ, hlim, fun Γ hΓ hΓθ => ?_⟩
  obtain ⟨m, hm⟩ := (hΞ Γ hΓ hΓθ).1
  rw [hm]
  refine ⟨by positivity, ?_⟩
  calc (1 / 2 : ℝ) ^ (m + 4) ≤ (1 / 2 : ℝ) ^ 4 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 16 := by norm_num

end GC.MetricGeometry
