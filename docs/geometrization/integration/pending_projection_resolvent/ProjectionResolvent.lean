import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionSpectrum

set_option autoImplicit false

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 H]

theorem mem_resolventSet_of_norm_sub_starProjection_lt
    (A : H →L[𝕜] H) (P : Submodule 𝕜 H) {μ : 𝕜}
    (hclose : ‖A - P.starProjection‖ < min ‖μ‖ ‖μ - 1‖) :
    μ ∈ resolventSet 𝕜 A := by
  let : CompleteSpace H := FiniteDimensional.complete 𝕜 H
  let B : H →L[𝕜] H := algebraMap 𝕜 (H →L[𝕜] H) μ - A
  have hinj : Function.Injective B := by
    intro u v huv
    have hz : B (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hl := norm_smul_sub_apply_ge_of_norm_sub_starProjection_le A P le_rfl μ (u - v)
    change (min ‖μ‖ ‖μ - 1‖ - ‖A - P.starProjection‖) * ‖u - v‖ ≤ ‖B (u - v)‖ at hl
    rw [hz, norm_zero] at hl
    have hnorm : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, LinearMap.injective_iff_surjective.mp (show Function.Injective B.toLinearMap from hinj)⟩

theorem norm_resolvent_le_of_norm_sub_starProjection_le
    (A : H →L[𝕜] H) (P : Submodule 𝕜 H) {μ : 𝕜} {ε : ℝ}
    (hclose : ‖A - P.starProjection‖ ≤ ε) (hgap : ε < min ‖μ‖ ‖μ - 1‖) :
    ‖resolvent A μ‖ ≤ 1 / (min ‖μ‖ ‖μ - 1‖ - ε) := by
  let B : H →L[𝕜] H := algebraMap 𝕜 (H →L[𝕜] H) μ - A
  have hunit : IsUnit B := mem_resolventSet_of_norm_sub_starProjection_lt A P (hclose.trans_lt hgap)
  have hpos : 0 < min ‖μ‖ ‖μ - 1‖ - ε := sub_pos.mpr hgap
  have hleft (v : H) : B ((Ring.inverse B) v) = v :=
    congrArg (fun T : H →L[𝕜] H => T v) (Ring.mul_inverse_cancel B hunit)
  apply opNorm_le_bound _ (by positivity)
  intro v
  have hl := norm_smul_sub_apply_ge_of_norm_sub_starProjection_le A P hclose μ ((Ring.inverse B) v)
  change (min ‖μ‖ ‖μ - 1‖ - ε) * ‖(Ring.inverse B) v‖ ≤ ‖B ((Ring.inverse B) v)‖ at hl
  rw [hleft] at hl
  change ‖(Ring.inverse B) v‖ ≤ _
  calc
    ‖(Ring.inverse B) v‖ ≤ ‖v‖ / (min ‖μ‖ ‖μ - 1‖ - ε) :=
      (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hl)
    _ = 1 / (min ‖μ‖ ‖μ - 1‖ - ε) * ‖v‖ := by ring

end ContinuousLinearMap
