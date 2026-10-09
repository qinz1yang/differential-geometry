import DifferentialGeometry.Geometry.Metric.RadialCurvature

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold InnerProductSpace Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem radialBilinearField_gram (a : ℝ → ℝ) {x : E} (hx : x ≠ 0) (u v : E) :
    let r := ‖x‖
    let uT := u - (⟪x, u⟫_ℝ / r ^ 2) • x
    let vT := v - (⟪x, v⟫_ℝ / r ^ 2) • x
    radialBilinearField a x u u * radialBilinearField a x v v -
      radialBilinearField a x u v ^ 2 =
      a r ^ 2 / r ^ 4 * ‖⟪x, u⟫_ℝ • v - ⟪x, v⟫_ℝ • u‖ ^ 2 +
        a r ^ 4 / r ^ 4 * (‖uT‖ ^ 2 * ‖vT‖ ^ 2 - ⟪uT, vT⟫_ℝ ^ 2) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  dsimp only
  simp only [radialBilinearField_apply, ← real_inner_self_eq_norm_sq,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  rw [real_inner_self_eq_norm_sq x]
  field_simp
  ring

theorem metricRm04StdAt_radialBilinearField_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {a : ℝ → ℝ} {x : E}
    (hg : (fun y : E => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : ContDiff ℝ ∞ a) (hx : x ≠ 0) (hapos : 0 < a ‖x‖)
    (hconc : deriv (deriv a) ‖x‖ < 0) (hslope : |deriv a ‖x‖| < 1) (u v : E)
    (hplane : 0 <
      g.inner x ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u)
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u) *
      g.inner x ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v) -
      (g.inner x ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u)
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)) ^ 2) :
    0 < metricRm04StandardAt (I := 𝓘(ℝ, E)) g x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u) := by
  let B := ‖⟪x, u⟫_ℝ • v - ⟪x, v⟫_ℝ • u‖ ^ 2
  let uT := u - (⟪x, u⟫_ℝ / ‖x‖ ^ 2) • x
  let vT := v - (⟪x, v⟫_ℝ / ‖x‖ ^ 2) • x
  let D := ‖uT‖ ^ 2 * ‖vT‖ ^ 2 - ⟪uT, vT⟫_ℝ ^ 2
  have hB : 0 ≤ B := sq_nonneg _
  have hD : 0 ≤ D := by
    simpa only [D, real_inner_self_eq_norm_sq, ← pow_two, sub_nonneg] using
      real_inner_mul_inner_self_le uT vT
  have hGram : 0 < a ‖x‖ ^ 2 / ‖x‖ ^ 4 * B + a ‖x‖ ^ 4 / ‖x‖ ^ 4 * D := by
    change 0 < tangentBilinearFormToModel x (g.inner x) u u *
      tangentBilinearFormToModel x (g.inner x) v v -
      tangentBilinearFormToModel x (g.inner x) u v ^ 2 at hplane
    rw [hg.eq_of_nhds, radialBilinearField_gram a hx u v] at hplane
    exact hplane
  have hpos : 0 < B ∨ 0 < D := by
    by_contra! h
    have hB0 : B = 0 := le_antisymm h.1 hB
    have hD0 : D = 0 := le_antisymm h.2 hD
    rw [hB0, hD0] at hGram
    norm_num at hGram
  have hR : 0 < -a ‖x‖ * deriv (deriv a) ‖x‖ / ‖x‖ ^ 4 :=
    div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hapos) hconc)
      (pow_pos (norm_pos_iff.mpr hx) 4)
  have hT : 0 < a ‖x‖ ^ 2 * (1 - deriv a ‖x‖ ^ 2) / ‖x‖ ^ 4 :=
    div_pos (mul_pos (sq_pos_of_pos hapos)
      (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr hslope)))
      (pow_pos (norm_pos_iff.mpr hx) 4)
  rw [metricRm04StdAt_radialBilinearField_plane g hg ha hx hapos.ne' u v]
  change 0 < _ * B + _ * D
  rcases hpos with hpos | hpos
  · exact add_pos_of_pos_of_nonneg (mul_pos hR hpos) (mul_nonneg hT.le hD)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hR.le hB) (mul_pos hT hpos)

end DifferentialGeometry.Geometry.Riemannian
