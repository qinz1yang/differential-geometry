/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Curvature (vec2) in
theorem abs_metricTracePair0SAt_le_of_metric_le
    (g h : SmoothRiemannianMetric I M) (x : M) {C : ℝ}
    (hmetric : ∀ v : TangentSpace I x, h.inner x v v ≤ C * g.inner x v v)
    (T : Tensor0SSpace (I := I) 2 x) :
    |metricTracePair0SAt g T| ≤
      (Module.finrank ℝ E : ℝ) * C * Real.sqrt (normSq0S h x 2 T) := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g basis hON
  have htrace : metricTracePair0SAt g T =
      ∑ i, T (vec2 (basis i) (basis i)) := by
    rw [metricTracePair0SAt_eq_sum_basis g basis _ hinv]
    simp [identityInvMetric, diagonalInvMetric]
  rw [htrace]
  calc
    |∑ i, T (vec2 (basis i) (basis i))| ≤
        ∑ i, |T (vec2 (basis i) (basis i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        Real.sqrt (normSq0S h x 2 T) * C := by
      apply Finset.sum_le_sum
      intro i _
      have ha := abs_apply_le_norm0S h x 2 T (vec2 (basis i) (basis i))
      have hn : 0 ≤ h.inner x (basis i) (basis i) := by
        rcases eq_or_ne (basis i) 0 with hi | hi
        · rw [hi]; simp
        · exact (h.pos x (basis i) hi).le
      have hc : h.inner x (basis i) (basis i) ≤ C := by
        simpa only [hON i i, ite_true, mul_one] using hmetric (basis i)
      simp only [Fin.prod_univ_two, vec2, ite_self, Real.mul_self_sqrt hn] at ha
      exact ha.trans (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (Module.finrank ℝ E : ℝ) * (Real.sqrt (normSq0S h x 2 T) * C) = _
      ring

theorem abs_metricTracePair0SAt_le_of_metric_lower_bound
    (g h : SmoothRiemannianMetric I M) (x : M) {c : ℝ} (hc : 0 < c)
    (hmetric : ∀ v : TangentSpace I x, c * h.inner x v v ≤ g.inner x v v)
    (T : Tensor0SSpace (I := I) 2 x) :
    |metricTracePair0SAt g T| ≤
      (Module.finrank ℝ E : ℝ) / c * Real.sqrt (normSq0S h x 2 T) := by
  have hm (v : TangentSpace I x) : h.inner x v v ≤ c⁻¹ * g.inner x v v := by
    have hh := mul_le_mul_of_nonneg_left (hmetric v) (inv_pos.mpr hc).le
    simpa only [inv_mul_cancel_left₀ hc.ne'] using hh
  simpa only [div_eq_mul_inv] using abs_metricTracePair0SAt_le_of_metric_le g h x hm T

end

end DifferentialGeometry.Geometry.Operator
