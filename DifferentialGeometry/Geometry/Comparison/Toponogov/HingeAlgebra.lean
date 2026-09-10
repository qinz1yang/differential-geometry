/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngleOrder
import DifferentialGeometry.Geometry.Metric.TangentAngle

set_option autoImplicit false

noncomputable section

open Set

namespace Poincare.Toponogov

theorem comparisonAngle_le_of_hinge_sq
    {a b c θ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hreverse : |a - b| ≤ c) (htriangle : c ≤ a + b)
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi)
    (hhinge : c ^ 2 ≤
      a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ) :
    comparisonAngle a b c ≤ θ := by
  exact (comparisonAngle_le_iff_sq_le_cos ha hb hreverse htriangle
    hθ.1 hθ.2).2 hhinge

theorem metricComparisonAngle_le_of_hinge_sq
    {X : Type*} [MetricSpace X] {x o y : X} {θ : ℝ}
    (hxo : x ≠ o) (hyo : y ≠ o)
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi)
    (hhinge : dist x y ^ 2 ≤
      dist o x ^ 2 + dist o y ^ 2 -
        2 * dist o x * dist o y * Real.cos θ) :
    metricComparisonAngle x o y ≤ θ := by
  have hx : 0 < dist o x := dist_pos.mpr hxo.symm
  have hy : 0 < dist o y := dist_pos.mpr hyo.symm
  have hside := metricComparisonAngle_sideInequalities x o y
  exact comparisonAngle_le_of_hinge_sq hx hy hside.1 hside.2 hθ hhinge

theorem equalArm_le_two_mul_sin_half_of_sq_le
    {a c θ : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi)
    (hhinge : c ^ 2 ≤ 2 * a ^ 2 * (1 - Real.cos θ)) :
    c ≤ 2 * a * Real.sin (θ / 2) := by
  have hsin : 0 ≤ Real.sin (θ / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hrhs : 0 ≤ 2 * a * Real.sin (θ / 2) := by positivity
  have hhalf : 2 * Real.sin (θ / 2) ^ 2 = 1 - Real.cos θ := by
    have h := Real.cos_two_mul_eq_one_sub (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    linarith
  apply (sq_le_sq₀ hc hrhs).mp
  calc
    c ^ 2 ≤ 2 * a ^ 2 * (1 - Real.cos θ) := hhinge
    _ = (2 * a * Real.sin (θ / 2)) ^ 2 := by rw [← hhalf]; ring

section TangentAngle

open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry
open Poincare.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem comparisonAngle_le_tangentAngle_of_unit_hinge
    (g : SmoothRiemannianMetric I M) {x : M}
    {v w : TangentSpace I x}
    (hv : IsUnitTangent g v) (hw : IsUnitTangent g w)
    {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hreverse : |a - b| ≤ c) (htriangle : c ≤ a + b)
    (hhinge : c ^ 2 ≤
      a ^ 2 + b ^ 2 - 2 * a * b * g.inner x v w) :
    comparisonAngle a b c ≤ tangentAngle g v w := by
  apply comparisonAngle_le_of_hinge_sq ha hb hreverse htriangle
    (tangentAngle_mem_Icc g v w)
  rw [cos_tangentAngle_of_unit g hv hw]
  exact hhinge

theorem equalArm_le_two_mul_sin_half_tangentAngle_of_unit
    (g : SmoothRiemannianMetric I M) {x : M}
    {v w : TangentSpace I x}
    (hv : IsUnitTangent g v) (hw : IsUnitTangent g w)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hhinge : c ^ 2 ≤ 2 * a ^ 2 * (1 - g.inner x v w)) :
    c ≤ 2 * a * Real.sin (tangentAngle g v w / 2) := by
  apply equalArm_le_two_mul_sin_half_of_sq_le ha hc
    (tangentAngle_mem_Icc g v w)
  rw [cos_tangentAngle_of_unit g hv hw]
  exact hhinge

end TangentAngle

section Regression


example {a : ℝ} (ha : 0 ≤ a) :
    2 * a = 2 * a * Real.sin (Real.pi / 2) := by
  apply le_antisymm
  · apply equalArm_le_two_mul_sin_half_of_sq_le ha (by positivity)
      ⟨Real.pi_pos.le, le_rfl⟩
    rw [Real.cos_pi]
    ring_nf
    exact le_rfl
  · simp

example {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hhinge : c ^ 2 ≤ 2 * a ^ 2 * (1 - Real.cos 0)) :
    c = 0 := by
  have hle : c ≤ 2 * a * Real.sin (0 / 2) :=
    equalArm_le_two_mul_sin_half_of_sq_le ha hc
      ⟨le_rfl, Real.pi_pos.le⟩ hhinge
  norm_num at hle
  exact le_antisymm hle hc

end Regression

end Poincare.Toponogov
