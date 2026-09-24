import DifferentialGeometry.Geometry.Curvature.Riemann.Tensor
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem sqrt_le_of_le_mul_sqrt {a B : Real} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (h : a ≤ B * Real.sqrt a) : Real.sqrt a ≤ B := by
  rcases (Real.sqrt_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]
    exact hB
  · nlinarith [Real.mul_self_sqrt ha]

theorem norm_connection_variation_le_of_metric_comparison
    (g₀ g : SmoothRiemannianMetric I M) (y : M)
    (NRy : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 y)
    (Zy a b : TangentSpace I y) {r c : Real}
    (hkos : ∀ v : TangentSpace I y,
      g.inner y Zy v =
        -NRy (vec3 (I := I) a b v) - NRy (vec3 (I := I) b a v)
          + NRy (vec3 (I := I) v a b))
    (hNR : Real.sqrt (normSq0S (I := I) g y 3 NRy) ≤ r)
    (hlow : ∀ v : TangentSpace I y,
      Real.sqrt (g₀.inner y v v) ≤ Real.exp c * Real.sqrt (g.inner y v v))
    (hup : ∀ v : TangentSpace I y,
      Real.sqrt (g.inner y v v) ≤ Real.exp c * Real.sqrt (g₀.inner y v v)) :
    Real.sqrt (g₀.inner y Zy Zy) ≤
      3 * r * Real.exp (3 * c) *
        Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by
  classical
  have hr : 0 ≤ r := (Real.sqrt_nonneg _).trans hNR
  have hprod : ∀ p q z : TangentSpace I y,
      (∏ i : Fin 3, Real.sqrt (g.inner y
          (vec3 (I := I) p q z i) (vec3 (I := I) p q z i))) =
        Real.sqrt (g.inner y p p) * Real.sqrt (g.inner y q q) *
          Real.sqrt (g.inner y z z) := by
    intro p q z
    rw [Fin.prod_univ_three]
    simp [vec3]
  have hterm : ∀ p q z : TangentSpace I y,
      |NRy (vec3 (I := I) p q z)| ≤
        Real.sqrt (normSq0S (I := I) g y 3 NRy) *
          (Real.sqrt (g.inner y p p) * Real.sqrt (g.inner y q q) *
            Real.sqrt (g.inner y z z)) := by
    intro p q z
    have h := abs_apply_le_norm0S (I := I) g y 3 NRy (vec3 (I := I) p q z)
    rw [hprod p q z] at h
    exact h
  have hNRnn : 0 ≤ Real.sqrt (normSq0S (I := I) g y 3 NRy) := Real.sqrt_nonneg _
  have hpair : ∀ v : TangentSpace I y,
      |g.inner y Zy v| ≤
        3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
          Real.sqrt (g.inner y a a) * Real.sqrt (g.inner y b b) *
          Real.sqrt (g.inner y v v) := by
    intro v
    rw [hkos v]
    obtain ⟨h1a, h1b⟩ := abs_le.mp (hterm a b v)
    obtain ⟨h2a, h2b⟩ := abs_le.mp (hterm b a v)
    obtain ⟨h3a, h3b⟩ := abs_le.mp (hterm v a b)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hZg : Real.sqrt (g.inner y Zy Zy) ≤
      3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
        Real.sqrt (g.inner y a a) * Real.sqrt (g.inner y b b) := by
    refine sqrt_le_of_le_mul_sqrt
      (DifferentialGeometry.metric_inner_self_nonneg
        (I := I) (M := M) g y Zy)
      (by positivity) ?_
    exact le_trans (le_abs_self _) (hpair Zy)
  have hstep1 : 3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) ≤ 3 * r :=
    mul_le_mul_of_nonneg_left hNR (by norm_num)
  have hstep2 : 3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
      Real.sqrt (g.inner y a a) ≤
      3 * r * (Real.exp c * Real.sqrt (g₀.inner y a a)) :=
    mul_le_mul hstep1 (hup a) (Real.sqrt_nonneg _) (by linarith)
  have hstep3 : 3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
      Real.sqrt (g.inner y a a) * Real.sqrt (g.inner y b b) ≤
      3 * r * (Real.exp c * Real.sqrt (g₀.inner y a a)) *
        (Real.exp c * Real.sqrt (g₀.inner y b b)) := by
    refine mul_le_mul hstep2 (hup b) (Real.sqrt_nonneg _) ?_
    have : 0 ≤ Real.exp c * Real.sqrt (g₀.inner y a a) := by positivity
    nlinarith [hr]
  have hexp3 : Real.exp (3 * c) = Real.exp c * Real.exp c * Real.exp c := by
    rw [show (3 : Real) * c = c + c + c by ring, Real.exp_add, Real.exp_add]
  calc Real.sqrt (g₀.inner y Zy Zy)
      ≤ Real.exp c * Real.sqrt (g.inner y Zy Zy) := hlow Zy
    _ ≤ Real.exp c * (3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
          Real.sqrt (g.inner y a a) * Real.sqrt (g.inner y b b)) :=
        mul_le_mul_of_nonneg_left hZg (Real.exp_nonneg c)
    _ ≤ Real.exp c * (3 * r * (Real.exp c * Real.sqrt (g₀.inner y a a)) *
          (Real.exp c * Real.sqrt (g₀.inner y b b))) :=
        mul_le_mul_of_nonneg_left hstep3 (Real.exp_nonneg c)
    _ = 3 * r * Real.exp (3 * c) *
          Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by
        rw [hexp3]
        ring

end DifferentialGeometry.Geometry.Connection

end
