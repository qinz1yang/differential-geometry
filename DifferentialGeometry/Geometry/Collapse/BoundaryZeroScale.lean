import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-! A genuinely negative tangent plane bounds the normalized zero-stratum scale. -/

set_option autoImplicit false

open Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Curvature

universe uE uH uM

theorem zeroScale_le_of_negative_plane {r A K : ℝ} (hr : 0 < r) (hA : 0 < A)
    (hlower : -(1 / (60 * r) ^ 2) * A ≤ K) (hupper : K ≤ -(1 / 8) * A) :
    r ≤ Real.sqrt 8 / 60 ∧ r < 1 / 20 := by
  have hinv : (1 : ℝ) / 8 ≤ 1 / (60 * r) ^ 2 := by
    nlinarith [hlower.trans hupper]
  have hsquare : (60 * r) ^ 2 ≤ 8 := by
    have hpos : 0 < (60 * r) ^ 2 := by positivity
    have hmul := (le_div_iff₀ hpos).mp hinv
    nlinarith
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
  have hsqrtpos := Real.sqrt_nonneg 8
  have hbound : r ≤ Real.sqrt 8 / 60 := by nlinarith
  have hsmall : Real.sqrt 8 / 60 < (1 : ℝ) / 20 := by nlinarith
  exact ⟨hbound, hbound.trans_lt hsmall⟩

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem zeroScale_le_of_sectional_lower_bound
    (g : SmoothRiemannianMetric I M) (x : M) {r : ℝ} (hr : 0 < r)
    (v w : TangentSpace I x)
    (hplane : 0 < g.inner x v v * g.inner x w w - g.inner x v w ^ 2)
    (hlower : SectionalBoundedBelowAt g x (-(1 / (60 * r) ^ 2)))
    (hupper : metricRm04StandardAt (I := I) (M := M) g x v w w v ≤
      -(1 / 8) * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2)) :
    r ≤ Real.sqrt 8 / 60 ∧ r < 1 / 20 :=
  zeroScale_le_of_negative_plane hr hplane (hlower v w) hupper

theorem zeroScale_negative_quarter_regression :
    (1 : ℝ) / 100 ≤ Real.sqrt 8 / 60 ∧ (1 : ℝ) / 100 < 1 / 20 :=
  zeroScale_le_of_negative_plane (A := 1) (K := -(1 / 4))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end DifferentialGeometry.Geometry.Riemannian
