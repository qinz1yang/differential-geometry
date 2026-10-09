import DifferentialGeometry.Geometry.Metric.Approximation.Bilipschitz
import DifferentialGeometry.Geometry.Metric.Approximation.RealSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation

/-!
# Rank-one splittings from bi-Lipschitz product comparisons (foundation F-f, metric kernel)

`hasEuclideanSplitting_one_of_bilipschitz_product`: a map `F : X → ℝ ×₂ Y` sending `p` to `(0, y₀)`
which is `(1 ± a)`-bi-Lipschitz on the closed ball `B̄(p, β⁻¹ + β)` and `β/4`-covers the target ball
of radius `β⁻¹ + β - β/4` around `(0, y₀)` is a rank-one Kleiner–Lott splitting at scale `β`,
provided the distortion budget `2a(β⁻¹ + β) < β/4` holds.

This is the interface of the actual cusp splitting maps of BCP02 (blueprint 207B, `B:8212–8321`):
the hypotheses are the DISTORTION and the COVERAGE of the map itself, in the source and target
distances, as required by the foundations review (§3.4). Proof: `PointedBallApprox.ofBilipschitz`,
`PointedBallApprox.toKleinerLott`, `hasEuclideanSplitting_one_iff`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v

/-- F-f.K1: a bi-Lipschitz map of the buffered ball into `ℝ ×₂ Y` with coverage gives a rank-one
Kleiner–Lott splitting. -/
theorem hasEuclideanSplitting_one_of_bilipschitz_product {X : Type u} [MetricSpace X]
    {Y : Type v} [MetricSpace Y] {p : X} {y₀ : Y} {β a : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (ha : 0 ≤ a) (ha1 : a < 1) (herr : 2 * a * (β⁻¹ + β) < β / 4)
    (F : X → WithLp 2 (ℝ × Y)) (hbase : F p = WithLp.toLp 2 (0, y₀))
    (hdist : ∀ x x', dist x p ≤ β⁻¹ + β → dist x' p ≤ β⁻¹ + β →
      (1 - a) * dist x x' ≤ dist (F x) (F x') ∧ dist (F x) (F x') ≤ (1 + a) * dist x x')
    (hcov : ∀ y, dist y (WithLp.toLp 2 ((0 : ℝ), y₀)) ≤ β⁻¹ + β - β / 4 →
      ∃ x, dist x p ≤ β⁻¹ + β ∧ dist y (F x) < β / 4) :
    HasEuclideanSplitting.{u, v} p 1 β := by
  have hε : 0 < β / 4 := by positivity
  have hεR : β / 4 < β⁻¹ + β := by
    have := inv_pos.mpr hβ
    linarith
  let f : PointedBallApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) (β⁻¹ + β) (β / 4) :=
    PointedBallApprox.ofBilipschitz ⟨ha, ha1⟩ hε hεR herr (fun x => F x.val) hbase
      (fun x x' => hdist x.val x'.val x.property x'.property)
      (fun y hy => by
        obtain ⟨x, hx, hxy⟩ := hcov y hy
        exact ⟨⟨x, hx⟩, hxy⟩)
  exact hasEuclideanSplitting_one_iff.mpr
    ⟨Y, inferInstance, y₀, ⟨f.toKleinerLott hβ hβ1⟩⟩

end GC.MetricGeometry
