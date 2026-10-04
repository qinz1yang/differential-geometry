import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspProductUpperDistance
import DifferentialGeometry.Geometry.Metric.Approximation.ProductComparisonSplitting

/-!
# Consumers of the F-f kernels

* `NearlyCuspidalBoundary.riemannianEDistOf_le_frozen_product`: the upper frozen-product
  distortion (F-f.U) on every collar of an actual nearly cuspidal boundary.
* `hasEuclideanSplitting_one_withLp_prod`: the model `ℝ ×₂ Y` itself has a rank-one splitting at
  every scale `β ∈ (0, 1)` at every point `(0, y₀)`, through the bi-Lipschitz kernel F-f.K1 with
  zero distortion.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u v

/-- F-f.U on every collar of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.riemannianEDistOf_le_frozen_product {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) {p p' : CuspHalfSpace} {z₀ a : ℝ}
    (hlow : a < z₀) (hup : z₀ + a < 100) (hp : |p.2.val 0 - z₀| ≤ a)
    (hp' : |p'.2.val 0 - z₀| ≤ a) :
    riemannianEDistOf g ((B.collar i).toFun p) ((B.collar i).toFun p') ≤
      ENNReal.ofReal (Real.sqrt ((1 + δ) * Real.exp a * ((p'.2.val 0 - p.2.val 0) ^ 2 +
        Real.exp (-z₀) * (riemannianEDistOf (B.collar i).cusp.torusMetric p.1 p'.1).toReal ^ 2))) :=
  (B.collar i).riemannianEDistOf_le_frozen_product hlow hup hp hp'

/-- The model `ℝ ×₂ Y` splits off a line at `(0, y₀)` at every scale `β ∈ (0, 1)`, by F-f.K1
applied to the identity. -/
theorem hasEuclideanSplitting_one_withLp_prod {Y : Type u} [MetricSpace Y] (y₀ : Y) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) :
    HasEuclideanSplitting.{u, u} (WithLp.toLp 2 ((0 : ℝ), y₀)) 1 β := by
  refine hasEuclideanSplitting_one_of_bilipschitz_product hβ hβ1 le_rfl zero_lt_one
    (by simpa using (by positivity : (0 : ℝ) < β / 4)) id rfl
    (fun x x' _ _ => by simp) (fun y hy => ⟨y, ?_, by simpa using hβ⟩)
  have h4 : 0 ≤ β / 4 := by positivity
  linarith

end DifferentialGeometry.Geometry.Collapse
