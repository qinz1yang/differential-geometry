import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarLowerDistance
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspProductUpperDistance

/-!
# Consumers of F-f.L: two-sided frozen comparison of a cusp collar

* `NearlyCuspidalBoundary.frozen_le_riemannianEDistOf`: F-f.L for every collar of a nearly
  cuspidal boundary;
* `CuspEmbedding.frozen_two_sided`: at interior heights (`a/2 < z₀`, `z₀ + a < 100`), for points
  with heights within `a/2` of `z₀` and `d_g < √(1 - δ) a / 2`, the actual distance is pinched
  between `√(1 - δ) e^{-a/2} D` (F-f.L) and `√((1 + δ) e^{a/2}) D` (F-f.U, B-2b), where
  `D = √((z' - z)² + e^{-z₀} d_q(t, t')²)` is the frozen product distance.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- F-f.L for the collars of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.frozen_le_riemannianEDistOf {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) {p p' : CuspHalfSpace} {z₀ a : ℝ}
    (hup : z₀ + a < cuspDepth) (hp : |p.2.val 0 - z₀| ≤ a / 2) (hp' : |p'.2.val 0 - z₀| ≤ a / 2)
    (hd : riemannianEDistOf g ((B.collar i).toFun p) ((B.collar i).toFun p') <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (a / 2))) :
    ENNReal.ofReal (Real.sqrt (1 - δ) * (Real.exp (-a / 2) *
        Real.sqrt ((p'.2.val 0 - p.2.val 0) ^ 2 + Real.exp (-z₀) *
          (riemannianEDistOf (B.collar i).cusp.torusMetric p.1 p'.1).toReal ^ 2))) ≤
      riemannianEDistOf g ((B.collar i).toFun p) ((B.collar i).toFun p') :=
  (B.collar i).frozen_le_riemannianEDistOf hup hp hp' hd

/-- Two-sided frozen comparison at interior heights (F-f.L and F-f.U). -/
theorem CuspEmbedding.frozen_two_sided {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p p' : CuspHalfSpace} {z₀ a : ℝ} (hlow : a / 2 < z₀)
    (hup : z₀ + a < cuspDepth) (hp : |p.2.val 0 - z₀| ≤ a / 2) (hp' : |p'.2.val 0 - z₀| ≤ a / 2)
    (hd : riemannianEDistOf g (e.toFun p) (e.toFun p') <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (a / 2))) :
    ENNReal.ofReal (Real.sqrt (1 - δ) * (Real.exp (-a / 2) *
        Real.sqrt ((p'.2.val 0 - p.2.val 0) ^ 2 + Real.exp (-z₀) *
          (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2))) ≤
      riemannianEDistOf g (e.toFun p) (e.toFun p') ∧
    riemannianEDistOf g (e.toFun p) (e.toFun p') ≤ ENNReal.ofReal (Real.sqrt
      ((1 + δ) * Real.exp (a / 2) * ((p'.2.val 0 - p.2.val 0) ^ 2 +
        Real.exp (-z₀) * (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2))) := by
  have ha : 0 ≤ a := by have := (abs_nonneg _).trans hp; linarith
  have hup' : z₀ + a / 2 < 100 := by
    have : z₀ + a / 2 ≤ z₀ + a := by linarith
    exact lt_of_le_of_lt this hup
  exact ⟨e.frozen_le_riemannianEDistOf hup hp hp' hd,
    e.riemannianEDistOf_le_frozen_product hlow hup' hp hp'⟩

end DifferentialGeometry.Geometry.Collapse
