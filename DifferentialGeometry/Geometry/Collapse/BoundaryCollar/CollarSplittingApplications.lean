import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplitting

/-!
# Consumers of the collar splitting (F-f.B)

* `NearlyCuspidalBoundary.hasEuclideanSplitting_collar`: every collar point of every component of
  a nearly cuspidal boundary at height `5 ≤ z ≤ 95` splits off a line at scale `β` in
  `(W, r⁻¹ d_g)` once `δ ≤ β²/1000` and `0 < r ≤ β³/2000`.
* `NearlyCuspidalBoundary.one_le_splittingRank_collar`: hence its splitting rank (with any
  parameters `β_k`, `β_1 = β`, any cap `N ≥ 1`) is at least one; the zero stratum is excluded on
  this band (the last sentence of BCP02).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- F-f.B on every collar of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.hasEuclideanSplitting_collar [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) {q₀ : CuspHalfSpace} {β r : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hz5 : 5 ≤ q₀.2.val 0) (hz95 : q₀.2.val 0 ≤ 95)
    (hδ : δ ≤ β ^ 2 / 1000) (hr : 0 < r) (hrβ : r ≤ β ^ 3 / 2000) :
    @HasEuclideanSplitting.{u, 0} W.Carrier ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr))
      ((B.collar i).toFun q₀) 1 β :=
  (B.collar i).hasEuclideanSplitting_frozen_of_small hβ hβ1 hz5 hz95 hδ hr hrβ

/-- The zero stratum is excluded on the collar band: the splitting rank is at least one. -/
theorem NearlyCuspidalBoundary.one_le_splittingRank_collar [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) {q₀ : CuspHalfSpace} {r : ℝ}
    (βs : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) (hβ : 0 < βs 1) (hβ1 : βs 1 < 1)
    (hz5 : 5 ≤ q₀.2.val 0) (hz95 : q₀.2.val 0 ≤ 95) (hδ : δ ≤ βs 1 ^ 2 / 1000) (hr : 0 < r)
    (hrβ : r ≤ βs 1 ^ 3 / 2000) :
    1 ≤ @splittingRank.{u, 0} W.Carrier ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr))
      ((B.collar i).toFun q₀) βs N :=
  @le_splittingRank.{u, 0} W.Carrier ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr))
    ((B.collar i).toFun q₀) βs N 1 hN
    (B.hasEuclideanSplitting_collar i hβ hβ1 hz5 hz95 hδ hr hrβ)

end DifferentialGeometry.Geometry.Collapse
