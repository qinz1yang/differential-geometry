import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarAssembly
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspVolumeTransfer

/-!
# Statement G, volume binding: `vol B(p, r) ≤ 1000 δ² r` in a nearly cuspidal collar

Blueprint 207B, BSA01 (ii), (vi) (`B:7606–7611`, BCP01 proof `B:8159–8162`). The volume kernel
`CuspEmbedding.ballVolume_le_of_volume_transfer` with its input discharged by the volume transfer
V.1 (`CuspEmbedding.volume_transfer`, lane BDY-V) and the area bound by G-diam:

* `NearlyCuspidalBoundary.ballVolume_le_thousand`: for `δ ≤ 1/100`, `z(p) ≤ 96` and `r ≤ 1`,
  `vol B(e_i p, r) ≤ 1000 δ² r` (BSA01 (ii) with `96` for `95`; BCP01's `(vi)`);
* `NearlyCuspidalBoundary.ballVolume_le_thousand_of_distanceToBoundary_le_ten`: the volume part of
  the first clause of `G_consumer_clauses`;
* `G_consumer_clauses_of_pinching`: the interface `G_consumer_clauses` verbatim, with only the cusp
  pinching of lane FT-C as hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open GC.Endpoint DifferentialGeometry.Topology.Manifold DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **BSA01 (ii)/(vi), volume.** For `δ ≤ 1/100`, every ball `B(e_i p, r)` of a collar of a nearly
cuspidal boundary with `z(p) ≤ 96` and `r ≤ 1` has volume at most `1000 δ² r`. -/
theorem NearlyCuspidalBoundary.ballVolume_le_thousand {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100) (i : Fin B.count)
    {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 96) {r : ℝ} (hr : r ≤ 1) :
    ballVolume g ((B.collar i).toFun p) r ≤ ENNReal.ofReal (1000 * δ ^ 2 * r) :=
  B.ballVolume_le_of_volume_transfer hδ i (fun _ hS hSd =>
    ((B.collar i).volume_transfer (B.collar i).delta_nonneg (by linarith) hS hSd).2) hp hr

/-- **BSA01 (ii), near the boundary.** For `δ ≤ 1/100`, every point within `10` of `∂W` has
`vol B(p, a) ≤ 1000 δ² a` for `0 < a ≤ 1`. -/
theorem NearlyCuspidalBoundary.ballVolume_le_thousand_of_distanceToBoundary_le_ten
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100) {p : W.Carrier}
    (hp : distanceToBoundary W g p ≤ ENNReal.ofReal 10) :
    ∀ a : ℝ, 0 < a → a ≤ 1 → ballVolume g p a ≤ ENNReal.ofReal (1000 * δ ^ 2 * a) :=
  B.ballVolume_le_of_distanceToBoundary_le_ten hδ (fun i _ hS hSd =>
    ((B.collar i).volume_transfer (B.collar i).delta_nonneg (by linarith) hS hSd).2) hp

/-- **G (consumer clauses), modulo the cusp pinching.** The frozen interface `G_consumer_clauses`,
verbatim, from the cusp pinching of lane FT-C (BSA01 (i), sectional part, `K ≥ 2`, `δ ≤ δ₁`). -/
theorem G_consumer_clauses_of_pinching
    (hpinch : ∃ δ₁ > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ) (X : Set W.Carrier) (e : CuspEmbedding W g K δ X), 2 ≤ K → 0 ≤ δ →
      δ ≤ δ₁ → ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 → ∀ u w : TangentSpace W.model (e.toFun q),
        -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
            metricRm04StandardAt g (e.toFun q) u w w u ∧
          metricRm04StandardAt g (e.toFun q) u w w u ≤
            -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2)) :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ), 2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      (∀ p, distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
        1 ≤ curvatureRadius g p ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
          ballVolume g p a ≤ ENNReal.ofReal (1000 * δ ^ 2 * a)) ∧
      (ConnectedSpace W.Carrier → ∀ p, distanceToBoundary W g p < ⊤ ∧
        curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3) :=
  G_consumer_clauses_of_pinching_of_volume_transfer hpinch
    fun _ _ _ _ _ e h0 h1 _ hS hSd => (e.volume_transfer h0 h1 hS hSd).2

end DifferentialGeometry.Geometry.Collapse
