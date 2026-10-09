import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarVolume

/-!
# Consumer of the G-vol kernel: the volume part of the first clause of `G_consumer_clauses`

`NearlyCuspidalBoundary.ballVolume_le_of_distanceToBoundary_le_ten`: for a nearly cuspidal
boundary with `δ ≤ 1/100` whose collars satisfy the upper half of V.1 (lane BDY-V), every point
`p` with `d(p, ∂W) ≤ 10` has `vol B(p, a) ≤ 1000 δ² a` for `0 < a ≤ 1` (blueprint 207B, BSA01 (ii)
and (iii), `B:7606–7613`): `p` is a collar point of height `< 11 ≤ 96` (BSA01 (iii)), and the
collar volume kernel applies. This is the shape read by `StandingSequence.lean`'s `hnear`.
-/

set_option autoImplicit false

noncomputable section

open Set Function MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open GC.Endpoint DifferentialGeometry.Topology.Manifold DifferentialGeometry.Integral.Measure
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **BSA01 (ii), near the boundary.** Under the upper half of V.1 on every collar and
`δ ≤ 1/100`, every point within `10` of `∂W` has `vol B(p, a) ≤ 1000 δ² a` for `0 < a ≤ 1`. -/
theorem NearlyCuspidalBoundary.ballVolume_le_of_distanceToBoundary_le_ten
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100)
    (hV : ∀ (i : Fin B.count) (S : Set (Torus × ℝ)), MeasurableSet[borel (Torus × ℝ)] S →
      (∀ q ∈ S, 0 ≤ q.2 ∧ q.2 < cuspDepth) →
      riemannianVolumeMeasure W.model W.Carrier g
          ((B.collar i).toFun '' ((fun q : Torus × ℝ => (q.1, halfSpaceOneLift q.2)) '' S)) ≤
        ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2)) *
          (@Measure.prod Torus ℝ (borel Torus) _
            (riemannianVolumeMeasure torusModel Torus (B.collar i).cusp.torusMetric)
              volume).withDensity (fun q => ENNReal.ofReal (Real.exp (-q.2))) S)
    {p : W.Carrier} (hp : distanceToBoundary W g p ≤ ENNReal.ofReal 10) :
    ∀ a : ℝ, 0 < a → a ≤ 1 → ballVolume g p a ≤ ENNReal.ofReal (1000 * δ ^ 2 * a) := by
  intro a _ ha
  obtain ⟨i, x, z, hz0, hz, rfl⟩ := B.exists_collar_height_lt_eleven hδ hp
  refine B.ballVolume_le_of_volume_transfer hδ i (hV i) ?_ ha
  change (halfSpaceOneLift z).val 0 ≤ 96
  rw [halfSpaceOneLift_val_zero, max_eq_left hz0]
  linarith

end DifferentialGeometry.Geometry.Collapse
