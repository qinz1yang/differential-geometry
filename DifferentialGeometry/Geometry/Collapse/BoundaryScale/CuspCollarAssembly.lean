import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarPinching
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarVolumeApplications

/-!
# Statement G, assembly: the consumer clauses of BSA01 from pinching and volume transfer

Blueprint 207B, BSA01 (`B:7591–7672`); frozen interface `G_consumer_clauses`
(`build-logs/scratch/BDY-FILL/BoundaryInterfaces.lean:167–175`), read by
`StandingSequence.lean` (`hnear`) and BSA06.

* `NearlyCuspidalBoundary.consumer_clauses_of_pinching_of_volume_transfer` (kernel, one boundary):
  with the pinching `-1/2 ≤ sec ≤ -1/8` on `z ≤ 98` of every collar (lane FT-C) and the upper half
  of the volume transfer V.1 on every collar (lane BDY-V), and `δ ≤ 1/100`, exactly the two
  clauses of `G_consumer_clauses` hold for this boundary.
* `G_consumer_clauses_of_pinching_of_volume_transfer`: the interface statement verbatim
  (`δStar = min (1/100) δ₁`), with the two supplier statements, in their frozen shapes, as
  hypotheses. When FT-C's pinching theorem and BDY-V's `CuspEmbedding.volume_transfer` land, the
  binding is the application of this theorem to them (V.1's second conjunct).
-/

set_option autoImplicit false

noncomputable section

open Set Function MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open GC.Endpoint DifferentialGeometry.Topology.Manifold DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **G, consumer clauses for one boundary (kernel).** Pinching on every collar, the upper half of
V.1 on every collar and `δ ≤ 1/100` give BSA01's near-boundary clause (`1 ≤ R_p`,
`vol B(p, a) ≤ 1000 δ² a` for `d(p, ∂W) ≤ 10`, `0 < a ≤ 1`) and BSA01.c on a connected carrier. -/
theorem NearlyCuspidalBoundary.consumer_clauses_of_pinching_of_volume_transfer
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100)
    (hpinch : ∀ (i : Fin B.count), ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 →
      ∀ u w : TangentSpace W.model ((B.collar i).toFun q),
        -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
            metricRm04StandardAt g ((B.collar i).toFun q) u w w u ∧
          metricRm04StandardAt g ((B.collar i).toFun q) u w w u ≤
            -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2))
    (hV : ∀ (i : Fin B.count) (S : Set (Torus × ℝ)), MeasurableSet[borel (Torus × ℝ)] S →
      (∀ q ∈ S, 0 ≤ q.2 ∧ q.2 < cuspDepth) →
      riemannianVolumeMeasure W.model W.Carrier g
          ((B.collar i).toFun '' ((fun q : Torus × ℝ => (q.1, halfSpaceOneLift q.2)) '' S)) ≤
        ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2)) *
          (@Measure.prod Torus ℝ (borel Torus) _
            (riemannianVolumeMeasure torusModel Torus (B.collar i).cusp.torusMetric)
              volume).withDensity (fun q => ENNReal.ofReal (Real.exp (-q.2))) S) :
    (∀ p, distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
        1 ≤ curvatureRadius g p ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
          ballVolume g p a ≤ ENNReal.ofReal (1000 * δ ^ 2 * a)) ∧
      (ConnectedSpace W.Carrier → ∀ p, distanceToBoundary W g p < ⊤ ∧
        curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3) :=
  ⟨fun _ hp => ⟨B.one_le_curvatureRadius_of_distanceToBoundary_le_ten hδ
      (fun i q hq hz u w => (hpinch i q hq hz u w).1) hp,
    B.ballVolume_le_of_distanceToBoundary_le_ten hδ hV hp⟩,
   fun _ p => ⟨B.distanceToBoundary_lt_top p,
    B.curvatureRadius_le_distanceToBoundary_add_three_of_pinching hδ
      (fun i q hq hz u w => (hpinch i q hq hz u w).2) p⟩⟩

/-- **G (consumer clauses), from the supplier statements.** The frozen interface
`G_consumer_clauses`, verbatim, from (1) the cusp pinching of lane FT-C (BSA01 (i), sectional
part, `K ≥ 2`, `δ ≤ δ₁`) and (2) the upper half of the volume transfer V.1 of lane BDY-V. -/
theorem G_consumer_clauses_of_pinching_of_volume_transfer
    (hpinch : ∃ δ₁ > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ) (X : Set W.Carrier) (e : CuspEmbedding W g K δ X), 2 ≤ K → 0 ≤ δ →
      δ ≤ δ₁ → ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 → ∀ u w : TangentSpace W.model (e.toFun q),
        -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
            metricRm04StandardAt g (e.toFun q) u w w u ∧
          metricRm04StandardAt g (e.toFun q) u w w u ≤
            -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2))
    (hV : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ)
      (δ : ℝ) (X : Set W.Carrier) (e : CuspEmbedding W g K δ X), 0 ≤ δ → δ < 1 →
      ∀ S : Set (Torus × ℝ), MeasurableSet[borel (Torus × ℝ)] S →
      (∀ q ∈ S, 0 ≤ q.2 ∧ q.2 < cuspDepth) →
      riemannianVolumeMeasure W.model W.Carrier g
          (e.toFun '' ((fun q : Torus × ℝ => (q.1, halfSpaceOneLift q.2)) '' S)) ≤
        ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2)) *
          (@Measure.prod Torus ℝ (borel Torus) _
            (riemannianVolumeMeasure torusModel Torus e.cusp.torusMetric) volume).withDensity
              (fun q => ENNReal.ofReal (Real.exp (-q.2))) S) :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ), 2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      (∀ p, distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
        1 ≤ curvatureRadius g p ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
          ballVolume g p a ≤ ENNReal.ofReal (1000 * δ ^ 2 * a)) ∧
      (ConnectedSpace W.Carrier → ∀ p, distanceToBoundary W g p < ⊤ ∧
        curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3) := by
  obtain ⟨δ₁, hδ₁, hpin⟩ := hpinch
  refine ⟨min (1 / 100) δ₁, lt_min (by norm_num) hδ₁, fun W g K δ hK hδ0 hδ B => ?_⟩
  have hδa : δ ≤ 1 / 100 := hδ.trans (min_le_left _ _)
  exact B.consumer_clauses_of_pinching_of_volume_transfer hδa
    (fun i => hpin W g K δ _ (B.collar i) hK hδ0 (hδ.trans (min_le_right _ _)))
    (fun i => hV W g K δ _ (B.collar i) hδ0 (by linarith))

end DifferentialGeometry.Geometry.Collapse
