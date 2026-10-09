import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42FinalTheorem

/-!
# The static threshold from PER-SEQUENCE bindings (lane FC39-BQ; review 52 R-c, route 2)

User decision 2026-10-05 (dispositions task 52, R-c): the boundary supply takes the blueprint's own
per-sequence form. BBR01 (B:10356–10367) fixes ONE assignment independent of the member, point and
boundary component; BR20–BR23 (B:10452–10455) let the joint producer output `V` and the tail on the
sequence; BBR02 (B:10567–10574) gives certificates on every sufficiently late member of BSA04's
counterexample sequence; BBR03 (B:10620–10644) turns this into the static threshold by
contradiction. The closed side has the same shape (PBR02–PBR03,
`closed_graph_threshold_of_sequence_binding_of_consumer`).

The consumers of the uniform boundary binding
(`exists_boundary_graph_threshold_of_boundary_binding`,
`exists_graph_threshold_disj_of_rimProduct_bindings`, FC42's
`exists_graph_threshold_disj_of_rimProduct_bindings_fc42`) only extract ONE threshold `∃ w₀`; here
the threshold comes from the sequence binding instead:

* `boundary_graph_threshold_of_sequence_binding_of_consumer_BQ` — BBR03 (A2 conclusion) from a
  boundary binding on the tail of every boundary standing sequence at the ratios `δ_{n+1}`
  (`exists_boundary_counterexample_sequence_of_no_threshold`, B:10624–10625) and the FC42 consumer;
* `boundary_graph_threshold_of_sequence_binding_rimProduct_BQ`,
  `closed_graph_threshold_of_sequence_binding_rimProduct_BQ` — the same in form (b) (certificates
  with the rim-product clause, lead decision M1);
* `exists_graph_threshold_disj_of_rimProduct_sequence_bindings_BQ` and the unconditional-consumer
  form `exists_graph_threshold_disj_of_rimProduct_sequence_bindings_fc42_BQ` — the common static
  threshold (V3 form) from the two sequence bindings;
* consumers `boundary_sequence_binding_of_boundary_binding_BQ`,
  `closed_sequence_binding_of_closed_binding_BQ` — the old uniform bindings imply the sequence
  bindings, so the new final theorem is no stronger in its hypotheses than the old one.

The boundary sequence binding fixes `δ*` BEFORE the sequence (BBR03, B:10621: thresholds are
restricted below BSA01's `δ*` first). No carrier is constructed here.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Collapse.Assembly
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **BBR03 from a per-sequence boundary binding** (B:10620–10644; A2 conclusion): if every
boundary standing sequence at the ratios `δ_{n+1}` carries labelled certificates on a tail, then
the nonempty-boundary static threshold exists. -/
theorem boundary_graph_threshold_of_sequence_binding_of_consumer_BQ (K : ℕ) (A : ℝ → ℝ)
    {δStar : ℝ} (hδ : 0 < δStar)
    (hseq : ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
      (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
      (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))),
      (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
        curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1))) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ E : BoundaryTori (W n) (B n).count,
        Nonempty (DecompositionCertificate (W n) E) ∧
        ∀ i, Set.range (E.torusMap i) = (B n).component i)
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W,
          ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  by_contra hno
  obtain ⟨W, hW, g, B, hdata⟩ := exists_boundary_counterexample_sequence_of_no_threshold K A hδ
    (fun W _ _ B => ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (e i)) = B.component i) hno
  obtain ⟨N, hN⟩ := @hseq W hW g B fun n => ⟨(hdata n).1, (hdata n).2.1⟩
  obtain ⟨E, ⟨Dc⟩, -⟩ := hN N le_rfl
  have := hW N
  exact (hdata N).2.2
    (exists_boundary_presentation_of_certificate_of_consumer consumer (W N) (B N) Dc)

/-- **BBR03 from a per-sequence boundary binding, form (b)**: the certificates carry the
rim-product clause and the consumer is FC42's form (b). -/
theorem boundary_graph_threshold_of_sequence_binding_rimProduct_BQ (K : ℕ) (A : ℝ → ℝ)
    {δStar : ℝ} (hδ : 0 < δStar)
    (hseq : ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
      (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
      (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))),
      (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
        curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1))) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ E : BoundaryTori (W n) (B n).count,
        (∃ Dc : DecompositionCertificate (W n) E, Dc.RimProduct) ∧
        ∀ i, Set.range (E.torusMap i) = (B n).component i)
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n} (D : DecompositionCertificate W E), D.RimProduct →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W,
          ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  by_contra hno
  obtain ⟨W, hW, g, B, hdata⟩ := exists_boundary_counterexample_sequence_of_no_threshold K A hδ
    (fun W _ _ B => ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (e i)) = B.component i) hno
  obtain ⟨N, hN⟩ := @hseq W hW g B fun n => ⟨(hdata n).1, (hdata n).2.1⟩
  obtain ⟨E, ⟨Dc, hDc⟩, -⟩ := hN N le_rfl
  have := hW N
  exact (hdata N).2.2
    (exists_boundary_presentation_of_rimProduct_of_consumer consumer (W N) (B N) Dc hDc)

/-- **PBR03 from a per-sequence closed binding, form (b)** (the closed twin; member `m` at the
ratio `closedCounterexampleRatio (m + 2)`, as in the frozen closed wrapper (2)). -/
theorem closed_graph_threshold_of_sequence_binding_rimProduct_BQ (K : ℕ) (A : ℝ → ℝ)
    (hseq : ∀ (W : ℕ → CompactCarrier.{u}) [∀ m, ConnectedSpace (W m).Carrier]
      (g : ∀ m, SmoothRiemannianMetric (W m).model (W m).Carrier),
      (∀ m, (∀ p, curvatureRadius (g m) p ≠ ⊤) ∧
        closedCollapseHypotheses (W m) (g m) K A (closedCounterexampleRatio (m + 2))) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ Dc : ClosedDecompositionCertificate (W m), Dc.cert.RimProduct)
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n} (D : DecompositionCertificate W E), D.RimProduct →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0) := by
  by_contra hno
  obtain ⟨W, hW, g, hdata⟩ := exists_closed_standing_sequence_of_no_threshold K A
    (fun W => Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
        DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0)) hno
  obtain ⟨N, hN⟩ := @hseq W hW g fun m => ⟨(hdata m).1, (hdata m).2.1⟩
  obtain ⟨Dc, hDc⟩ := hN N le_rfl
  have := hW N
  exact (hdata N).2.2.1 (consumer (W N) Dc.cert hDc)

/-- **The common static threshold (V3 form) from the two PER-SEQUENCE bindings**, form (b), with
the FC42 consumer as input. Same conclusion as
`exists_graph_threshold_disj_of_rimProduct_bindings`. -/
theorem exists_graph_threshold_disj_of_rimProduct_sequence_bindings_BQ (K : ℕ) (A : ℝ → ℝ)
    (closedSeq : ∀ (W : ℕ → CompactCarrier.{u}) [∀ m, ConnectedSpace (W m).Carrier]
      (g : ∀ m, SmoothRiemannianMetric (W m).model (W m).Carrier),
      (∀ m, (∀ p, curvatureRadius (g m) p ≠ ⊤) ∧
        closedCollapseHypotheses (W m) (g m) K A (closedCounterexampleRatio (m + 2))) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ Dc : ClosedDecompositionCertificate (W m), Dc.cert.RimProduct)
    (boundarySeq : ∃ δStar : ℝ, 0 < δStar ∧
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
          curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1))) →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ E : BoundaryTori (W n) (B n).count,
          (∃ Dc : DecompositionCertificate (W n) E, Dc.RimProduct) ∧
          ∀ i, Set.range (E.torusMap i) = (B n).component i)
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n} (D : DecompositionCertificate W E), D.RimProduct →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) := by
  obtain ⟨δStar, hδ, hbs⟩ := boundarySeq
  obtain ⟨wc, hwc, hwcl, hDI⟩ := closed_graph_threshold_of_sequence_binding_rimProduct_BQ K A
    closedSeq consumer
  exact exists_graph_threshold_disj_of_closed_disj
    (exists_closed_graph_threshold_disj_of_finite_scales_disj
      ⟨wc, hwc, hwcl, finite_scales_disj_of_raw_or_aux_nonneg hDI⟩)
    (boundary_graph_threshold_of_sequence_binding_rimProduct_BQ K A hδ hbs consumer)

/-- **FC42's final theorem from the two PER-SEQUENCE bindings** (route 2): the twin of
`exists_graph_threshold_disj_of_rimProduct_bindings_fc42` with the closed and boundary bindings in
the blueprint's per-sequence form (PBR02 / BBR02) and FC42 form (b) discharged unconditionally. -/
theorem exists_graph_threshold_disj_of_rimProduct_sequence_bindings_fc42_BQ (K : ℕ) (A : ℝ → ℝ)
    (closedSeq : ∀ (W : ℕ → CompactCarrier.{u}) [∀ m, ConnectedSpace (W m).Carrier]
      (g : ∀ m, SmoothRiemannianMetric (W m).model (W m).Carrier),
      (∀ m, (∀ p, curvatureRadius (g m) p ≠ ⊤) ∧
        closedCollapseHypotheses (W m) (g m) K A (closedCounterexampleRatio (m + 2))) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ Dc : ClosedDecompositionCertificate (W m), Dc.cert.RimProduct)
    (boundarySeq : ∃ δStar : ℝ, 0 < δStar ∧
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
          curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1))) →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ E : BoundaryTori (W n) (B n).count,
          (∃ Dc : DecompositionCertificate (W n) E, Dc.RimProduct) ∧
          ∀ i, Set.range (E.torusMap i) = (B n).component i) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_graph_threshold_disj_of_rimProduct_sequence_bindings_BQ K A closedSeq boundarySeq
    fun W _ _ _ D hp =>
      exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct W D hp

/-- **Consumer (the old uniform boundary binding implies the sequence binding)**: one register at
the uniform strategy and the tail `max 2 R.tail` work for every boundary standing sequence (member
`n` at `δ_{n+1}`), so the sequence form asks no more than the old binding. -/
theorem boundary_sequence_binding_of_boundary_binding_BQ (K : ℕ) (A : ℝ → ℝ)
    (boundaryBinding : ∃ D : BoundaryEarlyData, ∃ T : BoundaryThresholds D,
      ∀ (R : BoundaryRegister D T) (n : ℕ), max 2 R.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier)
          (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar n)),
          boundaryVolumeCollapsed W g (boundaryCounterexampleRatio D.δStar n) →
          curvatureDerivativesControlled g K A (boundaryCounterexampleRatio D.δStar n) →
          ∃ E : BoundaryTori W B.count,
            (∃ Dc : DecompositionCertificate W E, Dc.RimProduct) ∧
            ∀ i, Set.range (E.torusMap i) = B.component i) :
    ∃ δStar : ℝ, 0 < δStar ∧
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
          curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1))) →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ E : BoundaryTori (W n) (B n).count,
          (∃ Dc : DecompositionCertificate (W n) E, Dc.RimProduct) ∧
          ∀ i, Set.range (E.torusMap i) = (B n).component i := by
  obtain ⟨D, T, hbb⟩ := boundaryBinding
  obtain ⟨R⟩ := exists_boundaryRegister D T
  refine ⟨D.δStar, D.δStar_pos, fun W _ g B hdata => ⟨max 2 R.tail, fun n hn => ?_⟩⟩
  exact hbb R (n + 1) (by omega) (W n) (g n) (B n) (hdata n).1 (hdata n).2

/-- **Consumer (the old uniform closed binding implies the closed sequence binding)**. -/
theorem closed_sequence_binding_of_closed_binding_BQ (K : ℕ) (A : ℝ → ℝ)
    (closedBinding : ∃ D : ClosedEarlyData, ∃ T : ClosedThresholds D,
      ∀ (R : ClosedRegister D T) (n : ℕ), max 2 R.later.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier),
          (∀ p, curvatureRadius g p ≠ ⊤) →
          closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
          ∃ Dc : ClosedDecompositionCertificate W, Dc.cert.RimProduct) :
    ∀ (W : ℕ → CompactCarrier.{u}) [∀ m, ConnectedSpace (W m).Carrier]
      (g : ∀ m, SmoothRiemannianMetric (W m).model (W m).Carrier),
      (∀ m, (∀ p, curvatureRadius (g m) p ≠ ⊤) ∧
        closedCollapseHypotheses (W m) (g m) K A (closedCounterexampleRatio (m + 2))) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        ∃ Dc : ClosedDecompositionCertificate (W m), Dc.cert.RimProduct := by
  obtain ⟨D, T, hcb⟩ := closedBinding
  obtain ⟨R⟩ := exists_closedRegister D T
  intro W _ g hdata
  exact ⟨max 2 R.later.tail, fun m hm =>
    hcb R (m + 2) (by omega) (W m) (g m) (hdata m).1 (hdata m).2⟩

end GC.GraphManifold.Assembly
