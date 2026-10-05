import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42Final
import DifferentialGeometry.Geometry.Collapse.AssemblyBindingThresholdsApplications

/-!
# Consumer of FC42 packet F1: the static threshold in form (b) (lane ASM-F1)

Lead decision M1 (2026-10-04): FC42 is consumed in form (b) — the bindings produce certificates
TOGETHER with the rim-product clause (the producer obligation RIMBOX-1 of review 44 item 3(d)), and
the consumer takes the clause as a plain hypothesis. This file re-runs the composition of
`Collapse/AssemblyBindingThresholds*.lean` (lane ASM-V3) with that consumer:

* `exists_boundary_presentation_of_rimProduct_of_consumer` — the boundary wrapper (BCF04): with
  nearly cuspidal boundary the auxiliary `sec ≥ 0` disjunct is impossible;
* `exists_graph_threshold_disj_of_rimProduct_bindings` — the static threshold in V3 form from the
  closed and boundary bindings in form (b) and a form-(b) FC42 consumer;
* `exists_graph_threshold_disj_of_rimProduct_bindings_of_steps` — the same with the consumer
  instantiated by `exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct_of_steps`
  (the packets not yet in the tree as plain hypotheses).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **The boundary wrapper, form (b)**: with nearly cuspidal boundary data `B`, a certificate with
the rim-product clause gives a raw presentation labelled by `B` (the auxiliary disjunct would make
the boundary empty, but it contains the component `0` of `B`). -/
theorem exists_boundary_presentation_of_rimProduct_of_consumer
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n} (D : DecompositionCertificate W E), D.RimProduct →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0))
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) {E : BoundaryTori W B.count}
    (D : DecompositionCertificate W E) (hprod : D.RimProduct) :
    ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  rcases consumer W D hprod with hG | ⟨hclosed, -⟩
  · obtain ⟨G⟩ := hG
    exact ⟨G, G.external_matching B⟩
  · have hi : B.component ⟨0, B.count_pos⟩ ⊆ W.model.boundary W.Carrier := by
      rw [← B.covers]
      exact Set.subset_iUnion _ _
    rw [hclosed, Set.subset_empty_iff] at hi
    exact ((B.connected ⟨0, B.count_pos⟩).nonempty.ne_empty hi).elim

/-- **The static threshold in V3 form, form (b)**: from the closed and boundary bindings producing
certificates with the rim-product clause and a form-(b) FC42 consumer; one uniform `w₀` before all
`(W, g)`. -/
theorem exists_graph_threshold_disj_of_rimProduct_bindings (K : ℕ) (A : ℝ → ℝ)
    (closedBinding : ∃ D : ClosedEarlyData, ∃ T : ClosedThresholds D,
      ∀ (R : ClosedRegister D T) (n : ℕ), max 2 R.later.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier),
          (∀ p, curvatureRadius g p ≠ ⊤) →
          closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
          ∃ Dc : ClosedDecompositionCertificate W, Dc.cert.RimProduct)
    (boundaryBinding : ∃ D : BoundaryEarlyData, ∃ T : BoundaryThresholds D,
      ∀ (R : BoundaryRegister D T) (n : ℕ), max 2 R.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier)
          (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar n)),
          boundaryVolumeCollapsed W g (boundaryCounterexampleRatio D.δStar n) →
          curvatureDerivativesControlled g K A (boundaryCounterexampleRatio D.δStar n) →
          ∃ E : BoundaryTori W B.count,
            (∃ Dc : DecompositionCertificate W E, Dc.RimProduct) ∧
            ∀ i, Set.range (E.torusMap i) = B.component i)
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
  obtain ⟨Dc, Tc, hcb⟩ := closedBinding
  obtain ⟨Rc⟩ := exists_closedRegister Dc Tc
  obtain ⟨Db, Tb, hbb⟩ := boundaryBinding
  obtain ⟨Rb⟩ := exists_boundaryRegister Db Tb
  refine exists_graph_threshold_disj_of_closed_disj
    (exists_closed_graph_threshold_disj_of_finite_scales_disj
      ⟨closedCounterexampleRatio (max 2 Rc.later.tail), closedCounterexampleRatio_pos (by omega),
        closedCounterexampleRatio_lt_volume _,
        finite_scales_disj_of_raw_or_aux_nonneg fun W _ g hfin hcol => ?_⟩)
    ⟨boundaryCounterexampleRatio Db.δStar (max 2 Rb.tail),
      boundaryCounterexampleRatio_pos Db.δStar_pos (by omega),
      boundaryCounterexampleRatio_lt_volume _ _, fun W _ g B hvol hder => ?_⟩
  · obtain ⟨C, hC⟩ := hcb Rc _ le_rfl W g hfin hcol
    exact consumer W C.cert hC
  · obtain ⟨E, ⟨C, hC⟩, -⟩ := hbb Rb _ le_rfl W g B hvol hder
    exact exists_boundary_presentation_of_rimProduct_of_consumer consumer W B C hC

/-- **The static threshold in V3 form from FC42, form (b)**, the packets not yet in the tree as plain
hypotheses (their frozen texts; see `AssemblyFC42Final.lean`). -/
theorem exists_graph_threshold_disj_of_rimProduct_bindings_of_steps (K : ℕ) (A : ℝ → ℝ)
    (hL1 : ∀ {W : CompactCarrier.{u}} (C : BallHandleCycle W), C.RimProduct →
      (∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) →
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
        C.union.Piece))
    (hS5 : ∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → ∀ c : Fin D.sphereSeamCount,
      ∃ (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
        Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
        Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
          (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
        ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
            (X.componentTori DQ i),
          D'.sphereSeamCount < D.sphereSeamCount ∧
          D'.badVertexCount ≤ (D.badVertexSet.filter fun k => ∀ b, k ≠ D.sphereSide c b).card ∧
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧
          (D.RimProduct → D'.RimProduct))
    (hN2 : ∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → D.sphereSeamCount = 0 →
      ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
      ∀ {P : PieceEmbedding W}
        {c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
        {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier}
        {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
        {hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}},
      D.vertex k = .zero P (.puncturedRP3 c f hf hr) →
      ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
        Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
        Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
          (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
        ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
            (X.componentTori DQ i),
          D'.sphereSeamCount = 0 ∧ D'.badVertexCount < D.badVertexCount ∧
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct))
    (hN3 : ∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → D.sphereSeamCount = 0 →
      ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
      ∀ {P : PieceEmbedding W}
        {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece},
      D.vertex k = .slim P (.sphereInterval e) →
      ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
        Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
        Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
          (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
        ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
            (X.componentTori DQ i),
          D'.sphereSeamCount = 0 ∧ D'.badVertexCount < D.badVertexCount ∧
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct))
    (hA4 : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
      (X : SphereCutCapped W S E) (DQ : X.Q.Components), DQ.count = 2 →
      (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W))
    (hA3 : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
      (X : SphereCutCapped W S E) (DQ : X.Q.Components), DQ.count = 1 →
      (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W))
    (closedBinding : ∃ D : ClosedEarlyData, ∃ T : ClosedThresholds D,
      ∀ (R : ClosedRegister D T) (n : ℕ), max 2 R.later.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier),
          (∀ p, curvatureRadius g p ≠ ⊤) →
          closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
          ∃ Dc : ClosedDecompositionCertificate W, Dc.cert.RimProduct)
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
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_graph_threshold_disj_of_rimProduct_bindings K A closedBinding boundaryBinding
    fun W _ _ _ D hprod => exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct_of_steps
      hL1 hS5 hN2 hN3 hA4 hA3 W D hprod

end GC.GraphManifold.Assembly
