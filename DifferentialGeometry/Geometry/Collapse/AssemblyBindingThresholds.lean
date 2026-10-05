import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples
import DifferentialGeometry.Geometry.Collapse.StaticRegister
import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctive
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate

/-!
# ASM-BIND, combinatorial part: thresholds from one register, against interfaces V2/V3

Design `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md` §4 row 5, §6 lane
ASM-BIND, Decision 11; frozen texts V2 (`build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean`
§5, change log rows 31–33) and V3 (`design-fc39-fc42-assembly-v3-changes-20261004.md`). The design
states each threshold here as an IMPLICATION: "from the binding at one register and the FC42
consumer". Accordingly:

* the FC42 shared consumer (`exists_rawGraphPresentation_or_aux_nonneg_of_certificate`, V2 §4, lane
  ASM-FC42, not yet proved) enters as the explicit `∀`-hypothesis `consumer`, with its frozen
  conclusion verbatim;
* the binding enters as in the frozen statements: `hbind` at one register for the `…_at_register`
  forms (exactly the V2 hypothesis), and the conclusion of the frozen binding theorem
  (`exists_closed_certificate_binding_weak`, `…_binding`, `exists_boundary_certificate_binding`;
  analytic producers, not yet proved) for the PBR03-DI / A2 forms;
* no other hypothesis is added; the quantifier order of every threshold (one uniform `w₀` before
  all `(W, g[, B])`) is the frozen one.

Contents.
* Wrappers of the consumer: `raw_or_aux_nonneg_of_closedCertificate_of_consumer` (closed) and
  `exists_boundary_presentation_of_certificate_of_consumer` (boundary; the auxiliary `sec ≥ 0`
  disjunct is excluded by `B.count_pos` and `B.covers`, so the nonnegative case never arises with
  nearly cuspidal boundary — decision 2026-10-04 item 1, checked here).
* One register: `closed_graph_threshold_at_register_of_consumer` (V2 conclusion),
  `closed_graph_threshold_at_register_disj` (V3 conclusion, by chapter 7's unconditional
  classification), `boundary_graph_threshold_at_register_of_consumer` (A2 conclusion).
* PBR03-DI and A2 from the binding theorems' conclusions:
  `exists_closed_graph_threshold_of_finite_scales_or_aux_nonneg_of_binding_weak` (V2),
  `exists_closed_graph_threshold_of_finite_scales_disj_of_binding_weak` and
  `…_disj_of_binding` (V3: the statement of the patched admitted
  `exists_closed_graph_threshold_of_finite_scales_disj`), `exists_boundary_graph_threshold_of_boundary_binding`
  (the statement of the admitted `exists_boundary_graph_threshold`).
* Sequence form (index `m` ↔ scale `m + 2`): `closed_graph_threshold_of_sequence_binding_of_consumer`
  (V2) and `closed_graph_threshold_of_sequence_binding_disj` (V3).
No connected sum is formed here: the closed reassembly (X95 `rawGraphPresentation_connectedSum`) is
inside FC42.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold GC.GraphManifold.Assembly
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse.Assembly

universe u

/-! ## Wrappers of the FC42 consumer -/

/-- The closed wrapper of the FC42 consumer: a closed certificate gives a raw presentation or an
auxiliary smooth `sec ≥ 0` metric on the closed carrier. -/
theorem raw_or_aux_nonneg_of_closedCertificate_of_consumer
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0))
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] (D : ClosedDecompositionCertificate W) :
    Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
        Riemannian.SectionalBoundedBelow g' 0) :=
  consumer W D.cert

/-- The boundary wrapper of the FC42 consumer (BCF04): with nearly cuspidal boundary data `B`, the
auxiliary `sec ≥ 0` disjunct is impossible (the boundary contains the nonempty component `0` of
`B`), and the raw presentation gets the labels of `B` by `RawGraphPresentation.external_matching`. -/
theorem exists_boundary_presentation_of_certificate_of_consumer
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0))
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) {E : BoundaryTori W B.count}
    (D : DecompositionCertificate W E) :
    ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  rcases consumer W D with hG | ⟨hclosed, -⟩
  · obtain ⟨G⟩ := hG
    exact ⟨G, G.external_matching B⟩
  · have hi : B.component ⟨0, B.count_pos⟩ ⊆ W.model.boundary W.Carrier := by
      rw [← B.covers]
      exact Set.subset_iUnion _ _
    rw [hclosed, Set.subset_empty_iff] at hi
    exact ((B.connected ⟨0, B.count_pos⟩).nonempty.ne_empty hi).elim

/-! ## Thresholds at one register (`N = max 2 tail`) -/

/-- **Closed threshold at one register, V2** (frozen `closed_graph_threshold_at_register` with the
FC42 consumer as explicit input): `w₀ = closedCounterexampleRatio (max 2 R.later.tail)`. -/
theorem closed_graph_threshold_at_register_of_consumer (K : ℕ) (A : ℝ → ℝ)
    {D : ClosedEarlyData} {T : ClosedThresholds D} (R : ClosedRegister D T)
    (hbind : ∀ n : ℕ, max 2 R.later.tail ≤ n →
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) →
        closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
        Nonempty (ClosedDecompositionCertificate W))
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    0 < closedCounterexampleRatio (max 2 R.later.tail) ∧
      closedCounterexampleRatio (max 2 R.later.tail) < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) →
        closedCollapseHypotheses W g K A (closedCounterexampleRatio (max 2 R.later.tail)) →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0) := by
  refine ⟨closedCounterexampleRatio_pos (by omega), closedCounterexampleRatio_lt_volume _, ?_⟩
  intro W _ g hfin hcol
  obtain ⟨Dc⟩ := hbind _ le_rfl W g hfin hcol
  exact raw_or_aux_nonneg_of_closedCertificate_of_consumer consumer W Dc

/-- **Closed threshold at one register, V3**: the same register threshold with the V3 conclusion
(raw presentation or a spherical, `S² × ℝ` or Euclidean geometric structure), by chapter 7's
unconditional classification applied to the auxiliary metric. -/
theorem closed_graph_threshold_at_register_disj (K : ℕ) (A : ℝ → ℝ)
    {D : ClosedEarlyData} {T : ClosedThresholds D} (R : ClosedRegister D T)
    (hbind : ∀ n : ℕ, max 2 R.later.tail ≤ n →
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) →
        closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
        Nonempty (ClosedDecompositionCertificate W))
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    0 < closedCounterexampleRatio (max 2 R.later.tail) ∧
      closedCounterexampleRatio (max 2 R.later.tail) < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) →
        closedCollapseHypotheses W g K A (closedCounterexampleRatio (max 2 R.later.tail)) →
        Nonempty (RawGraphPresentation W) ∨
          ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
            G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨hpos, hlt, hDI⟩ := closed_graph_threshold_at_register_of_consumer K A R hbind consumer
  exact ⟨hpos, hlt, finite_scales_disj_of_raw_or_aux_nonneg hDI⟩

/-- **Boundary threshold at one register** (frozen `boundary_graph_threshold_at_register` with the
FC42 consumer as explicit input): `w₀ = boundaryCounterexampleRatio D.δStar (max 2 R.tail)`; the
conclusion is A2's (labelled raw presentation). -/
theorem boundary_graph_threshold_at_register_of_consumer (K : ℕ) (A : ℝ → ℝ)
    {D : BoundaryEarlyData} {T : BoundaryThresholds D} (R : BoundaryRegister D T)
    (hbind : ∀ n : ℕ, max 2 R.tail ≤ n →
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar n)),
        boundaryVolumeCollapsed W g (boundaryCounterexampleRatio D.δStar n) →
        curvatureDerivativesControlled g K A (boundaryCounterexampleRatio D.δStar n) →
        ∃ E : BoundaryTori W B.count,
          Nonempty (DecompositionCertificate W E) ∧
          ∀ i, Set.range (E.torusMap i) = B.component i)
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    0 < boundaryCounterexampleRatio D.δStar (max 2 R.tail) ∧
      boundaryCounterexampleRatio D.δStar (max 2 R.tail) < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar (max 2 R.tail))),
        boundaryVolumeCollapsed W g (boundaryCounterexampleRatio D.δStar (max 2 R.tail)) →
        curvatureDerivativesControlled g K A (boundaryCounterexampleRatio D.δStar (max 2 R.tail)) →
        ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  refine ⟨boundaryCounterexampleRatio_pos D.δStar_pos (by omega),
    boundaryCounterexampleRatio_lt_volume _ _, ?_⟩
  intro W _ g B hvol hder
  obtain ⟨E, ⟨Dc⟩, -⟩ := hbind _ le_rfl W g B hvol hder
  exact exists_boundary_presentation_of_certificate_of_consumer consumer W B Dc

/-! ## PBR03-DI and A2 from the binding theorems -/

/-- **PBR03-DI, V2** (frozen `exists_closed_graph_threshold_of_finite_scales_or_aux_nonneg`), from the
conclusion of the weak closed binding `exists_closed_certificate_binding_weak` at `(K, A)` and the
FC42 consumer. -/
theorem exists_closed_graph_threshold_of_finite_scales_or_aux_nonneg_of_binding_weak
    (K : ℕ) (A : ℝ → ℝ)
    (binding : ∃ D : ClosedEarlyData, ∃ T : ClosedThresholds D, ∃ R : ClosedRegister D T,
      ∀ n : ℕ, max 2 R.later.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier),
          (∀ p, curvatureRadius g p ≠ ⊤) →
          closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
          Nonempty (ClosedDecompositionCertificate W))
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0) := by
  obtain ⟨_, _, R, hbind⟩ := binding
  exact ⟨_, closed_graph_threshold_at_register_of_consumer K A R hbind consumer⟩

/-- **PBR03, V3** — the statement of the (patched) admitted
`exists_closed_graph_threshold_of_finite_scales_disj` at `(K, A)` — from the conclusion of the weak
closed binding and the FC42 consumer. -/
theorem exists_closed_graph_threshold_of_finite_scales_disj_of_binding_weak
    (K : ℕ) (A : ℝ → ℝ)
    (binding : ∃ D : ClosedEarlyData, ∃ T : ClosedThresholds D, ∃ R : ClosedRegister D T,
      ∀ n : ℕ, max 2 R.later.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier),
          (∀ p, curvatureRadius g p ≠ ⊤) →
          closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
          Nonempty (ClosedDecompositionCertificate W))
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) →
        closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨_, _, R, hbind⟩ := binding
  exact ⟨_, closed_graph_threshold_at_register_disj K A R hbind consumer⟩

/-- **PBR03, V3**, from the conclusion of the `∀ R` closed binding `exists_closed_certificate_binding`
at `(K, A)` (one register by `exists_closedRegister`, PBR01) and the FC42 consumer. -/
theorem exists_closed_graph_threshold_of_finite_scales_disj_of_binding (K : ℕ) (A : ℝ → ℝ)
    (binding : ∃ D : ClosedEarlyData, ∃ T : ClosedThresholds D,
      ∀ (R : ClosedRegister D T) (n : ℕ), max 2 R.later.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier),
          (∀ p, curvatureRadius g p ≠ ⊤) →
          closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
          Nonempty (ClosedDecompositionCertificate W))
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) →
        closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨D, T, hbind⟩ := binding
  obtain ⟨R⟩ := exists_closedRegister D T
  exact ⟨_, closed_graph_threshold_at_register_disj K A R (hbind R) consumer⟩

/-- **A2 = BBR03** — the statement of the admitted `exists_boundary_graph_threshold` at `(K, A)` —
from the conclusion of the boundary binding `exists_boundary_certificate_binding` (one register by
`exists_boundaryRegister`, BBR01) and the FC42 consumer. -/
theorem exists_boundary_graph_threshold_of_boundary_binding (K : ℕ) (A : ℝ → ℝ)
    (binding : ∃ D : BoundaryEarlyData, ∃ T : BoundaryThresholds D,
      ∀ (R : BoundaryRegister D T) (n : ℕ), max 2 R.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier)
          (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar n)),
          boundaryVolumeCollapsed W g (boundaryCounterexampleRatio D.δStar n) →
          curvatureDerivativesControlled g K A (boundaryCounterexampleRatio D.δStar n) →
          ∃ E : BoundaryTori W B.count,
            Nonempty (DecompositionCertificate W E) ∧
            ∀ i, Set.range (E.torusMap i) = B.component i)
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W,
          ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  obtain ⟨D, T, hbind⟩ := binding
  obtain ⟨R⟩ := exists_boundaryRegister D T
  exact ⟨_, boundary_graph_threshold_at_register_of_consumer K A R (hbind R) consumer⟩

/-! ## The standing-sequence form (member `m` at scale `m + 2`) -/

/-- **Sequence form, V2** (frozen `closed_graph_threshold_of_sequence_binding` with the FC42 consumer
as explicit input): a producer that gives closed certificates on the tail `N ≤ m + 2` of every
standing sequence at the ratios `closedCounterexampleRatio (m + 2)` gives the PBR03-DI threshold,
by contradiction with `exists_closed_standing_sequence_of_no_threshold`. -/
theorem closed_graph_threshold_of_sequence_binding_of_consumer (K : ℕ) (A : ℝ → ℝ)
    (hseq : ∀ (W : ℕ → CompactCarrier.{u}) [∀ m, ConnectedSpace (W m).Carrier]
      (g : ∀ m, SmoothRiemannianMetric (W m).model (W m).Carrier),
      (∀ m, (∀ p, curvatureRadius (g m) p ≠ ⊤) ∧
        closedCollapseHypotheses (W m) (g m) K A (closedCounterexampleRatio (m + 2))) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m + 2 → Nonempty (ClosedDecompositionCertificate (W m)))
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0) := by
  by_contra hno
  obtain ⟨W, hW, g, hdata⟩ := exists_closed_standing_sequence_of_no_threshold K A
    (fun W => Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
        Riemannian.SectionalBoundedBelow g' 0)) hno
  obtain ⟨N, hN⟩ := @hseq W hW g fun m => ⟨(hdata m).1, (hdata m).2.1⟩
  obtain ⟨Dc⟩ := hN N (by omega)
  have := hW N
  exact (hdata N).2.2.1 (raw_or_aux_nonneg_of_closedCertificate_of_consumer consumer (W N) Dc)

/-- **Sequence form, V3**: the same producer hypothesis gives the V3 finite-scale threshold (the
statement of the patched admitted `exists_closed_graph_threshold_of_finite_scales_disj` at
`(K, A)`). -/
theorem closed_graph_threshold_of_sequence_binding_disj (K : ℕ) (A : ℝ → ℝ)
    (hseq : ∀ (W : ℕ → CompactCarrier.{u}) [∀ m, ConnectedSpace (W m).Carrier]
      (g : ∀ m, SmoothRiemannianMetric (W m).model (W m).Carrier),
      (∀ m, (∀ p, curvatureRadius (g m) p ≠ ⊤) ∧
        closedCollapseHypotheses (W m) (g m) K A (closedCounterexampleRatio (m + 2))) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m + 2 → Nonempty (ClosedDecompositionCertificate (W m)))
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) →
        closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨w₀, hw₀, hwc, hDI⟩ := closed_graph_threshold_of_sequence_binding_of_consumer K A hseq consumer
  exact ⟨w₀, hw₀, hwc, finite_scales_disj_of_raw_or_aux_nonneg hDI⟩

end DifferentialGeometry.Geometry.Collapse.Assembly
