import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4CertificateFCW

/-!
# CAA02 (completion of the written static assembly goal) from the two certificate producers

Lane S-FC-WRAP, group G5 (suffix `_FCW`). Blueprint `master207B.tex`, CAA02 (B:10773–10810): "the
active Chapter14 construction now proves the closed static conclusion PBR03 and the nearly cuspidal
boundary conclusion BBR03. In both scopes it produces the actual finite smooth KL graph
presentation on the original carrier, with its collared attaching maps and, when present, original
external boundary labels." Its proof is "use CAA01's refined assignments; PBR03's reduction;
BBR03" — no new mathematics. CAA01 (`exists_closed_and_boundary_registersV4`, the two refined
registers for the same early data) is DONE; both static data theorems already sit on those
registers.

`caa02_row_FCW` is the conjunction PBR03 ∧ BBR03 ∧ (their common static threshold, V3 form):

1. PBR03, the closed threshold (`pbr03_threshold_FCW`, from the closed rows producer `hrows`:
   chain outputs at every base point give `FC39RowsV2 W (BoundaryTori.empty W)`);
2. BBR03, the boundary threshold with labelled raw graph presentations
   (`boundary_graph_threshold_of_sequence_binding_rimProduct_BQ`), from the boundary per-sequence
   certificate binding `hbseq` (BBR02: for every boundary standing sequence below `δ*` at the
   ratios `δ_{n+1}`, a tail whose members carry a boundary-torus family `E` with a rim-product
   certificate whose external tori are the boundary components);
3. the common static threshold of
   `exists_graph_threshold_disj_of_rimProduct_sequence_bindings_fc42_BQ` (one `w₀` for
   `staticCollapseHypotheses`; the nonnegative branch as a geometric structure).

The two arguments `hrows` (closed) and `hbseq` (boundary) are the two certificate producers still
to be written (closed: `closed_rows_of_chain_outputs74` + the delivered last link; boundary:
BAUG-D / BASES / BCG / BCF chain to a certificate); nothing else is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Curvature
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **CAA02** (B:10773–10810) from the closed rows producer `hrows` and the boundary per-sequence
certificate binding `hbseq`: PBR03, BBR03 and their common static threshold. -/
theorem caa02_row_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x)
    (hrows : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (V : CompactCarrier.{u})
      (gV : SmoothRiemannianMetric V.model V.Carrier) (M : ClosedModel V gV) (δ εr Λz : ℝ),
      (∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀) →
        Nonempty (FC39RowsV2 V (BoundaryTori.empty V)))
    (hbseq : ∃ δStar : ℝ, 0 < δStar ∧
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
          curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1))) →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ E : BoundaryTori (W n) (B n).count,
          (∃ Dc : DecompositionCertificate (W n) E, Dc.RimProduct) ∧
          ∀ i, Set.range (E.torusMap i) = (B n).component i) :
    (∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            SectionalBoundedBelow g' 0)) ∧
    (∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ i, Set.range (G.external.torusMap (e i)) = B.component i) ∧
    (∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)) := by
  obtain ⟨δStar, hδ, hseq⟩ := hbseq
  refine ⟨pbr03_threshold_FCW K hK A hA hrows, ?_,
    exists_graph_threshold_disj_of_rimProduct_sequence_bindings_fc42_BQ K A
      (fun W _ g hs => closedSeq_of_rows_FCW K hK A hA hrows W g hs) ⟨δStar, hδ, hseq⟩⟩
  exact boundary_graph_threshold_of_sequence_binding_rimProduct_BQ K A hδ hseq
    fun W _ _ _ D hp =>
      exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct W D hp

end DifferentialGeometry.Geometry.Collapse
