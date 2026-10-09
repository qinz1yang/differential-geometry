import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4CaaFCW
import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctive

/-!
# Consumers of the CAA02 wrapper: the closed threshold in the form FC45 reads

Lane S-FC-WRAP, group G5 (suffix `_FCW`). `pbr03_closed_geometric_FCW`: PBR03's closed threshold
(from the closed rows producer) turned into the V3 form without the finite-scale hypothesis whose
nonnegative branch is a closed geometric structure (spherical, spherical product or Euclidean), by
`finite_scales_disj_of_raw_or_aux_nonneg` and
`exists_closed_graph_threshold_disj_of_finite_scales_disj` applied to `pbr03_threshold_FCW`.
`caa02_static_FCW` is the third conjunct of `caa02_row_FCW` read back as the static threshold.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **PBR03's closed threshold in the geometric disjunctive form** from the closed rows producer. -/
theorem pbr03_closed_geometric_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x)
    (hrows : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (V : CompactCarrier.{u})
      (gV : SmoothRiemannianMetric V.model V.Carrier) (M : ClosedModel V gV) (δ εr Λz : ℝ),
      (∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀) →
        Nonempty (FC39RowsV2 V (BoundaryTori.empty V))) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨w₀, hw₀, hwu, hDI⟩ := pbr03_threshold_FCW K hK A hA hrows
  exact exists_closed_graph_threshold_disj_of_finite_scales_disj
    ⟨w₀, hw₀, hwu, fun W _ g hfin hcol => finite_scales_disj_of_raw_or_aux_nonneg hDI W g hfin hcol⟩

/-- **The static threshold of CAA02** (third conjunct of `caa02_row_FCW`), unpacked. -/
theorem caa02_static_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ) (hA : ∀ x, 0 < x → 0 < A x)
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
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  (caa02_row_FCW K hK A hA hrows hbseq).2.2

end DifferentialGeometry.Geometry.Collapse
