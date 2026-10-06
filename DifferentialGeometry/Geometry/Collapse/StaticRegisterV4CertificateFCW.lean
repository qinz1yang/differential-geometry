import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEPbrZ
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42SequenceBindings
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed

/-!
# PBR02's certificate part and PBR03's closed threshold from the closed rows producer

Lane S-FC-WRAP, group G5 (suffix `_FCW`). Blueprint `master207B.tex`, PBR02 (B:10257–10275: "every
sufficiently late member of the closed standing construction has an actual FC39 decomposition and
finite KL graph presentation on its SAME smooth carrier") and PBR03 (B:10277–10333, the last line:
"PBR02 makes every sufficiently late counterexample a graph manifold").

The tree has (i) PBR02's STATIC data (`pbr02_staticEZ_RGC`: one register, on every late member the
normalized model `M` and, at every base point `x₀`, the rows' source
`S : ClosedChainEZRowsSource_RGC` whose `S.chain` is the enhanced chain with (JA)), (ii) the FC39
last link `exists_strongCertificate_of_rows_GFIN` (closed rows `FC39RowsV2 W (BoundaryTori.empty W)`
give a strong certificate), (iii) FC42 form (b) (`StrongCertificate.raw_or_aux_nonneg`) and (iv) the
sequence-binding threshold `closed_graph_threshold_of_sequence_binding_rimProduct_BQ`. What is NOT
in the tree is the closed ROWS PRODUCER (the unwritten `closed_rows_of_chain_outputs74`): from the
chain outputs at every base point of the model, the record `FC39RowsV2 W (BoundaryTori.empty W)` of
the carrier `W` itself (the same-kind transport `FC39RowsV2.transportEmpty74` along `M.ψ` is
delivered). It enters these theorems as the single explicit argument `hrows` (premise
`∀ x₀, ∃ S, S.chain.x₀ = x₀` of the static data, conclusion `Nonempty (FC39RowsV2 …)`; a theorem
proving it makes every statement here unconditional).

* `pbr02_certificate_FCW`: PBR02 in full: the static data of `pbr02_staticEZ_RGC` AND, on every
  late member, the closed strong certificate `Dc` (rim-product clause) and, by FC42 form (b), a raw
  graph presentation or a closed auxiliary `sec ≥ 0` metric (the nonnegative branch).
* `closedSeq_of_rows_FCW`: the per-sequence closed binding (`closedSeq` of
  `exists_graph_threshold_disj_of_rimProduct_sequence_bindings_fc42_BQ`) derived from it.
* `pbr03_threshold_FCW`: PBR03 (closed threshold with the nonnegative branch) from `hrows`.

Consumer: `closedSeq_of_rows_FCW` is the `closedSeq` input of the common static threshold
(`caa02_row_FCW`, file `StaticRegisterV4CaaFCW`).
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **PBR02, certificate part** (B:10257–10275) from the closed rows producer `hrows`: the static
data of `pbr02_staticEZ_RGC` and, on every late member of the closed standing sequence, a closed
strong certificate `Dc` (rim-product clause) from the rows `FC39RowsV2 W (BoundaryTori.empty W)`,
hence a raw graph presentation or a closed auxiliary `sec ≥ 0` metric (FC42 form (b)). -/
theorem pbr02_certificate_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    (hrows : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (V : CompactCarrier.{u})
      (gV : SmoothRiemannianMetric V.model V.Carrier) (M : ClosedModel V gV) (δ εr Λz : ℝ),
      (∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀) →
        Nonempty (FC39RowsV2 V (BoundaryTori.empty V))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m),
          M.gX = Diffeomorph.pullbackMetricCross (gseq m) M.ψ ∧ Nonempty M.X ∧
          (∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀) ∧
          ∃ Dc : ClosedDecompositionCertificate (Wseq m), Dc.cert.RimProduct ∧
            (Nonempty (RawGraphPresentation (Wseq m)) ∨
              ((Wseq m).model.boundary (Wseq m).Carrier = ∅ ∧
                ∃ g' : SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier,
                  SectionalBoundedBelow g' 0)) := by
  obtain ⟨T, hTU, hv, hNb, hcw, hreg, hR⟩ := pbr02_staticEZ_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hv, hNb, hcw, hreg, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨εr, δ, Λz, fun m hm => ?_⟩
  obtain ⟨M, hM, hne, hS⟩ := ht m hm
  obtain ⟨Rw⟩ := hrows T R (Wseq m) (gseq m) M δ εr Λz hS
  obtain ⟨D⟩ := exists_strongCertificate_of_rows_GFIN Rw
  have := (hf m).connected
  exact ⟨M, hM, hne, hS, D.toClosed.toClosedCertificate, D.toClosed.rimProduct,
    D.raw_or_aux_nonneg (Wseq m)⟩

/-- **The per-sequence closed binding from the rows producer**: on every closed standing sequence
(members at `closedCounterexampleRatio (m + 2)`) there is a tail on which every member has a closed
strong certificate (the `closedSeq` input of the common static threshold). -/
theorem closedSeq_of_rows_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x)
    (hrows : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (V : CompactCarrier.{u})
      (gV : SmoothRiemannianMetric V.model V.Carrier) (M : ClosedModel V gV) (δ εr Λz : ℝ),
      (∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀) →
        Nonempty (FC39RowsV2 V (BoundaryTori.empty V)))
    (W : ℕ → CompactCarrier.{u}) [hW : ∀ m, ConnectedSpace (W m).Carrier]
    (g : ∀ m, SmoothRiemannianMetric (W m).model (W m).Carrier)
    (hseq : ∀ m, (∀ p, curvatureRadius (g m) p ≠ ⊤) ∧
      closedCollapseHypotheses (W m) (g m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ Dc : ClosedDecompositionCertificate (W m), Dc.cert.RimProduct := by
  obtain ⟨T, -, -, -, -, ⟨R⟩, hR⟩ := pbr02_certificate_FCW K hK A hA W g
    (fun m => ⟨(hseq m).2.1, hW m⟩) (fun m => (hseq m).2) hrows
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨R.later.tail, fun m hm => ?_⟩
  obtain ⟨-, -, -, -, Dc, hDc, -⟩ := ht m hm
  exact ⟨Dc, hDc⟩

/-- **PBR03, the closed static threshold** (B:10277–10333, the nonnegative branch included, form
(b)) from the closed rows producer `hrows`: there is `w₀ < ω₃` such that every closed connected
member with finite curvature scales at volume ratio `w₀` and the whole-ball derivative bounds is a
graph manifold (raw presentation) or carries a closed auxiliary `sec ≥ 0` metric. -/
theorem pbr03_threshold_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x)
    (hrows : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (V : CompactCarrier.{u})
      (gV : SmoothRiemannianMetric V.model V.Carrier) (M : ClosedModel V gV) (δ εr Λz : ℝ),
      (∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀) →
        Nonempty (FC39RowsV2 V (BoundaryTori.empty V))) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            SectionalBoundedBelow g' 0) :=
  closed_graph_threshold_of_sequence_binding_rimProduct_BQ K A
    (fun W _ g hseq => closedSeq_of_rows_FCW K hK A hA hrows W g hseq)
    fun W _ _ _ D hp =>
      exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct W D hp

end DifferentialGeometry.Geometry.Collapse
