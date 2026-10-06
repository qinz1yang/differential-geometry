import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate6JN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCornerDescentJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesVertJN74

/-!
# Draft 74, `local_faces` at `D_R`: the vertical points

Lane S-JUNCTIONS (by S-JUNCTIONS4), G23 consumer (suffix `_JN74`). On the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero` and ANY rows `Rw : StageCutRows74 P.A P.cut` with face
facts `F`: the vertical case of `local_faces` (`localFaces_vertical_JN74`) with its three chain
inputs produced at `D_R`: `edge_region` (`cut_edgeSet_inter_M₃_eq_vertical_JN74`, G9),
`edgeSet ⊆ M₂` (`cover_at_OCL`) and the fibre constancy of `T` (`cornerT_fibreConst_at_JN74`, G19).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- **`local_faces` at a vertical point, on the actual rows at `D_R`.** -/
theorem localFaces_vertical_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (F : JunctionFaceFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut Rw)
    (rimBase : Rw.edge.Base → Rw.circle.Base)
    (hrim : ∀ c ∈ Rw.edge.cbase, Rw.edge.rim c = Rw.circle.fibre (rimBase c))
    {c' : Rw.edge.Base} (hc' : c' ∈ Rw.edge.cbase) (hnf : c' ∉ frontier Rw.edge.cbase) :
    ∃ U : TopologicalSpace.Opens Rw.circle.Base, rimBase c' ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel Rw.slimPieces.ResidualFace Rw.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel Rw.slimPieces.ResidualFace Rw.edge.EdgeBaseComponent →
          Rw.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f (rimBase c') = 0 ∧
          {c'' | c'' ∈ U ∧ c'' ∈ Rw.circle.cbase ∧ φ f c'' = 0} =
            {c'' | c'' ∈ U ∧ c'' ∈ Rw.circle.cbase ∧
              Rw.circle.fibre c'' ⊆ circleFaceSet Rw.slimPieces Rw.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) (rimBase c') =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) (rimBase c') w) ∧
        Rw.circle.cbase ∩ U = {c'' | c'' ∈ U ∧ ∀ f ∈ L, φ f c'' ≤ 0} :=
  Rw.localFaces_vertical_JN74 F rimBase hrim
    (S.cut_edgeSet_inter_M₃_eq_vertical_JN74 B hT hεr A zero hNb hcw Rw.edgeFacts)
    (S.cover_at_OCL B hT hεr A zero (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)).edgeSet_subset_M₂
    (fun x y hx hy hxy => S.cornerT_fibreConst_at_JN74 B hT hεr A zero Rw x y hx hy hxy) hc' hnf

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
