import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCornerDescentAt3JN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankPrimJN74

/-!
# Draft 74, the gate with `hdesc` and `hrank` produced from the endpoint primitives

Lane S-JUNCTIONS (by S-JUNCTIONS5), G31 exit-3 copy of G29's consumer (suffix `_JN74`).
`cornerRankDescended_of_prim_JN74` with `hKR` produced (`zeroFace_slim_relInt_at_JN74`) and `hdesc`
produced (`cornerDescent_at3_JN74`, G27):

* `closed_rows_gate_prim3_JN74`: `closed_rows_gate6d_JN74` whose residual inputs are the faces (g),
  the rims (h) and the per-endpoint EDP05 primitives `hprim` (the data of
  `exists_rims_of_faces3_JN74`, G26): `hdesc` and `hrank` are PRODUCED.
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
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)

/-- The rows of the gate with the exit `slimExitAt3_OCL`. -/
abbrev rows3At_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    StageCutRows74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut :=
  (S.stagesAtZ_OCL B hT hεr A).rows
    (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr) (S.slimExitAt3_OCL B hT hεr A hK))
    (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
    (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
      (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw))

/-- **The gate with `hdesc` and `hrank` produced from the endpoint primitives.** -/
theorem closed_rows_gate_prim3_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (faces : EDP05HorizontalExitU74 (S.stagesAtZ_OCL B hT hεr A)
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK))
      (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
      (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
        (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw)))
    (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut
      (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail))
    (hprim : ∀ e : (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.EdgeEnd,
      ∃ (b : (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.Base → ℝ)
        (U : TopologicalSpace.Opens (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.Base),
        e.1 ∈ U ∧ ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
        (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.cbase ∩ U =
          {c | c ∈ U ∧ 0 ≤ b c} ∧
        ∃ N' : Set W.Carrier, IsOpen N' ∧
          (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
          ∃ hx : x ∈ (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.source,
            (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).slimPieces.residualFn
              (faces.facts.horizontal e) x =
              b ((S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.proj ⟨x, hx⟩)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate6e_JN74 B hT hεr A hK hNb hcw Htail faces rims fun e => by
    obtain ⟨b, U, heU, hb, hbreg, hCU, hN⟩ := hprim e
    exact StageCutRows74.cornerRankDescended_of_prim_JN74
      (S.zeroFace_slim_relInt_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)) e
      (S.cornerDescent_at3_JN74 B hT hεr A hK _ _ _ rfl faces.facts rims e) b U heU hb hbreg hCU hN

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
