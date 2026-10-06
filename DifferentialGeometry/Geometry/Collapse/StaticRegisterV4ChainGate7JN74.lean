import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFacesAssembleJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCornerRankPrim3JN74

/-!
# Draft 74, FC39 gate 1A at `D_R`, eighth form: the faces produced

Lane S-JUNCTIONS (by S-JUNCTIONS5), G30 consumer (suffix `_JN74`). `closed_rows_gate_prim3_JN74`
(G31) with `faces := faces3_JN74` (G30, fields g1–g7 produced) and `rims` produced from the faces
and the endpoint primitives by `exists_rims_of_faces3_JN74` (G31). The only residual input of the
gate is `hprim`, the per-endpoint EDP05 primitives (b smooth, `db ≠ 0`, `C₂ ∩ U = {b ≥ 0}`, the
face function equals `b ∘ q₁` near the rim).
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

/-- The produced face facts of the gate at `D_R` (exit `slimExitAt3_OCL`, the produced edge and
remainder exits). -/
abbrev facesAt3_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    EDP05HorizontalExitU74 (S.stagesAtZ_OCL B hT hεr A)
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr) (S.slimExitAt3_OCL B hT hεr A hK))
      (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
      (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
        (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw)) :=
  S.faces3_JN74 B hT hεr A hK (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
    (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
      (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw))
    Htail hNb hcw

/-- **FC39 gate 1A at `D_R`, eighth form**: the faces and the rims are produced; the residual input
is `hprim`. -/
theorem closed_rows_gate7_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
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
              ((S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts.horizontal e) x =
              b ((S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.proj ⟨x, hx⟩)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate_prim3_JN74 B hT hεr A hK hNb hcw Htail
    (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail)
    (Classical.choice (S.exists_rims_of_faces3_JN74 B hT hεr A hK
      (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
      (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
        (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw))
      hNb hcw (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail) rfl
      (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts hprim)) hprim

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
