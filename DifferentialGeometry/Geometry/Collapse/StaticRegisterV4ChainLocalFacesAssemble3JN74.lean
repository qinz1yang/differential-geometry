import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLocalFacesHoriz3JN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLocalFacesClassJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRimSmoothJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesAssembleJN74

/-!
# Draft 74, the rim facts at `D_R` given the face facts and the endpoint primitives

Lane S-JUNCTIONS (by S-JUNCTIONS5), G31 exit-3 copy of G26's consumer (suffix `_JN74`). On the
rows of the gate with the exit `slimExitAt3_OCL` (any edge and remainder exits):
`localFaces_assemble_JN74` with
`edge_region`, `edgeSet ⊆ M₂`, `hKR` (`zeroFace_slim_relInt_at_JN74`), the fibre constancy of `T`
(`cornerT_fibreConst_at_JN74`) and of the face functions (`hconstH_atExit3_JN74`) produced, and with
`rimBase`, `rimBase_smooth`, `rim_fibre` from `exists_rimBase_smooth_at_JN74` into
`junctionRimFacts_ofPrimitives_JN74`:

* `exists_rims_of_faces3_JN74`: the whole `JunctionRimFacts74` at `D_R`, given the face facts `F`
  (the gate has `faces` as an input) and the per-endpoint EDP05 primitives (`hprim`).
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
  (edge : EDP04WholeDiskExitU74 (S.stagesAtZ_OCL B hT hεr A))
  (final : FDC03ActualRemainderU74 (S.stagesAtZ_OCL B hT hεr A))

/-- **The rim facts at `D_R`, given the face facts and the endpoint primitives.** -/
theorem exists_rims_of_faces3_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Rw : StageCutRows74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut)
    (hRw : Rw = (S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final)
    (F : JunctionFaceFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut Rw)
    (hprim : ∀ e : Rw.edge.EdgeEnd, ∃ (b : Rw.edge.Base → ℝ)
      (U : TopologicalSpace.Opens Rw.edge.Base), e.1 ∈ U ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
      Rw.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c} ∧
      ∃ N' : Set W.Carrier, IsOpen N' ∧ Rw.edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
        ∃ hx : x ∈ Rw.edge.source,
          Rw.slimPieces.residualFn (F.horizontal e) x = b (Rw.edge.proj ⟨x, hx⟩)) :
    Nonempty (JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A
      (S.stagesAtZ_OCL B hT hεr A).cut Rw) := by
  obtain ⟨rimBase, hsm, hrim⟩ := S.exists_rimBase_smooth_at_JN74 B hT hεr A
    (S.zsp02SmoothExit74 hεr) hNb hcw Rw.edgeFacts Rw.circleFacts
  have hlf := Rw.localFaces_assemble_JN74 F
    (S.zeroFace_slim_relInt_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)) rimBase hrim
    (S.cut_edgeSet_inter_M₃_eq_vertical_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw
      Rw.edgeFacts)
    (S.cover_at_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
      (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)).edgeSet_subset_M₂
    (fun x y hx hy hxy => S.cornerT_fibreConst_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) Rw x y
      hx hy hxy)
    (by
      subst hRw
      exact fun Fl x y hx hy hxy =>
        S.hconstH_atExit3_JN74 B hT hεr A hK edge final Fl x y hx hy hxy)
    hprim
  exact ⟨S.junctionRimFacts_ofPrimitives_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw Rw
    rimBase hsm hrim hlf⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
