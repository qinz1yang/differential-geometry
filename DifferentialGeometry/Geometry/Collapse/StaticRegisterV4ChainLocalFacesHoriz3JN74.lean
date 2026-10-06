import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFaceRemovalJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimEndFreeOCLConsumer
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLocalFacesHorizJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCornerDescentJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesHorizJN74

/-!
# Draft 74, `local_faces` at `D_R`: the horizontal points

Lane S-JUNCTIONS (by S-JUNCTIONS5), G31 exit-3 copy of G24's consumer (suffix `_JN74`). On the
rows of the gate with the exit `slimExitAt3_OCL` (the stage geometry of `closedStagesAt_OCL`,
any edge and remainder exits):

* `hconstH_atExit3_JN74`: every residual face function is constant on the `q₀`-fibres of its
  neighbourhood: zero face by `zero_ratio_fibreConst_JN74` (the ratio is a function of `E`),
  new slim end by `slimEnd3_circleFibreConst_OCL` (S-REG-CHAIN6), no cusp faces (`n = 0`);
* `localFaces_horizontal_at3_JN74`: `localFaces_horizontal_JN74` with `hKR` produced
  (`zeroFace_slim_relInt_at_JN74`) and `hconstH` produced.
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

/-- **The face functions are constant on the `q₀`-fibres, for the exit `slimExitAt3_OCL`.** -/
theorem hconstH_atExit3_JN74
    (Fl : ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.ResidualFace)
    (x y : ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).circle.domain)
    (hx : (x : W.Carrier) ∈ (((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.residualNear Fl :
          Set W.Carrier))
    (hy : (y : W.Carrier) ∈ (((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.residualNear Fl :
          Set W.Carrier))
    (hxy : ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).circle.proj y =
      ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).circle.proj x) :
    ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.residualFn Fl x.1 =
    ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.residualFn Fl y.1 := by
  have hE := S.circle_fibre_E_eq_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) _ x y hxy
  rcases Fl with ⟨F' | F', hF'⟩ | en
  · exact S.zero_ratio_fibreConst_JN74 (S.zsp02SmoothExit74 hεr) F'.1 hx hy hE
  · obtain ⟨b, -⟩ := F'
    exact (IsEmpty.false b).elim
  · exact S.slimEnd3_circleFibreConst_OCL B hT hεr A hK edge final en x y hx hy hxy

/-- **`local_faces` at a horizontal point, on the actual rows at `D_R`** (exit
`slimExitAt3_OCL`). -/
theorem localFaces_horizontal_at3_JN74
    (Rw : StageCutRows74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut)
    (hRw : Rw = (S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final)
    (F : JunctionFaceFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut Rw)
    (Fl : Rw.slimPieces.ResidualFace) {c : Rw.circle.Base} {x₀ : W.Carrier}
    (hx₀ : x₀ ∈ Rw.circle.fibre c) (hx₀F : x₀ ∈ Rw.slimPieces.residualSet Fl)
    (hnoE : ∀ x ∈ Rw.circle.fibre c, x ∉ (S.stagesAtZ_OCL B hT hεr A).cut.edgeSet) :
    ∃ U : TopologicalSpace.Opens Rw.circle.Base, c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel Rw.slimPieces.ResidualFace Rw.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel Rw.slimPieces.ResidualFace Rw.edge.EdgeBaseComponent →
          Rw.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c'' | c'' ∈ U ∧ c'' ∈ Rw.circle.cbase ∧ φ f c'' = 0} =
            {c'' | c'' ∈ U ∧ c'' ∈ Rw.circle.cbase ∧
              Rw.circle.fibre c'' ⊆ circleFaceSet Rw.slimPieces Rw.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        Rw.circle.cbase ∩ U = {c'' | c'' ∈ U ∧ ∀ f ∈ L, φ f c'' ≤ 0} := by
  subst hRw
  exact StageCutRows74.localFaces_horizontal_JN74 _ F
    (S.zeroFace_slim_relInt_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)) Fl
    (fun x y hx hy hxy => S.hconstH_atExit3_JN74 B hT hεr A hK edge final Fl x y hx hy hxy)
    hx₀ hx₀F hnoE

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
