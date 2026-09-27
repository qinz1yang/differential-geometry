import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapBallOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapDecomposition
import DifferentialGeometry.Topology.Manifold.ClopenOrientation

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev ER := E2 × EuclideanSpace ℝ (Fin 1)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "OrientedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

theorem exists_finiteCapSelectedSmoothOrientations
    (R : Set (ConnectedComponents (cutCore f))) (o : SmoothOrientation I M) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    let F := finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R
    ∃ oE : (ι × Bool) → Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
      ∃ oQ : SmoothOrientation (𝓡 3) OrientedQ,
      ∃ oRet : SmoothOrientation (𝓡 3) (finiteCapRetained hL hδ f hf hdisj R),
      ∃ oDisc : SmoothOrientation (𝓡 3) (finiteCapDiscarded hL hδ f hf hdisj R),
      ∃ oSum : SmoothOrientation (𝓡 3)
        (finiteCapRetained hL hδ f hf hdisj R ⊕ finiteCapDiscarded hL hδ f hf hdisj R),
        (∀ b, oE b = (Module.finBasis ℝ E3).orientation ∨ oE b = -(Module.finBasis ℝ E3).orientation) ∧
        (∀ b : ι × Bool,
          letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
          letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
          ∀ q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)),
            (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) (oE b)).val q =
              (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q) ∧
        (∀ p : finiteCoreInteriorOpens hL hδ f hf hdisj,
          oQ.val p.val = (finiteOldSmoothOrientation I hdim hL hδ f hf hdisj hs o).val p) ∧
        (∀ (b : ι × Bool) (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b),
          oQ.val p.val = (finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b (oE b)).val p) ∧
        (∀ p : cutCore f,
          tangentOrientationEquiv (differentialEquivOfBijective IR (𝓡 3)
            (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
            (finiteCoreInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs) p).toLinearEquiv
              ((cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val p) =
                oQ.val (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p) ) ∧
        (∀ (b : ι × Bool) (x : Ball L),
          tangentOrientationEquiv (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3)
            (fun y : Ball L => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩)
            (finiteCapInclusion_ball_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) x).toLinearEquiv
              ((closedBallSmoothOrientation hL (oE b)).val x) =
                oQ.val (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) ) ∧
        (∀ p : finiteCapRetained hL hδ f hf hdisj R, oRet.val p = oQ.val p.val) ∧
        (∀ p : finiteCapDiscarded hL hδ f hf hdisj R, oDisc.val p = oQ.val p.val) ∧
        (∀ p : finiteCapRetained hL hδ f hf hdisj R, oSum.val (Sum.inl p) = oRet.val p) ∧
        (∀ p : finiteCapDiscarded hL hδ f hf hdisj R, oSum.val (Sum.inr p) = oDisc.val p) ∧
        (∀ p : finiteCapRetained hL hδ f hf hdisj R ⊕ finiteCapDiscarded hL hδ f hf hdisj R,
          tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) (𝓡 3) F
            (fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective) p).toLinearEquiv
              (oSum.val p) = oQ.val (F p)) ∧
        ∀ p : OrientedQ,
          tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) (𝓡 3) F.symm
            (fun x => (F.symm.mfderivToContinuousLinearEquiv (by simp) x).bijective) p).toLinearEquiv
              (oQ.val p) = oSum.val (F.symm p) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let F := finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R
  obtain ⟨oE, oQ, hsign, hcollar, hOld, hCap, hCore, hBall⟩ :=
    exists_finiteCapSmoothOrientation_preserving_core_and_caps I hdim hL hδ f hf hdisj hs o
  let Ret := finiteCapRetained hL hδ f hf hdisj R
  let Disc := finiteCapDiscarded hL hδ f hf hdisj R
  let hRet := (isClopen_finiteCapRetained_discarded hL hδ f hf hdisj R).1.isClosed
  let oRet := restrictSmoothOrientation (𝓡 3) Ret oQ
  let oDisc := restrictSmoothOrientation (𝓡 3) Disc oQ
  let oSum := clopenSumSmoothOrientation (𝓡 3) Ret hRet oQ
  exact ⟨oE, oQ, oRet, oDisc, oSum, hsign, hcollar, hOld, hCap, hCore, hBall,
    fun _ => rfl, fun _ => rfl,
    fun p => clopenSumSmoothOrientation_apply (𝓡 3) Ret hRet oQ (Sum.inl p),
    fun p => clopenSumSmoothOrientation_apply (𝓡 3) Ret hRet oQ (Sum.inr p),
    fun p => clopenSumSmoothOrientation_pushforward (𝓡 3) Ret hRet oQ p,
    fun p => clopenSumSmoothOrientation_symm_preserves (𝓡 3) Ret hRet oQ p⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
