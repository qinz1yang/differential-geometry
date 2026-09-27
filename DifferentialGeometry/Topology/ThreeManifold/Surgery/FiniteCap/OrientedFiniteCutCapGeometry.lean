import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCutCapGeometry
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapIntrinsicBoundaryOrientation

set_option autoImplicit false
noncomputable section
open Set Function Module TopologicalSpace Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
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
private local instance : HasSmoothBoundary ER IH IR := productHalfSpaceBoundaryModel
private local instance : Nonempty (HasSmoothBoundary.boundaryH IR) := show Nonempty E2 from inferInstance
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    ChartedSpace E2 (BoundaryManifold IR X) := BoundaryManifold.chartedSpace (I := IR)
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold IR X) := BoundaryManifold.isManifold (I := IR)
private local instance : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) := show Nonempty E2 from inferInstance
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X] [IsManifold (𝓡∂ 3) ∞ X] :
    ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) X) := BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X] [IsManifold (𝓡∂ 3) ∞ X] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) X) := BoundaryManifold.isManifold (I := 𝓡∂ 3)

private def b2 : Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
private def i2 : Fin 2 ≃ Fin (Module.finrank ℝ E2) := finCongr (by simp)
private def i3 : Fin 3 ≃ Fin (Module.finrank ℝ E3) := finCongr (by simp)
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

def OrientedFiniteCutCapGeometry (hδ1 : ∀ i, precision i < 1)
    (R : Set (ConnectedComponents (cutCore f))) (o : SmoothOrientation I M) : Prop :=
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
    let : ChartedSpace IH (retainedCore f Rᶜ) := retainedCoreChartedSpace I hdim hδ f hf hdisj Rᶜ
    let : IsManifold IR ∞ (retainedCore f Rᶜ) := retainedCore_isManifold I hdim hδ f hf hdisj Rᶜ hs
    let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    let F := finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R
    ∃ oE : (ι × Bool) → Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
      ∃ oQ : SmoothOrientation (𝓡 3) OrientedQ,
      ∃ oRet : SmoothOrientation (𝓡 3) (finiteCapRetained hL hδ f hf hdisj R),
      ∃ oDisc : SmoothOrientation (𝓡 3) (finiteCapDiscarded hL hδ f hf hdisj R),
      ∃ oSum : SmoothOrientation (𝓡 3)
        (finiteCapRetained hL hδ f hf hdisj R ⊕ finiteCapDiscarded hL hδ f hf hdisj R),
      ∃ oN : SmoothOrientation (𝓡 2) (BoundaryManifold IR (cutCore f)),
        FiniteCutCapGeometry I hdim hL hδ f hf hdisj hs hδ1 R ∧
        (
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
        (∀ p : OrientedQ,
          tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) (𝓡 3) F.symm
            (fun x => (F.symm.mfderivToContinuousLinearEquiv (by simp) x).bijective) p).toLinearEquiv
              (oQ.val p) = oSum.val (F.symm p)) ∧
        (∀ p : retainedCore f R,
          tangentOrientationEquiv (differentialEquivOfBijective IR (𝓡 3) (finiteRetainedCoreInclusion hL hδ f hf hdisj R) (finiteRetainedCoreInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs R) p).toLinearEquiv
            ((retainedCoreSmoothOrientation I hdim hδ f hf hdisj hs R o).val p) =
              oRet.val (finiteRetainedCoreInclusion hL hδ f hf hdisj R p)) ∧
        (∀ p : retainedCore f Rᶜ,
          tangentOrientationEquiv (differentialEquivOfBijective IR (𝓡 3) (finiteRetainedCoreInclusion hL hδ f hf hdisj Rᶜ) (finiteRetainedCoreInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs Rᶜ) p).toLinearEquiv
            ((retainedCoreSmoothOrientation I hdim hδ f hf hdisj hs Rᶜ o).val p) =
              oDisc.val (finiteRetainedCoreInclusion hL hδ f hf hdisj Rᶜ p)) ∧
        (∀ (b : ι × Bool) (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R) (x : Ball L),
          tangentOrientationEquiv (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (fun y : Ball L => (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩, hb⟩ : finiteCapRetained hL hδ f hf hdisj R)) (finiteRetainedCapInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs R b hb) x).toLinearEquiv
            ((closedBallSmoothOrientation hL (oE b)).val x) = oRet.val ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, hb⟩) ∧
        (∀ (b : ι × Bool) (hb : cuttingSphereComponent hδ f hf hdisj b ∈ Rᶜ) (x : Ball L),
          tangentOrientationEquiv (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (fun y : Ball L => (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩, hb⟩ : finiteCapRetained hL hδ f hf hdisj Rᶜ)) (finiteRetainedCapInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs Rᶜ b hb) x).toLinearEquiv
            ((closedBallSmoothOrientation hL (oE b)).val x) = oDisc.val ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, hb⟩)
        ) ∧
        oN = nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL (fun b => Orientation.reindex ℝ E3 i3.symm (oE b)) ∧
        (∀ (b : ι × Bool) (x : Ball L),
          Orientation.reindex ℝ E3 i3 (closedBallTangentOrientationThree hL (Orientation.reindex ℝ E3 i3.symm (oE b)) x) =
            (closedBallSmoothOrientation hL (oE b)).val x) ∧
        (∀ (b : ι × Bool) (x : BoundaryManifold (𝓡∂ 3) (Ball L)),
          (closedBallBoundarySmoothOrientation hL (Orientation.reindex ℝ E3 i3.symm (oE b))).val x =
            Orientation.reindex ℝ E2 i2 (normalFirstOrientation (closedBallBoundaryIntrinsicFrame hL x) b2
              (closedBallTangentOrientationThree hL (Orientation.reindex ℝ E3 i3.symm (oE b)) x.val))) ∧
        (∀ b : ι × Bool,
          let hB := cuttingCollarWidth_pos (hδ b.1)
          letI := halfClosedIntervalChartedSpace hB
          letI := halfClosedInterval_isManifold hB
          letI := retainedFaceChartedSpace hB
          letI := retainedFace_isManifold hB
          ∀ q : retainedFace (cuttingCollarWidth (precision b.1)),
            oN.val (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val =
              Orientation.reindex ℝ E2 i2 (normalFirstOrientation (nativeCoreBoundaryIntrinsicFrame I hdim hδ f hf hdisj hs hL b q) b2
                (nativeCoreTangentOrientationThree I hdim hδ f hf hdisj hs o (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val.val))) ∧
        (∀ b : ι × Bool,
          let hB := cuttingCollarWidth_pos (hδ b.1)
          letI := halfClosedIntervalChartedSpace hB
          letI := halfClosedInterval_isManifold hB
          letI := retainedFaceChartedSpace hB
          letI := retainedFace_isManifold hB
          ∀ q : retainedFace (cuttingCollarWidth (precision b.1)), ∀ t : ℝ, ∀ v : E2,
            let D : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR (boundaryInclusion IR (cutCore f)) (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val
            let K := differentialEquivOfBijective IR IR (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
              (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b) q.val
            let T := differentialEquivOfBijective IR (𝓡 3) (radialCollarOrientationMap L (cuttingCollarWidth (precision b.1)))
              (radialCollarOrientationMap_mfderiv_bijective hL hB) q.val
            nativeCoreBoundaryIntrinsicFrame I hdim hδ f hf hdisj hs hL b q (t, v) =
              t • K (T.symm (retainedFaceOutwardNormal (cuttingCollarWidth (precision b.1)) q)) + D v) ∧
        (∀ (b : ι × Bool) (x : BoundaryManifold (𝓡∂ 3) (Ball L)),
          let φ := nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b
          tangentOrientationEquiv (φ.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
            ((closedBallBoundarySmoothOrientation hL (Orientation.reindex ℝ E3 i3.symm (oE b))).val x) = -oN.val (φ x).val ∧
          (φ x).val.val = cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, closedBallBoundaryDiffeomorph hL x⟩ ∧
          finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x.val⟩ =
            finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj (φ x).val.val)

theorem orientedFiniteCutCapGeometry [CompactSpace M] [Nonempty M]
    (hδ1 : ∀ i, precision i < 1) (R : Set (ConnectedComponents (cutCore f)))
    (o : SmoothOrientation I M) (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ)) :
    OrientedFiniteCutCapGeometry I hdim hL hδ f hf hdisj hs hδ1 R o := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
  let : ChartedSpace IH (retainedCore f Rᶜ) := retainedCoreChartedSpace I hdim hδ f hf hdisj Rᶜ
  let : IsManifold IR ∞ (retainedCore f Rᶜ) := retainedCore_isManifold I hdim hδ f hf hdisj Rᶜ hs
  let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let F := finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R
  obtain ⟨oE, oQ, oRet, oDisc, oSum, oN, hOri⟩ :=
    exists_finiteCapSelectedSmoothOrientations_with_intrinsic_boundary I hdim hL hδ f hf hdisj hs R o
  exact ⟨oE, oQ, oRet, oDisc, oSum, oN,
    finiteCutCapGeometry I hdim hL hδ f hf hdisj hs hδ1 R hnontrivial, hOri⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
