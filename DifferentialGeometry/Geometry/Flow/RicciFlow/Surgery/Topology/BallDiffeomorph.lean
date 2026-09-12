import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapCompletion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.ClosedBall

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (DifferentialGeometry.Topology.ClosedCell (m + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc m

private local instance (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) (⊤ : ℕ∞) (DifferentialGeometry.Topology.ClosedCell (m + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold m

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage}

noncomputable def closedCellBallDiffeomorph (X : SmoothCutCapTransition P Q D N) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
    DifferentialGeometry.Topology.ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall := by
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  let e0 : DifferentialGeometry.Topology.ClosedCell 3 ≃ ThreeBall :=
    Equiv.subtypeEquivRight (fun x => by simp [Metric.mem_closedBall, dist_eq_norm])
  have hcont : Continuous (e0 : DifferentialGeometry.Topology.ClosedCell 3 → ThreeBall) :=
    continuous_subtype_val.subtype_mk _
  have hcont' : Continuous (e0.symm : ThreeBall → DifferentialGeometry.Topology.ClosedCell 3) :=
    continuous_subtype_val.subtype_mk _
  have hto : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
      (e0 : DifferentialGeometry.Topology.ClosedCell 3 → ThreeBall) := by
    intro x
    refine (ContMDiffAt.iff_comp_isImmersionAt
      (hφ := X.ball_induced.isImmersion.isImmersionAt (e0 x))).mpr ⟨hcont.continuousAt, ?_⟩
    have h : (Subtype.val ∘ (e0 : DifferentialGeometry.Topology.ClosedCell 3 → ThreeBall)) =
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) := by
      funext y
      rfl
    rw [h]
    exact (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 2).contMDiff.contMDiffAt
  have hfrom : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
      (e0.symm : ThreeBall → DifferentialGeometry.Topology.ClosedCell 3) := by
    intro y
    refine (ContMDiffAt.iff_comp_isImmersionAt
      (hφ := (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion
        2).isImmersion.isImmersionAt (e0.symm y))).mpr ⟨hcont'.continuousAt, ?_⟩
    have h : (Subtype.val ∘ (e0.symm : ThreeBall → DifferentialGeometry.Topology.ClosedCell 3)) =
        (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3)) := by
      funext z
      rfl
    rw [h]
    exact X.ball_induced.contMDiff.contMDiffAt
  exact ⟨e0, hto, hfrom⟩

theorem cap_isSmoothEmbedding_closedCell (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun z : DifferentialGeometry.Topology.ClosedCell 3 =>
        X.trace.capping.cap b (X.closedCellBallDiffeomorph z)) := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
    (I := 𝓡∂ 3) (J := ThreeModel) (M := ThreeBall) (N := N.Carrier)
    (P := DifferentialGeometry.Topology.ClosedCell 3)
    (X.trace.capping.cap b) (X.cap_smooth b) (X.closedCellBallDiffeomorph)

theorem closedCellBallDiffeomorph_sphereToClosedCell (X : SmoothCutCapTransition P Q D N)
    (z : Sphere 2) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
    X.closedCellBallDiffeomorph (DifferentialGeometry.Topology.sphereToClosedCell z) =
      sphereToThreeBall z := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  apply Subtype.ext
  rfl

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
