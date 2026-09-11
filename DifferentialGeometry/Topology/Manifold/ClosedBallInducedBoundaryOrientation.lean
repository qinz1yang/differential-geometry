import DifferentialGeometry.Topology.Manifold.ClosedBallBoundaryOrientation

set_option autoImplicit false
noncomputable section
open Set Function Module Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty E2 from inferInstance
private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.isManifold (I := 𝓡∂ 3)
private def b2 : Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
private def i2 : Fin 2 ≃ Fin (Module.finrank ℝ E2) := finCongr (by simp)

private def i3 : Fin 3 ≃ Fin (Module.finrank ℝ E3) := finCongr (by simp)
private def ballInclusionDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    Ball L → E3 ≃L[ℝ] E3 := by
  let := closedBallChartedSpace hL
  exact differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
    (closedBall_inclusion_mfderiv_bijective hL)

def closedBallTangentOrientationThree {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    Ball L → Orientation ℝ E3 (Fin 3) := by
  let := closedBallChartedSpace hL
  exact fun x => Orientation.map (Fin 3) (ballInclusionDerivative hL x).symm.toLinearEquiv o

theorem closedBallTangentOrientationThree_eq {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ x : Ball L, Orientation.reindex ℝ E3 i3 (closedBallTangentOrientationThree hL o x) =
      (closedBallSmoothOrientation hL (Orientation.reindex ℝ E3 i3 o)).val x := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro x
  change Orientation.reindex ℝ E3 i3 (Orientation.map (Fin 3) (ballInclusionDerivative hL x).symm.toLinearEquiv o) =
    tangentOrientationEquiv (ballInclusionDerivative hL x).symm.toLinearEquiv (Orientation.reindex ℝ E3 i3 o)
  rw [tangentOrientationEquiv_self]
  induction o using Module.Ray.ind
  rfl

def closedBallBoundaryIntrinsicFrame {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → (ℝ × E2) ≃ₗ[ℝ] E3 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => (hypersurfaceNormalFrameEquiv (closedBallBoundaryAmbient hL)
    (closedBallBoundaryRadialNormal hL) (closedBallBoundaryNormalFrame_bijective hL) b).toLinearEquiv.trans
      (ballInclusionDerivative hL b.val).symm.toLinearEquiv

private def boundaryInclusionDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E2 →L[ℝ] E3 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => mfderiv (𝓡 2) (𝓡∂ 3) (boundaryInclusion (𝓡∂ 3) (Ball L)) b
private def boundaryAmbientDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E2 →L[ℝ] E3 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => mfderiv (𝓡 2) (𝓡 3) (closedBallBoundaryAmbient hL) b
private theorem boundary_inclusion_chain {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      boundaryAmbientDerivative hL b = (ballInclusionDerivative hL b.val : E3 →L[ℝ] E3).comp
        (boundaryInclusionDerivative hL b) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  exact mfderiv_comp b ((isSmoothEmbedding_closedBall_inclusion hL).contMDiff.mdifferentiableAt (by simp))
    ((boundaryInclusion_contMDiff (I := 𝓡∂ 3) (M := Ball L)).mdifferentiableAt (by simp))

theorem closedBallBoundaryIntrinsicFrame_apply {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L), ∀ t : ℝ, ∀ v : E2,
      let D : E2 →L[ℝ] E3 := mfderiv (𝓡 2) (𝓡∂ 3) (boundaryInclusion (𝓡∂ 3) (Ball L)) b
      closedBallBoundaryIntrinsicFrame hL b (t,v) =
        t • (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
          (closedBall_inclusion_mfderiv_bijective hL) b.val).symm (closedBallBoundaryRadialNormal hL b) + D v := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b t v
  change (ballInclusionDerivative hL b.val).symm
    (t • closedBallBoundaryRadialNormal hL b + boundaryAmbientDerivative hL b v) =
      t • (ballInclusionDerivative hL b.val).symm (closedBallBoundaryRadialNormal hL b) + boundaryInclusionDerivative hL b v
  rw [map_add, map_smul, boundary_inclusion_chain hL b]
  change t • (ballInclusionDerivative hL b.val).symm (closedBallBoundaryRadialNormal hL b) +
    (ballInclusionDerivative hL b.val).symm ((ballInclusionDerivative hL b.val) (boundaryInclusionDerivative hL b v)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem closedBallBoundarySmoothOrientation_induced {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      (closedBallBoundarySmoothOrientation hL o).val b = Orientation.reindex ℝ E2 i2
        (normalFirstOrientation (closedBallBoundaryIntrinsicFrame hL b) b2 (closedBallTangentOrientationThree hL o b.val)) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  rw [closedBallBoundarySmoothOrientation_apply]
  have h := normalFirstOrientation_map
    (hypersurfaceNormalFrameEquiv (closedBallBoundaryAmbient hL) (closedBallBoundaryRadialNormal hL)
      (closedBallBoundaryNormalFrame_bijective hL) b).toLinearEquiv
    (ballInclusionDerivative hL b.val).symm.toLinearEquiv b2 o
  exact congrArg (Orientation.reindex ℝ E2 i2) h.symm
end DifferentialGeometry.Topology.Manifold
