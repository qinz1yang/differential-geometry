import DifferentialGeometry.Topology.Manifold.HypersurfaceOrientation
import DifferentialGeometry.Topology.Manifold.ClosedBallOrientation
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false
noncomputable section
open Set Function Module Manifold DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
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

def radialSphereNormalFrame {L : ℝ} (hL : 0 < L) (y : S2) : (ℝ × E2) ≃L[ℝ] E3 :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ E2).trans
    ((PartialDiffeomorph.isLocalDiffeomorphAt IC (𝓡 3) ∞
      (euclideanPolarDiffeomorph (E := E3) (n := 2)) (x := (y, L)) hL).mfderivToContinuousLinearEquiv (by simp))

theorem radialSphereNormalFrame_apply {L : ℝ} (hL : 0 < L) (y : S2) (t : ℝ) (v : E2) :
    radialSphereNormalFrame hL y (t, v) = t • y.val + L • dIncl (n := 2) y v :=
  euclideanPolarMap_mfderiv (y, L) (v, t)

private def scaledSphere (L : ℝ) (y : S2) : E3 := L • y.val
private def sphereNormal (y : S2) : E3 := y.val
private theorem scaledSphere_smooth (L : ℝ) : ContMDiff (𝓡 2) (𝓡 3) ∞ (scaledSphere L) := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val : S2 → E3) := contMDiff_coe_sphere (n := 2)
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun _ : S2 => L) := contMDiff_const
  exact hc.smul hs
private def scaledSphereDifferential (L : ℝ) (y : S2) : E2 →L[ℝ] E3 :=
  mfderiv (𝓡 2) (𝓡 3) (scaledSphere L) y
private theorem scaledSphere_derivative (L : ℝ) (y : S2) :
    scaledSphereDifferential L y = L • dIncl (n := 2) y := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val : S2 → E3) := contMDiff_coe_sphere (n := 2)
  have h := mvfderiv_fun_smul (I := 𝓡 2)
    (mdifferentiableAt_const (c := L) (x := y)) (hs.mdifferentiableAt (by simp) (x := y))
  simp only [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] at h
  change mvfderiv (𝓡 2) (fun z : S2 => L • z.val) y = L • mvfderiv (𝓡 2) (Subtype.val : S2 → E3) y
  exact h
private theorem sphereNormal_continuous : Continuous sphereNormal := continuous_subtype_val
private theorem sphere_frame_eq {L : ℝ} (hL : 0 < L) (y : S2) :
    hypersurfaceNormalFrame (scaledSphere L) sphereNormal y = (radialSphereNormalFrame hL y : (ℝ × E2) →L[ℝ] E3) := by
  apply ContinuousLinearMap.ext
  intro v
  change v.1 • sphereNormal y + scaledSphereDifferential L y v.2 = _
  rw [scaledSphere_derivative]
  exact (radialSphereNormalFrame_apply hL y v.1 v.2).symm
private theorem sphere_frame_bijective {L : ℝ} (hL : 0 < L) (y : S2) :
    Bijective (hypersurfaceNormalFrame (scaledSphere L) sphereNormal y) := by
  rw [sphere_frame_eq hL y]
  exact (radialSphereNormalFrame hL y).bijective
private theorem sphere_frame_equiv {L : ℝ} (hL : 0 < L) (y : S2) :
    (hypersurfaceNormalFrameEquiv (scaledSphere L) sphereNormal (sphere_frame_bijective hL) y).toLinearEquiv =
      (radialSphereNormalFrame hL y).toLinearEquiv := by
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun A : (ℝ × E2) →L[ℝ] E3 => A v) (sphere_frame_eq hL y)

def radialSphereSmoothOrientation {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    SmoothOrientation (𝓡 2) S2 :=
  hypersurfaceSmoothOrientation (scaledSphere L) sphereNormal (scaledSphere_smooth L)
    sphereNormal_continuous (sphere_frame_bijective hL) o

theorem radialSphereSmoothOrientation_apply {L : ℝ} (hL : 0 < L)
    (o : Orientation ℝ E3 (Fin 3)) (y : S2) :
    (radialSphereSmoothOrientation hL o).val y = Orientation.reindex ℝ E2 i2
      (normalFirstOrientation (radialSphereNormalFrame hL y).toLinearEquiv b2 o) := by
  change (hypersurfaceSmoothOrientation (scaledSphere L) sphereNormal (scaledSphere_smooth L)
    sphereNormal_continuous (sphere_frame_bijective hL) o).val y = _
  rw [hypersurfaceSmoothOrientation_apply, sphere_frame_equiv hL y]
  rfl

def closedBallBoundaryAmbient {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E3 := by
  let := closedBallChartedSpace hL
  exact fun b => b.val.val

def closedBallBoundaryRadialNormal {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E3 := by
  let := closedBallChartedSpace hL
  exact fun b => L⁻¹ • b.val.val

private theorem boundary_ambient_smooth {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ContMDiff (𝓡 2) (𝓡 3) ∞ (closedBallBoundaryAmbient hL) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact (isSmoothEmbedding_closedBall_inclusion hL).contMDiff.comp
    (boundaryInclusion_contMDiff (I := 𝓡∂ 3) (M := Ball L))
private theorem boundary_normal_continuous {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    Continuous (closedBallBoundaryRadialNormal hL) := by
  let := closedBallChartedSpace hL
  change Continuous (fun b : BoundaryManifold (𝓡∂ 3) (Ball L) => L⁻¹ • b.val.val)
  have hb : Continuous (fun b : BoundaryManifold (𝓡∂ 3) (Ball L) => b.val.val) :=
    (show Continuous (Subtype.val : Ball L → E3) from continuous_subtype_val).comp
      (show Continuous (fun b : BoundaryManifold (𝓡∂ 3) (Ball L) => b.val) from continuous_subtype_val)
  exact hb.const_smul L⁻¹

theorem closedBallBoundaryRadialNormal_outward {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      ‖closedBallBoundaryRadialNormal hL b‖ = 1 ∧
      ∀ s : ℝ, 0 < s → L < ‖closedBallBoundaryAmbient hL b + s • closedBallBoundaryRadialNormal hL b‖ := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  let y := closedBallBoundaryDiffeomorph hL b
  have hn : closedBallBoundaryRadialNormal hL b = y.val := rfl
  have ha : closedBallBoundaryAmbient hL b = L • y.val := by
    change b.val.val = L • (L⁻¹ • b.val.val)
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hy : ‖y.val‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
  refine ⟨hn ▸ hy, ?_⟩
  intro s hs
  rw [ha, hn, ← add_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos hL hs), hy, mul_one]
  linarith

private def boundaryDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E2 →L[ℝ] E3 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => mfderiv (𝓡 2) (𝓡 3) (closedBallBoundaryAmbient hL) b
private def boundaryNormalizationDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E2 ≃L[ℝ] E2 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => (closedBallBoundaryDiffeomorph hL).mfderivToContinuousLinearEquiv (by simp) b

private theorem boundary_derivative_chain {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      boundaryDerivative hL b = (scaledSphereDifferential L (closedBallBoundaryDiffeomorph hL b)).comp
        (boundaryNormalizationDerivative hL b : E2 →L[ℝ] E2) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  have he : scaledSphere L ∘ closedBallBoundaryDiffeomorph hL = closedBallBoundaryAmbient hL := by
    funext x
    change L • (L⁻¹ • x.val.val) = x.val.val
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have h := mfderiv_comp b ((scaledSphere_smooth L).mdifferentiableAt (by simp))
    ((closedBallBoundaryDiffeomorph hL).contMDiff.mdifferentiableAt (by simp))
  rw [he] at h
  exact h

private theorem boundary_frame_eq {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      hypersurfaceNormalFrame (closedBallBoundaryAmbient hL) (closedBallBoundaryRadialNormal hL) b =
        ((((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (boundaryNormalizationDerivative hL b)).trans
          (radialSphereNormalFrame hL (closedBallBoundaryDiffeomorph hL b))) : (ℝ × E2) →L[ℝ] E3) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  apply ContinuousLinearMap.ext
  intro v
  change v.1 • closedBallBoundaryRadialNormal hL b + boundaryDerivative hL b v.2 = _
  rw [boundary_derivative_chain hL b, scaledSphere_derivative]
  exact (radialSphereNormalFrame_apply hL (closedBallBoundaryDiffeomorph hL b) v.1
    (boundaryNormalizationDerivative hL b v.2)).symm

theorem closedBallBoundaryNormalFrame_bijective {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      Bijective (hypersurfaceNormalFrame (closedBallBoundaryAmbient hL) (closedBallBoundaryRadialNormal hL) b) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  rw [boundary_frame_eq hL b]
  exact (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (boundaryNormalizationDerivative hL b)).trans
    (radialSphereNormalFrame hL (closedBallBoundaryDiffeomorph hL b))).bijective

def closedBallBoundarySmoothOrientation {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    SmoothOrientation (𝓡 2) (BoundaryManifold (𝓡∂ 3) (Ball L)) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact hypersurfaceSmoothOrientation (closedBallBoundaryAmbient hL) (closedBallBoundaryRadialNormal hL)
    (boundary_ambient_smooth hL) (boundary_normal_continuous hL) (closedBallBoundaryNormalFrame_bijective hL) o

theorem closedBallBoundarySmoothOrientation_apply {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      (closedBallBoundarySmoothOrientation hL o).val b = Orientation.reindex ℝ E2 i2
        (normalFirstOrientation (hypersurfaceNormalFrameEquiv (closedBallBoundaryAmbient hL)
          (closedBallBoundaryRadialNormal hL) (closedBallBoundaryNormalFrame_bijective hL) b).toLinearEquiv b2 o) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  rfl

private theorem map_reindex (A : E2 ≃ₗ[ℝ] E2) (q : Orientation ℝ E2 (Fin 2)) :
    Orientation.map (Fin (Module.finrank ℝ E2)) A (Orientation.reindex ℝ E2 i2 q) =
      Orientation.reindex ℝ E2 i2 (Orientation.map (Fin 2) A q) := by
  induction q using Module.Ray.ind
  rfl

theorem closedBallBoundarySmoothOrientation_normalization {L : ℝ} (hL : 0 < L)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      tangentOrientationEquiv ((closedBallBoundaryDiffeomorph hL).mfderivToContinuousLinearEquiv (by simp) b).toLinearEquiv
        ((closedBallBoundarySmoothOrientation hL o).val b) =
          (radialSphereSmoothOrientation hL o).val (closedBallBoundaryDiffeomorph hL b) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  have he : (hypersurfaceNormalFrameEquiv (closedBallBoundaryAmbient hL)
      (closedBallBoundaryRadialNormal hL) (closedBallBoundaryNormalFrame_bijective hL) b).toLinearEquiv =
      ((LinearEquiv.refl ℝ ℝ).prodCongr (boundaryNormalizationDerivative hL b).toLinearEquiv).trans
        (radialSphereNormalFrame hL (closedBallBoundaryDiffeomorph hL b)).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun A : (ℝ × E2) →L[ℝ] E3 => A v) (boundary_frame_eq hL b)
  change tangentOrientationEquiv (boundaryNormalizationDerivative hL b).toLinearEquiv
    ((closedBallBoundarySmoothOrientation hL o).val b) = _
  rw [closedBallBoundarySmoothOrientation_apply, radialSphereSmoothOrientation_apply, tangentOrientationEquiv_self,
    map_reindex, he, normalFirstOrientation_change_boundary
      (radialSphereNormalFrame hL (closedBallBoundaryDiffeomorph hL b)).toLinearEquiv
      (boundaryNormalizationDerivative hL b).toLinearEquiv b2 b2 o]
  congr 1
  rw [← Orientation.map_symm, Equiv.apply_symm_apply]
end DifferentialGeometry.Topology.Manifold
