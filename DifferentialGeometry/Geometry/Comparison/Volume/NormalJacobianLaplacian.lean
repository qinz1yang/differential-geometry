import DifferentialGeometry.Geometry.Comparison.Volume.NormalJacobian
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.Smoothness
import DifferentialGeometry.Geometry.Connection.Hessian.Scalar
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open NormalCoordinates
open Exponential
open Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

private theorem normalChart_ball_preimage_isOpen
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) :=
  (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
    (normalChartAt g p).open_source Metric.isOpen_ball

private theorem normalChart_ball_preimage_mem
    (g : SmoothRiemannianMetric I M) (p : M) :
    p ∈ (normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p) := by
  refine ⟨normalChartAt_source g p, ?_⟩
  change normalChartAt g p p ∈ Metric.ball (0 : E) (expMapC2Radius g p)
  rw [normalChartAt_centre]
  exact Metric.mem_ball_self (expMapC2Radius_pos g p)

theorem contMDiffOn_normalJacobian_inv_sqrt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun q => (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹)
      ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) := by
  intro q hq
  have hqball : normalChartAt g p q ∈ Metric.ball (0 : E) (expMapC2Radius g p) := hq.2
  have heq : expMap g p (show TangentSpace I p from normalChartAt g p q) = q := by
    rw [← normalChartAt_symm_apply g p ((normalChartAt g p).map_source hq.1)]
    exact (normalChartAt g p).left_inv hq.1
  have hc := normal_chart_at_cont_mdiff_at_infty g p
    (show ‖normalChartAt g p q‖ < expMapC2Radius g p by simpa using hqball)
  rw [heq] at hc
  have hj := (contDiffOn_normalJacobian_inv_sqrt g p).contDiffAt
    (Metric.isOpen_ball.mem_nhds hqball)
  exact (hj.contMDiffAt.comp q hc).contMDiffWithinAt

theorem contMDiffAt_normalJacobian_inv_sqrt_centre
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q => (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹) p :=
  (contMDiffOn_normalJacobian_inv_sqrt g p).contMDiffAt
    ((normalChart_ball_preimage_isOpen g p).mem_nhds (normalChart_ball_preimage_mem g p))

variable [T2Space M]

private theorem normalJacobian_inv_sqrt_hessian_diagonal
    (g : SmoothRiemannianMetric I M) (p : M) (x : TangentSpace I p) :
    abstractHessian g (fun q => (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹)
      p x x = (1 / 6 : ℝ) * Curvature.ricciTensor g p x x := by
  let f : M → ℝ := fun q => (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹
  let γ := radialCurve g p (x : E)
  have hp : γ 0 = p := radialCurve_zero g p x
  have hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f (γ 0) := by
    rw [hp]
    exact (contMDiffAt_normalJacobian_inv_sqrt_centre g p).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ 0 :=
    radialCurve_contMDiffAt2 g p x 0
      (by
        change ‖(0 : ℝ) • (x : E)‖ < expMapC2Radius g p
        rw [zero_smul, norm_zero]
        exact expMapC2Radius_pos g p)
  have hgeo : Geodesic.HasGeodesicEquationAt g γ 0 := exp_radial_geo_zero g p x
  have h := abstractHessian_apply_velocity_of_hasGeodesicEquationAt g hf hγ
    (BoundarylessManifold.isInteriorPoint (I := I)) hgeo
  dsimp only at h
  have hv : mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) =
      (x : E) := radialCurve_launch_velocity g p x
  rw [hv] at h
  have hbase : abstractHessian g f (γ 0) (x : E) (x : E) = abstractHessian g f p x x :=
    congrArg (fun q : M => abstractHessian g f q (x : E) (x : E)) hp
  have heq : (f ∘ γ) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (Real.sqrt (normalJacobian g p (t • (x : E))))⁻¹) := by
    filter_upwards [radialChartCurve_eventuallyEq g p (x : E)] with t ht
    exact congrArg (fun v : E => (Real.sqrt (normalJacobian g p v))⁻¹) ht
  exact hbase.symm.trans (h.trans ((heq.iteratedDeriv_eq 2).trans
    (second_derivative_normalJacobian_inv_sqrt_radial_zero g p x)))

theorem abstractHessian_normalJacobian_inv_sqrt_centre
    (g : SmoothRiemannianMetric I M) (p : M) :
    abstractHessian g (fun q => (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹) p =
      (1 / 6 : ℝ) • Curvature.ricciTensor g p := by
  let f : M → ℝ := fun q => (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹
  have hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f p :=
    (contMDiffAt_normalJacobian_inv_sqrt_centre g p).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  ext x y
  have hx := normalJacobian_inv_sqrt_hessian_diagonal g p x
  have hy := normalJacobian_inv_sqrt_hessian_diagonal g p y
  have hxy := normalJacobian_inv_sqrt_hessian_diagonal g p (x + y)
  have hs := abstractHessian_symm g hf x y
  have hr := Curvature.ricciTensor_symm g p x y
  simp only [map_add, add_apply] at hxy
  change abstractHessian g f p x y = (1 / 6 : ℝ) * Curvature.ricciTensor g p x y
  change abstractHessian g f p x x = _ at hx
  change abstractHessian g f p y y = _ at hy
  change abstractHessian g f p x x + abstractHessian g f p y x +
    (abstractHessian g f p x y + abstractHessian g f p y y) = _ at hxy
  linarith

theorem laplacian_normalJacobian_inv_sqrt_centre
    (g : SmoothRiemannianMetric I M) (p : M) :
    Operator.laplacian (LeviCivita g) g
      (fun q => (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹) p =
      (1 / 6 : ℝ) * Curvature.metricScalarAt g p := by
  classical
  obtain ⟨F, hF, hFf⟩ := exists_smooth_germ
    (normalChart_ball_preimage_isOpen g p) (normalChart_ball_preimage_mem g p)
    (contMDiffOn_normalJacobian_inv_sqrt g p)
  have hLap := Operator.laplacian_congr_of_eventuallyEq (LeviCivita g) g
    hF.contMDiffAt (contMDiffAt_normalJacobian_inv_sqrt_centre g p) hFf
  have hHess : abstractHessian g F p = (1 / 6 : ℝ) • Curvature.ricciTensor g p :=
    (abstractHessian_congr_of_eventuallyEq g hFf).trans
      (abstractHessian_normalJacobian_inv_sqrt_centre g p)
  let B := fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame g p i p
  have hB : ∀ i j, g.inner p (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    let : NeZero (Module.finrank ℝ E) :=
      ⟨(lt_of_le_of_lt (Nat.zero_le i.val) i.isLt).ne'⟩
    exact smoothOrthoFrame_orthonormal_at_center g p i j
  have htrace := Curvature.sum_abstractHessian_orthonormal_eq_laplacian g hF p B hB
  rw [hHess] at htrace
  have hscalar := (Curvature.orthonormal_basis_bilin_trace g p
    (Curvature.ricciTensor g p) B hB).trans (Curvature.metric_scalar_at_eq_chart_ricci_sum g p).symm
  rw [← hLap, Operator.laplacian_levi_eq g hF p, ← htrace]
  simp only [smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, hscalar]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
