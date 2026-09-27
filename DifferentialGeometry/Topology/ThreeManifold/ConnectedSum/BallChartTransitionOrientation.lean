import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransitionDet

set_option autoImplicit false
noncomputable section
open Set Metric Manifold Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ClosedOrientedManifold.{u} 3}

namespace OrientedBallChart

theorem det_fderiv_chartTransition_pos (c c' : OrientedBallChart M)
    (hover : c.chart (0 : E3) ∈ c'.chart.target) :
    0 < (fderiv ℝ (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3)).det := by
  have h0 : (0 : E3) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hy0 : c'.chart.symm (c.chart (0 : E3)) ∈ c'.chart.source := c'.chart.map_target hover
  have hchart0 : c'.chart (c'.chart.symm (c.chart (0 : E3))) = c.chart (0 : E3) :=
    c'.chart.right_inv' hover
  let e : E3 ≃L[ℝ] E3 := OrientationAssembly.chartTangentEquiv c h0
  let e' : E3 ≃L[ℝ] E3 := OrientationAssembly.chartTangentEquiv c' hy0
  let A : E3 →L[ℝ] E3 :=
    mfderiv (𝓡 3) (𝓡 3) (fun z : E3 => c'.chart z) (c'.chart.symm (c.chart (0 : E3)))
  let B : E3 →L[ℝ] E3 :=
    mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart.symm y) (c.chart (0 : E3))
  have hA : A = e'.toContinuousLinearMap := rfl
  have heq : (fun y : M.Carrier => c'.chart (c'.chart.symm y))
      =ᶠ[𝓝 (c.chart (0 : E3))] id :=
    Filter.eventuallyEq_of_mem (c'.chart.open_target.mem_nhds hover)
      fun y hy => c'.chart.right_inv' hy
  have hcomp_symm := mfderiv_comp (x := c.chart (0 : E3))
    (f := fun y : M.Carrier => c'.chart.symm y) (g := fun z : E3 => c'.chart z)
    (PartialDiffeomorph.mdifferentiableAt c'.chart (by simp) hy0)
    (PartialDiffeomorph.mdifferentiableAt c'.chart.symm (by simp) hover)
  have hcompv : ∀ v : E3, e' (B v) = v := by
    intro v
    have h1 : ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart (c'.chart.symm y))
        (c.chart (0 : E3)) : E3 →L[ℝ] E3)) v = v := by
      have h := Filter.EventuallyEq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3) heq
      rw [mfderiv_id] at h
      exact congrArg (fun (f : E3 →L[ℝ] E3) => f v) h
    have h2 : ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart (c'.chart.symm y))
        (c.chart (0 : E3)) : E3 →L[ℝ] E3)) v = A (B v) := by
      have hcr : ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart (c'.chart.symm y))
          (c.chart (0 : E3)) : E3 →L[ℝ] E3)) = A.comp B := by
        have h1 : ((mfderiv (𝓡 3) (𝓡 3)
              (fun y : M.Carrier => c'.chart (c'.chart.symm y)) (c.chart (0 : E3))
              : E3 →L[ℝ] E3))
            = ((mfderiv (𝓡 3) (𝓡 3) (fun z : E3 => c'.chart z)
                (c'.chart.symm (c.chart (0 : E3))) : E3 →L[ℝ] E3)).comp B := hcomp_symm
        rw [h1, hA]
        rfl
      rw [hcr]
      rfl
    have h3 : A (B v) = v := h2 ▸ h1
    rw [hA] at h3
    exact h3
  have hBv : ∀ w : E3, B w = e'.symm w := fun w => by
    rw [← e'.symm_apply_apply (B w), hcompv w]
  have hchain := mfderiv_comp (x := (0 : E3)) (f := fun x : E3 => c.chart x)
    (g := fun y : M.Carrier => c'.chart.symm y)
    (PartialDiffeomorph.mdifferentiableAt c'.chart.symm (by simp) hover)
    (PartialDiffeomorph.mdifferentiableAt c.chart (by simp) h0)
  have hmain : ((fderiv ℝ (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3)
      : E3 →L[ℝ] E3))
      = ((e.trans e'.symm : E3 ≃L[ℝ] E3)).toContinuousLinearMap := by
    rw [← mfderiv_eq_fderiv]
    have hcr : ((mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3)
          : E3 →L[ℝ] E3)) = B.comp e.toContinuousLinearMap := by
      have h1 : ((mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3)
            : E3 →L[ℝ] E3))
          = ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart.symm y)
              (c.chart (0 : E3)) : E3 →L[ℝ] E3)).comp
            ((mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c.chart x) (0 : E3)
              : E3 →L[ℝ] E3)) := hchain
      rw [h1, show ((mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c.chart x) (0 : E3)
          : E3 →L[ℝ] E3)) = e.toContinuousLinearMap from rfl]
      rfl
    rw [hcr]
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, hBv]
    rfl
  rw [hmain]
  have hstep : (Orientation.map (Fin 3) e.toLinearEquiv)
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)
      = M.orientation.orientation (c.chart (0 : E3)) := c.preserves_orientation 0 h0
  have hstep' : (Orientation.map (Fin 3) (e'.toLinearEquiv).symm)
      (M.orientation.orientation (c'.chart (c'.chart.symm (c.chart (0 : E3)))))
      = (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation :=
    OrientationAssembly.orientation_map_chartTangentEquiv_symm c' hy0
  have hT : Orientation.map (Fin 3)
      ((e.toLinearEquiv).trans (e'.toLinearEquiv).symm)
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation := by
    rw [← _root_.OrientationAssembly.orientation_map_map_trans e.toLinearEquiv
      (e'.toLinearEquiv).symm ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)]
    rw [hstep, ← hchart0]
    exact hstep'
  exact (Orientation.map_eq_iff_det_pos
    ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)
    ((e.trans e'.symm : E3 ≃L[ℝ] E3)).toLinearEquiv
    (by simp : Fintype.card (Fin 3) = Module.finrank ℝ E3)).mp hT

theorem det_fderiv_chartTransition_self (c : OrientedBallChart M) :
    (fderiv ℝ (fun x : E3 => c.chart.symm (c.chart x)) (0 : E3)).det = 1 := by
  have h0 : (0 : E3) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have heq : (fun x : E3 => c.chart.symm (c.chart x)) =ᶠ[𝓝 (0 : E3)] id :=
    Filter.eventuallyEq_of_mem (c.chart.open_source.mem_nhds h0)
      fun x hx => c.chart.left_inv hx
  rw [heq.fderiv_eq, fderiv_id]
  rw [show ContinuousLinearMap.det (ContinuousLinearMap.id ℝ E3)
    = LinearMap.det (1 : E3 →ₗ[ℝ] E3) from rfl]
  exact map_one _

end OrientedBallChart

end DifferentialGeometry.Topology
