import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws

set_option autoImplicit false
noncomputable section
open Set Metric Manifold Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ClosedOrientedManifold.{u} 3}

theorem det_fderiv_chartTransition_pos (c c' : OrientedBallChart M)
    (hc : c.chart (0 : E3) = c'.chart (0 : E3)) :
    0 < (fderiv ℝ (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3)).det := by
  have h0 : (0 : E3) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have h0' : (0 : E3) ∈ c'.chart.source :=
    c'.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hp' : c'.chart (0 : E3) ∈ c'.chart.target := c'.chart.map_source h0'
  have hsymm0 : c'.chart.symm (c'.chart (0 : E3)) = (0 : E3) := c'.chart.left_inv h0'
  have hmem1 : c'.chart.symm (c'.chart (0 : E3)) ∈ c'.chart.source := by
    rw [hsymm0]; exact h0'
  have heq : (fun y : M.Carrier => c'.chart (c'.chart.symm y))
      =ᶠ[𝓝 (c'.chart (0 : E3))] id :=
    Filter.eventuallyEq_of_mem (c'.chart.open_target.mem_nhds hp')
      fun y hy => c'.chart.right_inv' hy
  let e : E3 ≃L[ℝ] E3 := OrientationAssembly.chartTangentEquiv c h0
  let e' : E3 ≃L[ℝ] E3 := OrientationAssembly.chartTangentEquiv c' h0'
  let A : E3 →L[ℝ] E3 := mfderiv (𝓡 3) (𝓡 3) (fun z : E3 => c'.chart z) (0 : E3)
  let B : E3 →L[ℝ] E3 :=
    mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart.symm y) (c'.chart (0 : E3))
  have hA : A = e'.toContinuousLinearMap := rfl
  have hAq : ((mfderiv (𝓡 3) (𝓡 3) (fun z : E3 => c'.chart z)
        (c'.chart.symm (c'.chart (0 : E3))) : E3 →L[ℝ] E3)) = e'.toContinuousLinearMap :=
    hsymm0.symm ▸ (rfl : ((mfderiv (𝓡 3) (𝓡 3) (fun z : E3 => c'.chart z) (0 : E3)
      : E3 →L[ℝ] E3)) = e'.toContinuousLinearMap)
  have hcomp_symm := mfderiv_comp (x := c'.chart (0 : E3))
    (f := fun y : M.Carrier => c'.chart.symm y) (g := fun z : E3 => c'.chart z)
    (PartialDiffeomorph.mdifferentiableAt c'.chart (by simp) hmem1)
    (PartialDiffeomorph.mdifferentiableAt c'.chart.symm (by simp) hp')
  have hcompv : ∀ v : E3, e' (B v) = v := by
    intro v
    have h1 : ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart (c'.chart.symm y))
        (c'.chart (0 : E3)) : E3 →L[ℝ] E3)) v = v := by
      have h := Filter.EventuallyEq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3) heq
      rw [mfderiv_id] at h
      exact congrArg (fun (f : E3 →L[ℝ] E3) => f v) h
    have h2 : ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart (c'.chart.symm y))
        (c'.chart (0 : E3)) : E3 →L[ℝ] E3)) v = A (B v) := by
      have hcr : ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart (c'.chart.symm y))
          (c'.chart (0 : E3)) : E3 →L[ℝ] E3)) = A.comp B := by
        have h1 : ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart (c'.chart.symm y))
            (c'.chart (0 : E3)) : E3 →L[ℝ] E3))
            = ((mfderiv (𝓡 3) (𝓡 3) (fun z : E3 => c'.chart z)
                (c'.chart.symm (c'.chart (0 : E3))) : E3 →L[ℝ] E3)).comp B := hcomp_symm
        rw [h1, hAq, hA]
        rfl
      rw [hcr]
      rfl
    have h3 : A (B v) = v := h2 ▸ h1
    rw [hA] at h3
    exact h3
  have hBv : ∀ w : E3, B w = e'.symm w := fun w => by
    rw [← e'.symm_apply_apply (B w), hcompv w]
  have hmem2 : c.chart (0 : E3) ∈ c'.chart.target := by rw [hc]; exact hp'
  have hchain := mfderiv_comp (x := (0 : E3)) (f := fun x : E3 => c.chart x)
    (g := fun y : M.Carrier => c'.chart.symm y)
    (PartialDiffeomorph.mdifferentiableAt c'.chart.symm (by simp) hmem2)
    (PartialDiffeomorph.mdifferentiableAt c.chart (by simp) h0)
  have hmain : ((fderiv ℝ (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3)
      : E3 →L[ℝ] E3))
      = ((OrientationAssembly.chartTangentEquiv c h0).trans
          (OrientationAssembly.chartTangentEquiv c' h0').symm : E3 ≃L[ℝ] E3).toContinuousLinearMap := by
    have hc' : ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart.symm y)
          (c.chart (0 : E3)) : E3 →L[ℝ] E3)) = B :=
      hc.symm ▸ (rfl : ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart.symm y)
        (c'.chart (0 : E3)) : E3 →L[ℝ] E3)) = B)
    have hcr : ((mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3)
          : E3 →L[ℝ] E3))
        = B.comp e.toContinuousLinearMap := by
      have h1 : ((mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3)
            : E3 →L[ℝ] E3))
          = ((mfderiv (𝓡 3) (𝓡 3) (fun y : M.Carrier => c'.chart.symm y)
              (c.chart (0 : E3)) : E3 →L[ℝ] E3)).comp
            ((mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c.chart x) (0 : E3) : E3 →L[ℝ] E3)) :=
        hchain
      rw [h1, hc']
      congr 1
    rw [mfderiv_eq_fderiv] at hcr
    have hfd : fderiv ℝ (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3) =
        B.comp e.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro v
      have hv := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ)
        (c'.chart.symm (c.chart (0 : E3)))
          (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : E3)).symm v))) hcr
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply] using! hv
    rw [hfd]
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, hBv]
    rfl
  rw [hmain]
  have hcomp_orient := orientation_map_trans (OrientationAssembly.chartTangentEquiv c h0).toLinearEquiv
    (OrientationAssembly.chartTangentEquiv c' h0').toLinearEquiv.symm
    (_root_.OrientationAssembly.stdOrientation (0 : E3))
  have hT : Orientation.map (Fin 3)
      (((OrientationAssembly.chartTangentEquiv c h0).toLinearEquiv.trans
        (OrientationAssembly.chartTangentEquiv c' h0').toLinearEquiv.symm : E3 ≃ₗ[ℝ] E3))
      (_root_.OrientationAssembly.stdOrientation (0 : E3))
      = _root_.OrientationAssembly.stdOrientation (0 : E3) := by
    erw [hcomp_orient]
    erw [← _root_.OrientationAssembly.orientation_eq_map_chartTangentEquiv c h0, hc,
      _root_.OrientationAssembly.orientation_eq_map_chartTangentEquiv c' h0']
    exact orientation_map_symm_map (OrientationAssembly.chartTangentEquiv c' h0').toLinearEquiv
      (_root_.OrientationAssembly.stdOrientation (0 : E3))
  exact (Orientation.map_eq_iff_det_pos (_root_.OrientationAssembly.stdOrientation (0 : E3))
    ((OrientationAssembly.chartTangentEquiv c h0).toLinearEquiv.trans
      (OrientationAssembly.chartTangentEquiv c' h0').toLinearEquiv.symm : E3 ≃ₗ[ℝ] E3)
    (by simp : Fintype.card (Fin 3) = Module.finrank ℝ E3)).mp hT

end DifferentialGeometry.Topology
