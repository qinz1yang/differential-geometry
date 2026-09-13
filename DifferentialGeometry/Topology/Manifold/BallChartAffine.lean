import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedChartPullback

set_option autoImplicit false
noncomputable section
open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

namespace AffineModel

def affineDiffeomorph (s : E3) (r : ℝ) (hr : r ≠ 0) :
    Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ where
  toEquiv :=
    { toFun := fun x => s + r • x
      invFun := fun y => r⁻¹ • (y - s)
      left_inv := fun x => by
        change r⁻¹ • (s + r • x - s) = x
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
      right_inv := fun y => by
        change s + r • (r⁻¹ • (y - s)) = y
        rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
        abel }
  contMDiff_toFun := (contDiff_const.contMDiff.add (contDiff_const_smul r).contMDiff)
  contMDiff_invFun := (contDiff_const_smul r⁻¹).contMDiff.comp
    (contMDiff_id.sub contMDiff_const)

theorem mfderiv_affineDiffeomorph (s : E3) (r : ℝ) (x v : E3) :
    mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => s + r • y) x v = r • v := by
  have h1 : HasMFDerivAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (fun y : E3 => s + r • y) x
      (ContinuousLinearMap.lsmul ℝ ℝ r : E3 →L[ℝ] E3) :=
    (((ContinuousLinearMap.lsmul ℝ ℝ r : E3 →L[ℝ] E3).hasFDerivAt).const_add s).hasMFDerivAt
  rw [h1.mfderiv]
  exact ContinuousLinearMap.lsmul_apply ℝ ℝ r v

end AffineModel

namespace BallChart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

def affine (c : BallChart 3 (𝓡 3) M) (s : E3) (r : ℝ) (hr : 0 < r)
    (hs : ‖s‖ + 2 * r ≤ 2) : BallChart 3 (𝓡 3) M where
  chart :=
    (AffineModel.affineDiffeomorph s r (ne_of_gt hr)).toPartialDiffeomorph.trans c.chart
  closedBall_subset_source := by
    intro x hx
    change x ∈ (((AffineModel.affineDiffeomorph s r (ne_of_gt hr)).toPartialDiffeomorph
      ).toOpenPartialHomeomorph.trans c.chart.toOpenPartialHomeomorph).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨Set.mem_univ _, ?_⟩
    refine c.closedBall_subset_source ?_
    change dist (s + r • x) 0 ≤ 2
    rw [dist_eq_norm, sub_zero]
    have hx2 : ‖x‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    calc ‖s + r • x‖ ≤ ‖s‖ + ‖r • x‖ := norm_add_le _ _
      _ = ‖s‖ + r * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ ‖s‖ + 2 * r := by
        have : r * ‖x‖ ≤ r * 2 := mul_le_mul_of_nonneg_left hx2 hr.le
        linarith
      _ ≤ 2 := hs

omit [IsManifold (𝓡 3) ∞ M] in
theorem affine_apply (c : BallChart 3 (𝓡 3) M) (s : E3) (r : ℝ) (hr : 0 < r)
    (hs : ‖s‖ + 2 * r ≤ 2) (x : E3) :
    (c.affine s r hr hs).chart x = c.chart (s + r • x) := rfl

omit [IsManifold (𝓡 3) ∞ M] in
theorem affine_source_subset (c : BallChart 3 (𝓡 3) M) (s : E3) (r : ℝ) (hr : 0 < r)
    (hs : ‖s‖ + 2 * r ≤ 2) {x : E3} (hx : x ∈ (c.affine s r hr hs).chart.source) :
    s + r • x ∈ c.chart.source := by
  have hx' := hx
  change x ∈ (((AffineModel.affineDiffeomorph s r (ne_of_gt hr)).toPartialDiffeomorph
    ).toOpenPartialHomeomorph.trans c.chart.toOpenPartialHomeomorph).source at hx'
  rw [OpenPartialHomeomorph.trans_source] at hx'
  exact hx'.2

end BallChart

namespace OrientationAssembly

theorem orientation_map_smulOfNeZero_tangent {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] (y : M) (r : ℝ) (hr : 0 < r)
    (o : Orientation ℝ (TangentSpace (𝓡 3) y) (Fin 3)) :
    Orientation.map (Fin 3)
      (LinearEquiv.smulOfNeZero ℝ (TangentSpace (𝓡 3) y) r (ne_of_gt hr)) o = o := by
  rw [Orientation.map_eq_iff_det_pos o _ (by
    change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    rw [finrank_euclideanSpace])]
  have hlm : ((LinearEquiv.smulOfNeZero ℝ (TangentSpace (𝓡 3) y) r (ne_of_gt hr) :
      TangentSpace (𝓡 3) y ≃ₗ[ℝ] TangentSpace (𝓡 3) y) : _ →ₗ[ℝ] _)
      = r • (LinearMap.id : TangentSpace (𝓡 3) y →ₗ[ℝ] TangentSpace (𝓡 3) y) := by
    ext v
    simp [LinearEquiv.smulOfNeZero_apply]
  rw [hlm, LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact pow_pos hr _

end OrientationAssembly

set_option backward.isDefEq.respectTransparency false in
theorem affine_chart_mfderiv_apply {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    (c : BallChart 3 (𝓡 3) M) (s : E3) (r : ℝ) (hr : 0 < r) {x v : E3}
    (hxc : s + r • x ∈ c.chart.source) :
    mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => c.chart (s + r • y)) x v
      = r • mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => c.chart y) (s + r • x) v := by
  have hcomp : mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => c.chart (s + r • y)) x
      = mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => c.chart y) (s + r • x)
        ∘L mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => s + r • y) x :=
    mfderiv_comp (x := x) (f := fun y : E3 => s + r • y)
      (g := fun y : E3 => c.chart y)
      (PartialDiffeomorph.mdifferentiableAt c.chart (by simp) hxc)
      ((AffineModel.affineDiffeomorph s r (ne_of_gt hr)).mdifferentiable (by simp) x)
  have hv := DFunLike.congr_fun hcomp v
  erw [ContinuousLinearMap.comp_apply, AffineModel.mfderiv_affineDiffeomorph] at hv
  rw [map_smul] at hv
  exact hv

namespace OrientedBallChart

variable {M : ClosedOrientedManifold.{u} 3}

def affine (c : OrientedBallChart M) (s : E3) (r : ℝ) (hr : 0 < r)
    (hs : ‖s‖ + 2 * r ≤ 2) : OrientedBallChart M where
  toBallChart := c.toBallChart.affine s r hr hs
  preserves_orientation := by
    intro x hx
    have hxc : s + r • x ∈ c.toBallChart.chart.source :=
      BallChart.affine_source_subset c.toBallChart s r hr hs hx
    have hchain :
        (OrientationAssembly.ballChartTangentEquiv (c.toBallChart.affine s r hr hs) hx
            ).toLinearEquiv
          = (OrientationAssembly.ballChartTangentEquiv c.toBallChart hxc).toLinearEquiv.trans
            (LinearEquiv.smulOfNeZero ℝ
              (TangentSpace (𝓡 3) (c.toBallChart.chart (s + r • x))) r (ne_of_gt hr)) := by
      refine LinearEquiv.ext fun v => ?_
      erw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply]
      exact affine_chart_mfderiv_apply c.toBallChart s r hr hxc (v := v)
    change Orientation.map (Fin 3) (OrientationAssembly.ballChartTangentEquiv
        (c.toBallChart.affine s r hr hs) hx).toLinearEquiv
        (OrientationAssembly.stdOrientation x)
      = M.orientation.orientation ((c.toBallChart.affine s r hr hs).chart x)
    rw [hchain]
    erw [← OrientationAssembly.orientation_map_map_trans
      (OrientationAssembly.ballChartTangentEquiv c.toBallChart hxc).toLinearEquiv
      (LinearEquiv.smulOfNeZero ℝ
        (TangentSpace (𝓡 3) (c.toBallChart.chart (s + r • x))) r (ne_of_gt hr))
      (OrientationAssembly.stdOrientation x)]
    rw [show OrientationAssembly.stdOrientation x = OrientationAssembly.stdOrientation (s + r • x)
      from OrientationAssembly.stdOrientation_eq x (s + r • x)]
    erw [c.preserves_orientation (s + r • x) hxc]
    exact OrientationAssembly.orientation_map_smulOfNeZero_tangent _ r hr _

@[simp]
theorem affine_apply (c : OrientedBallChart M) (s : E3) (r : ℝ) (hr : 0 < r)
    (hs : ‖s‖ + 2 * r ≤ 2) (x : E3) :
    (c.affine s r hr hs).chart x = c.chart (s + r • x) := rfl

end OrientedBallChart

theorem exists_disjointOrientedBallChart {M : ClosedOrientedManifold.{u} 3}
    (c : OrientedBallChart M) :
    ∃ d δ : OrientedBallChart M,
      (∀ x ∈ Metric.closedBall (0 : E3) 2, ∀ y ∈ Metric.ball (0 : E3) 1,
        d.chart x ≠ δ.chart y) ∧
      (∀ x ∈ Metric.closedBall (0 : E3) 2, ∀ y ∈ Metric.ball (0 : E3) 1,
        δ.chart x ≠ d.chart y) := by
  classical
  have hnorm : ‖((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3)‖ = 3 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hs : ‖((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3)‖ + 2 * (1 / 8) ≤ 2 := by
    rw [hnorm]; norm_num
  have h0 : ‖(0 : E3)‖ + 2 * (1 / 8) ≤ 2 := by norm_num
  have hsc : ∀ u : E3, ‖(1 / 8 : ℝ) • u‖ = 1 / 8 * ‖u‖ := by
    intro u
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
  have hfar : ∀ u : E3, ‖u‖ ≤ 2 →
      ‖((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3) + (1 / 8 : ℝ) • u‖ ≤ 2 := by
    intro u hu
    calc ‖((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3) + (1 / 8 : ℝ) • u‖
        ≤ ‖((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3)‖ + ‖(1 / 8 : ℝ) • u‖ :=
          norm_add_le _ _
      _ = 3 / 2 + 1 / 8 * ‖u‖ := by rw [hnorm, hsc]
      _ ≤ 2 := by nlinarith
  have hnear : ∀ u : E3, ‖u‖ ≤ 2 → ‖(1 / 8 : ℝ) • u‖ ≤ 2 := by
    intro u hu
    rw [hsc]
    nlinarith
  refine ⟨c.affine _ (1 / 8) (by norm_num) hs, c.affine 0 (1 / 8) (by norm_num) h0,
    ?_, ?_⟩
  · intro x hx y hy heq
    have hx2 : ‖x‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hy1 : ‖y‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hy
    have h1 : ((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3) + (1 / 8 : ℝ) • x
        ∈ c.toBallChart.chart.source :=
      c.toBallChart.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hfar x hx2)
    have h2 : (1 / 8 : ℝ) • y ∈ c.toBallChart.chart.source :=
      c.toBallChart.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hnear y (by linarith))
    have hinj : ((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3) + (1 / 8 : ℝ) • x
        = (1 / 8 : ℝ) • y :=
      c.toBallChart.chart.toPartialEquiv.injOn h1 h2 (by simpa using heq)
    have hdiff : ((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3)
        = (1 / 8 : ℝ) • (y - x) := by
      rw [smul_sub, ← hinj]
      abel
    have hb : ‖((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3)‖ < 3 / 8 := by
      rw [hdiff, hsc]
      have hsub : ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      nlinarith
    rw [hnorm] at hb
    norm_num at hb
  · intro x hx y hy heq
    have hx2 : ‖x‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hy1 : ‖y‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hy
    have h1 : (1 / 8 : ℝ) • x ∈ c.toBallChart.chart.source :=
      c.toBallChart.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hnear x hx2)
    have h2 : ((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3) + (1 / 8 : ℝ) • y
        ∈ c.toBallChart.chart.source :=
      c.toBallChart.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hfar y (by linarith))
    have hinj : (1 / 8 : ℝ) • x
        = ((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3) + (1 / 8 : ℝ) • y :=
      c.toBallChart.chart.toPartialEquiv.injOn h1 h2 (by simpa using heq)
    have hdiff : ((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3)
        = (1 / 8 : ℝ) • (x - y) := by
      rw [smul_sub, hinj]
      abel
    have hb : ‖((3 / 2 : ℝ) • EuclideanSpace.single 0 1 : E3)‖ < 3 / 8 := by
      rw [hdiff, hsc]
      have hsub : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      nlinarith
    rw [hnorm] at hb
    norm_num at hb

end DifferentialGeometry.Topology
