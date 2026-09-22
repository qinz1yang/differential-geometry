import DifferentialGeometry.Topology.PuncturedConnected

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology

namespace DifferentialGeometry.Topology

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [LocallyPathConnectedSpace M]

theorem isPathConnected_compl_image_ball_radius
    (e : OpenPartialHomeomorph E M) (hdim : 1 < Module.rank ℝ E)
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall 0 r ⊆ e.source) :
    IsPathConnected ((e '' Metric.ball 0 r)ᶜ : Set M) := by
  let scale : E ≃ₜ E := Homeomorph.smulOfNeZero r hr.ne'
  let f := scale.toOpenPartialHomeomorph.trans e
  have hfsource : Metric.closedBall (0 : E) 1 ⊆ f.source := by
    intro z hz
    refine ⟨mem_univ _, hball ?_⟩
    change r • z ∈ Metric.closedBall (0 : E) r
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
    have hz' : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz' hr.le
  have himage : f '' Metric.ball (0 : E) 1 = e '' Metric.ball (0 : E) r := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨r • z, ?_, rfl⟩
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
      have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      simpa only [mul_one] using mul_lt_mul_of_pos_left hz' hr
    · rintro ⟨z, hz, rfl⟩
      refine ⟨r⁻¹ • z, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        have hz' : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hz
        calc r⁻¹ * ‖z‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hz' (inv_pos.mpr hr)
             _ = 1 := inv_mul_cancel₀ hr.ne'
      · change e (r • (r⁻¹ • z)) = e z
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [← himage]
  exact isPathConnected_compl_image_ball f hdim hfsource

end DifferentialGeometry.Topology

end
