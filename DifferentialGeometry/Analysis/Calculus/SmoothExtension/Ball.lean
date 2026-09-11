import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct



noncomputable section

open Set
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis




theorem exists_contDiff_compactSupport_eq_near_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball (0 : E) R)) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∀ z ∈ Metric.closedBall (0 : E) r, F =ᶠ[𝓝 z] f := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  obtain ⟨t, hst, htR⟩ := exists_between hsR
  let b : ContDiffBump (0 : E) := ⟨s, t, hr.trans_lt hrs, hst⟩
  let F : E → ℝ := fun z => b z * f z
  have hF : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport b
    · have hzR : z ∈ Metric.ball (0 : E) R := by
        rw [b.tsupport_eq] at hz
        exact Metric.closedBall_subset_ball htR hz
      exact b.contDiffAt.mul ((hf z hzR).contDiffAt (Metric.isOpen_ball.mem_nhds hzR))
    · have heq : F =ᶠ[𝓝 z] (0 : E → ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with q hq
        simp [F, hq]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  refine ⟨F, hF, b.hasCompactSupport.mul_right, ?_⟩
  intro z hz
  have hzs : z ∈ Metric.ball (0 : E) s := Metric.closedBall_subset_ball hrs hz
  filter_upwards [b.eventuallyEq_one_of_mem_ball hzs] with q hq
  simp [F, hq]




theorem exists_contDiff_nonneg_compactSupport_eq_near_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball (0 : E) R))
    (hn : ∀ z ∈ Metric.ball (0 : E) R, 0 ≤ f z) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ (∀ z, 0 ≤ F z) ∧
      ∀ z ∈ Metric.closedBall (0 : E) r, F =ᶠ[𝓝 z] f := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  obtain ⟨t, hrt, hts⟩ := exists_between hrs
  obtain ⟨G, hG, _, heq⟩ :=
    exists_contDiff_compactSupport_eq_near_closedBall (hr.trans hrs.le) hsR hf
  let b : ContDiffBump (0 : E) := ⟨t, s, hr.trans_lt hrt, hts⟩
  refine ⟨fun z => b z * G z, b.contDiff.mul hG, b.hasCompactSupport.mul_right, ?_, ?_⟩
  · intro z
    change 0 ≤ b z * G z
    by_cases hz : z ∈ Metric.closedBall (0 : E) s
    · rw [(heq z hz).eq_of_nhds]
      exact mul_nonneg b.nonneg (hn z (Metric.closedBall_subset_ball hsR hz))
    · have hz' : z ∉ tsupport b := by simpa only [b.tsupport_eq] using hz
      rw [image_eq_zero_of_notMem_tsupport hz', zero_mul]
  · intro z hz
    have hzt : z ∈ Metric.ball (0 : E) t := Metric.closedBall_subset_ball hrt hz
    filter_upwards [b.eventuallyEq_one_of_mem_ball hzt,
      heq z (Metric.closedBall_subset_closedBall hrs.le hz)] with q hbq hGq
    simp only [hbq, hGq, Pi.one_apply, one_mul]

end DifferentialGeometry.Analysis
