import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.WeakGaugeCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Topology.Piecewise

set_option autoImplicit false
noncomputable section

open Set Filter Asymptotics
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem hasFDerivAt_indicator_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Set E) {f : E → F} {x : E} (hf : HasFDerivAt f (0 : E →L[ℝ] F) x) (hx : f x = 0) :
    HasFDerivAt (s.indicator f) (0 : E →L[ℝ] F) x := by
  classical
  have hzero : s.indicator f x = 0 := by
    by_cases hxs : x ∈ s <;> simp [hxs, hx]
  have hsmall : f =o[𝓝 x] (fun y => y - x) := by
    simpa only [hx, zero_apply, sub_zero] using hf.isLittleO
  apply HasFDerivAt.of_isLittleO
  simpa only [hzero, zero_apply, sub_zero] using
    (Asymptotics.isBigO_of_le (𝓝 x)
      (fun y => norm_indicator_le_norm_self (s := s) f y)).trans_isLittleO hsmall

private theorem hasFDerivAt_indicator_of_frontier_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U s : Set E} (hU : IsOpen U) (hs : IsOpen s)
    {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    (hzero : ∀ z ∈ U ∩ frontier s, f z = 0 ∧ fderiv ℝ f z = 0)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (s.indicator f) (s.indicator (fderiv ℝ f) x) x := by
  classical
  by_cases hxs : x ∈ s
  · have heq : s.indicator f =ᶠ[𝓝 x] f := by
      filter_upwards [hs.mem_nhds hxs] with y hy
      exact indicator_of_mem hy f
    rw [indicator_of_mem hxs]
    exact ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.congr_of_eventuallyEq heq
  · rw [indicator_of_notMem hxs]
    by_cases hxb : x ∈ frontier s
    · obtain ⟨hf0, hd0⟩ := hzero x ⟨hx, hxb⟩
      apply hasFDerivAt_indicator_zero s _ hf0
      simpa only [hd0] using
        ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    · have hxc : x ∉ closure s := by
        intro hxc
        apply hxb
        rw [frontier, hs.interior_eq]
        exact ⟨hxc, hxs⟩
      have heq : s.indicator f =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
        exact indicator_of_notMem (fun hys => hy (subset_closure hys)) f
      exact (hasFDerivAt_const (𝕜 := ℝ) (0 : F) x).congr_of_eventuallyEq heq

/-- A section with zero value and first derivative on an arbitrary open side's
frontier extends by zero as a `C¹` section. This statement does not identify the
side with a half-plane or extend any differential equation to the other side. -/
theorem contDiffOn_indicator_of_frontier_firstJet_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U s : Set E} (hU : IsOpen U) (hs : IsOpen s)
    {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    (hzero : ∀ z ∈ U ∩ frontier s, f z = 0 ∧ fderiv ℝ f z = 0) :
    ContDiffOn ℝ 1 (s.indicator f) U ∧
      ∀ z ∈ U, fderiv ℝ (s.indicator f) z = s.indicator (fderiv ℝ f) z := by
  classical
  have hd (z : E) (hz : z ∈ U) :=
    hasFDerivAt_indicator_of_frontier_zero hU hs hf hzero hz
  have hc : ContinuousOn (s.indicator (fderiv ℝ f)) U := by
    change ContinuousOn (s.piecewise (fderiv ℝ f) (fun _ => 0)) U
    apply ContinuousOn.piecewise
    · intro z hz
      exact (hzero z hz).2
    · exact (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono inter_subset_left
    · exact continuousOn_const
  have hdc : ContinuousOn (fderiv ℝ (s.indicator f)) U := by
    apply hc.congr
    intro z hz
    exact (hd z hz).fderiv
  refine ⟨?_, fun z hz => (hd z hz).fderiv⟩
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨fun z hz => (hd z hz).differentiableAt.differentiableWithinAt,
    by simp, by simpa only [contDiffOn_zero] using hdc⟩

/-- The literal zero extension preserves a first-order differential inequality
from the actual open side. Its complementary side has zero derivative by the
proved `C¹` gluing; no PDE is assumed there. The side may have a curved seam. -/
theorem complexDbar_indicator_of_frontier_firstJet_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {U s : Set ℂ} (hU : IsOpen U) (hs : IsOpen s)
    {ξ : ℂ → V} (hξ : ContDiffOn ℝ 1 ξ U)
    (hzero : ∀ z ∈ U ∩ frontier s, ξ z = 0 ∧ fderiv ℝ ξ z = 0)
    {C : ℝ} (hbound : ∀ z ∈ U ∩ s, ‖complexDbar ξ z‖ ≤ C * ‖ξ z‖) :
    ContDiffOn ℝ 1 (s.indicator ξ) U ∧
      (∀ z ∈ U, complexDbar (s.indicator ξ) z = s.indicator (complexDbar ξ) z) ∧
      (∀ z ∈ U, ‖complexDbar (s.indicator ξ) z‖ ≤ C * ‖s.indicator ξ z‖) := by
  classical
  obtain ⟨hreg, hd⟩ := contDiffOn_indicator_of_frontier_firstJet_zero hU hs hξ hzero
  have heq (z : ℂ) (hz : z ∈ U) :
      complexDbar (s.indicator ξ) z = s.indicator (complexDbar ξ) z := by
    unfold complexDbar
    rw [hd z hz]
    by_cases hzs : z ∈ s
    · simp only [indicator_of_mem hzs]
    · simp only [indicator_of_notMem hzs, zero_apply,
        smul_zero, add_zero]
  refine ⟨hreg, heq, ?_⟩
  intro z hz
  rw [heq z hz]
  by_cases hzs : z ∈ s
  · simpa only [indicator_of_mem hzs] using hbound z ⟨hz, hzs⟩
  · simp only [indicator_of_notMem hzs, norm_zero, mul_zero, le_refl]

end DifferentialGeometry.Analysis
