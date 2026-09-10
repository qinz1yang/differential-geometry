import DifferentialGeometry.Analysis.Calculus.Cutoff.LipschitzCutoff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff NNReal

namespace Poincare.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_small_compact_extension_of_zero_derivative
    {f : E → F} {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0)
    (c : ℝ≥0) (hc : 0 < c) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ U ∧ g =ᶠ[𝓝 0] f ∧ LipschitzWith c g := by
  let b : ContDiffBump (0 : E) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    (b.contDiff : ContDiff ℝ ∞ (b : E → ℝ)) (by simp)
  let δ : ℝ≥0 := c / (1 + B)
  have hδ : (0 : ℝ) < δ := by change 0 < (c : ℝ) / (1 + B); positivity
  have hdf := (hf.contDiffAt (hU.mem_nhds h0U)).continuousAt_fderiv (by simp)
  have hsmall : ∀ᶠ x in 𝓝 (0 : E), ‖fderiv ℝ f x‖ < δ :=
    hdf.norm.eventually_lt_const (by simpa only [hdf0, norm_zero] using hδ)
  obtain ⟨a, ha, haU⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds h0U) hsmall)
  let r : ℝ≥0 := ⟨a / 2, by positivity⟩
  have hr : (0 : ℝ) < r := by change 0 < a / 2; positivity
  have hball (x : E) (hx : x ∈ closedBall 0 r) : x ∈ U ∧ ‖fderiv ℝ f x‖ < δ := by
    apply haU
    rw [mem_ball, dist_zero_right]
    have hn := mem_closedBall_zero_iff.mp hx
    change ‖x‖ ≤ a / 2 at hn
    linarith
  have hflip : LipschitzOnWith δ f (closedBall 0 r) :=
    (convex_closedBall (0 : E) (r : ℝ)).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx ↦ (hf.contDiffAt (hU.mem_nhds (hball x hx).1)).differentiableAt (by simp))
      (fun x hx ↦ (hball x hx).2.le)
  let ψ : E → ℝ := fun x ↦ b ((r : ℝ)⁻¹ • x)
  have hscale : ContDiff ℝ ∞ (fun x : E ↦ (r : ℝ)⁻¹ • x) :=
    (contDiff_id : ContDiff ℝ ∞ (id : E → E)).const_smul (r : ℝ)⁻¹
  have hψsmooth : ContDiff ℝ ∞ ψ := b.contDiff.comp hscale
  have hscalelip : LipschitzWith r⁻¹ (fun x : E ↦ (r : ℝ)⁻¹ • x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), NNReal.coe_inv, le_refl]
  have hψlip : LipschitzWith (B * r⁻¹) ψ := hB.comp hscalelip
  have hψnorm (x : E) : ‖ψ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    exact b.le_one
  have hψout (x : E) (hx : x ∉ closedBall 0 r) : ψ x = 0 := by
    apply b.zero_of_le_dist
    change 1 ≤ dist ((r : ℝ)⁻¹ • x) 0
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
      ← div_eq_inv_mul]
    exact (one_le_div hr).mpr (not_le.mp (fun h ↦ hx (mem_closedBall_zero_iff.mpr h))).le
  let g : E → F := fun x ↦ ψ x • f x
  have hgsupport : tsupport g ⊆ closedBall 0 r :=
    closure_minimal (Function.support_subset_iff'.mpr (fun x hx ↦ by
      change ψ x • f x = 0
      rw [hψout x hx, zero_smul])) isClosed_closedBall
  have hgsmooth : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hψsmooth.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hxr : x ∉ closedBall 0 r := fun h ↦ hx (hball x h).1
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E ↦ (0 : F)) x).congr_of_eventuallyEq
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hxr] with y hy
      change ψ y • f y = 0
      rw [hψout y hy, zero_smul]
  have hgcompact : HasCompactSupport g :=
    (isCompact_closedBall (0 : E) (r : ℝ)).of_isClosed_subset (isClosed_tsupport g) hgsupport
  have hgerm : g =ᶠ[𝓝 0] f := by
    have hb0 : (b : E → ℝ) =ᶠ[𝓝 0] 1 := b.eventuallyEq_one_of_mem_ball (by simp [b])
    have hs0 : Tendsto (fun x : E ↦ (r : ℝ)⁻¹ • x) (𝓝 0) (𝓝 0) := by
      simpa only [smul_zero] using hscale.continuous.tendsto (0 : E)
    filter_upwards [hb0.comp_tendsto hs0] with x hx
    change b ((r : ℝ)⁻¹ • x) = 1 at hx
    change b ((r : ℝ)⁻¹ • x) • f x = f x
    rw [hx, one_smul]
  refine ⟨g, hgsmooth, hgcompact, hgsupport.trans (fun x hx ↦ (hball x hx).1), hgerm, ?_⟩
  have hbound := lipschitzWith_cutoff_smul hψlip hψnorm hψout hflip hf0
  have hrn : r ≠ 0 := by exact_mod_cast hr.ne'
  have heq : δ * (1 + B * r⁻¹ * r) = c := by
    rw [mul_assoc B, inv_mul_cancel₀ hrn, mul_one]
    exact div_mul_cancel₀ c (by positivity)
  exact heq ▸ hbound

end Poincare.Analysis
