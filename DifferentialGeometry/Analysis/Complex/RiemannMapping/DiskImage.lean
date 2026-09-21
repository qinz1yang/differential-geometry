import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.ContDiff.RCLike

section

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace Complex

private theorem closed_unit_disk_subset_source
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = ball (0 : ℂ) r) :
    closedBall (0 : ℂ) 1 ⊆ e.source := by
  rw [hsource]
  exact closedBall_subset_ball hr

theorem buffered_disk_image_geometry
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = ball (0 : ℂ) r) :
    IsOpen (e '' ball (0 : ℂ) 1) ∧
      IsCompact (e '' closedBall (0 : ℂ) 1) ∧
      closure (e '' ball (0 : ℂ) 1) = e '' closedBall (0 : ℂ) 1 ∧
      frontier (e '' ball (0 : ℂ) 1) = e '' sphere (0 : ℂ) 1 ∧
      e '' closedBall (0 : ℂ) 1 ⊆ e.target ∧
      e '' sphere (0 : ℂ) 1 ⊆ e.target ∧
      Bornology.IsBounded (e '' ball (0 : ℂ) 1) := by
  have hclosed := closed_unit_disk_subset_source e hr hsource
  have hball : ball (0 : ℂ) 1 ⊆ e.source := ball_subset_closedBall.trans hclosed
  have hsphere : sphere (0 : ℂ) 1 ⊆ e.source := sphere_subset_closedBall.trans hclosed
  have hcompact : IsCompact (e '' closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn (e.continuousOn.mono hclosed)
  have htarget : e '' closedBall (0 : ℂ) 1 ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hclosed hx)
  have hclsub : closure (e '' ball (0 : ℂ) 1) ⊆ e '' closedBall (0 : ℂ) 1 :=
    closure_minimal (image_mono ball_subset_closedBall) hcompact.isClosed
  have himage : e.IsImage (ball (0 : ℂ) 1) (e '' ball (0 : ℂ) 1) := by
    intro x hx
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyx := e.injOn (hball hy) hx heq
      simpa only [hyx] using hy
    · intro h
      exact mem_image_of_mem e h
  have hclosure : closure (e '' ball (0 : ℂ) 1) = e '' closedBall (0 : ℂ) 1 := by
    have h := himage.closure.image_eq
    rw [closure_ball (0 : ℂ) one_ne_zero,
      inter_eq_right.mpr hclosed, inter_eq_right.mpr (hclsub.trans htarget)] at h
    exact h.symm
  have hfrontier : frontier (e '' ball (0 : ℂ) 1) = e '' sphere (0 : ℂ) 1 := by
    have h := himage.frontier.image_eq
    have hfsub : frontier (e '' ball (0 : ℂ) 1) ⊆ e.target :=
      frontier_subset_closure.trans (hclsub.trans htarget)
    rw [frontier_ball (0 : ℂ) one_ne_zero, inter_eq_right.mpr hsphere,
      inter_eq_right.mpr hfsub] at h
    exact h.symm
  refine ⟨e.isOpen_image_of_subset_source isOpen_ball hball, hcompact, hclosure,
    hfrontier, htarget, ?_, ?_⟩
  · exact (image_mono sphere_subset_closedBall).trans htarget
  · exact hcompact.isBounded.subset (image_mono ball_subset_closedBall)

theorem buffered_disk_image_defining_function
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = ball (0 : ℂ) r)
    (he : ContDiffOn ℝ ∞ e e.source) (hinv : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (fun y => ‖e.symm y‖ ^ 2 - 1) e.target ∧
      (∀ y ∈ closure (e '' ball (0 : ℂ) 1), ‖e.symm y‖ ^ 2 - 1 ≤ 0) ∧
      ∀ y ∈ frontier (e '' ball (0 : ℂ) 1),
        ‖e.symm y‖ ^ 2 - 1 = 0 ∧
          fderiv ℝ (fun z => ‖e.symm z‖ ^ 2 - 1) y ≠ 0 := by
  let g : ℂ → ℝ := fun y => ‖e.symm y‖ ^ 2 - 1
  have hgs : ContDiffOn ℝ ∞ g e.target :=
    (ContDiffOn.norm_sq (𝕜 := ℝ) hinv).sub contDiffOn_const
  have hclosed := closed_unit_disk_subset_source e hr hsource
  obtain ⟨_, _, hclosure, hfrontier, _, _, _⟩ := buffered_disk_image_geometry e hr hsource
  refine ⟨hgs, ?_, ?_⟩
  · intro y hy
    rw [hclosure] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [e.left_inv (hclosed hx)]
    have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    nlinarith [norm_nonneg x]
  · intro y hy
    rw [hfrontier] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxs : x ∈ e.source := hclosed (sphere_subset_closedBall hx)
    have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    constructor
    · rw [e.left_inv hxs, hxnorm]
      norm_num
    · intro hzero
      have hdg : DifferentiableAt ℝ g (e x) :=
        (hgs.contDiffAt (e.open_target.mem_nhds (e.map_source hxs))).differentiableAt (by simp)
      have hde : DifferentiableAt ℝ e x :=
        (he.contDiffAt (e.open_source.mem_nhds hxs)).differentiableAt (by simp)
      have hgerm : g ∘ e =ᶠ[𝓝 x] (fun z : ℂ => ‖z‖ ^ 2 - 1) := by
        filter_upwards [e.open_source.mem_nhds hxs] with z hz
        simp only [Function.comp_apply, g, e.left_inv hz]
      have hchain := fderiv_comp x hdg hde
      change fderiv ℝ (g ∘ e) x = _ at hchain
      have hrad : HasFDerivAt (fun z : ℂ => ‖z‖ ^ 2 - 1) ((2 : ℕ) • innerSL ℝ x) x :=
        (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1
      rw [hgerm.fderiv_eq, hrad.fderiv] at hchain
      change fderiv ℝ g (e x) = 0 at hzero
      rw [hzero, ContinuousLinearMap.zero_comp] at hchain
      have hv := congrArg (fun L : ℂ →L[ℝ] ℝ => L x) hchain
      simp only [two_smul, _root_.add_apply, _root_.zero_apply] at hv
      change inner ℝ x x + inner ℝ x x = 0 at hv
      rw [real_inner_self_eq_norm_sq, hxnorm] at hv
      norm_num at hv

end Complex

end

end

section

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff NNReal

namespace Complex

theorem interior_closure_buffered_disk_image
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = ball (0 : ℂ) r) :
    interior (closure (e '' ball (0 : ℂ) 1)) = e '' ball (0 : ℂ) 1 := by
  obtain ⟨_, _, hclosure, _, hKtarget, _, _⟩ := buffered_disk_image_geometry e hr hsource
  have hclosed : closedBall (0 : ℂ) 1 ⊆ e.source := by
    rw [hsource]
    exact closedBall_subset_ball hr
  have hball : ball (0 : ℂ) 1 ⊆ e.source := ball_subset_closedBall.trans hclosed
  have htarget : e '' ball (0 : ℂ) 1 ⊆ e.target :=
    (image_mono ball_subset_closedBall).trans hKtarget
  have himage : e.IsImage (ball (0 : ℂ) 1) (e '' ball (0 : ℂ) 1) := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    rw [inter_eq_right.mpr hball, inter_eq_right.mpr htarget]
  have hi : interior (closure (e '' ball (0 : ℂ) 1)) ⊆ e.target := by
    apply interior_subset.trans
    rw [hclosure]
    exact hKtarget
  have h := himage.closure.interior.image_eq
  rw [closure_ball (0 : ℂ) one_ne_zero, interior_closedBall (0 : ℂ) one_ne_zero,
    inter_eq_right.mpr hball, inter_eq_right.mpr hi] at h
  exact h.symm

theorem exists_exterior_point_near_frontier_buffered_disk_image
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = ball (0 : ℂ) r)
    {p : ℂ} (hp : p ∈ frontier (e '' ball (0 : ℂ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ ball p ε, z ∉ closure (e '' ball (0 : ℂ) 1) := by
  have hU := (buffered_disk_image_geometry e hr hsource).1
  have hpout : p ∉ e '' ball (0 : ℂ) 1 := by
    rw [hU.frontier_eq] at hp
    exact hp.2
  have hpext : p ∈ closure (closure (e '' ball (0 : ℂ) 1))ᶜ := by
    rw [closure_compl, interior_closure_buffered_disk_image e hr hsource]
    exact hpout
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hpext ε hε
  exact ⟨z, by simpa only [mem_ball, dist_comm] using hdist, hz⟩

theorem exists_lipschitzOnWith_inverse_ball_of_contDiffOn
    (e : OpenPartialHomeomorph ℂ ℂ) (hinv : ContDiffOn ℝ 1 e.symm e.target)
    {p : ℂ} (hp : p ∈ e.target) :
    ∃ ε : ℝ, 0 < ε ∧ ball p ε ⊆ e.target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C e.symm (ball p ε) := by
  obtain ⟨C, s, hs, hLip⟩ :=
    (hinv.contDiffAt (e.open_target.mem_nhds hp)).exists_lipschitzOnWith
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (e.open_target.mem_nhds hp))
  exact ⟨ε, hε, hsub.trans inter_subset_right, C, hLip.mono (hsub.trans inter_subset_left)⟩

end Complex

end

end
