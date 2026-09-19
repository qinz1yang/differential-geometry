/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.FramedCornerSmoothing
import DifferentialGeometry.Topology.Homeomorph.ConjugateFamily

/-! Supported corner smoothing compatible with a prescribed smooth chart. -/

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Manifold

theorem exists_isotopy_smoothing_framed_corner_in_chart
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ F H} (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (he : ContMDiffOn I 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ e.symm e.target)
    {η : ℝ} (hη : 0 < η) (hηe : closedBall (0 : ℝ × ℝ) η ⊆ e.target) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η / 8 ∧
      ∃ J : ℝ → M ≃ₜ M,
        Continuous (fun z : ℝ × M => J z.1 z.2) ∧
        Continuous (fun z : ℝ × M => (J z.1).symm z.2) ∧
        J 0 = Homeomorph.refl M ∧
        IsCompact (e.symm '' closedBall (0 : ℝ × ℝ) η) ∧
        (∀ t, EqOn (J t) id (e.symm '' closedBall (0 : ℝ × ℝ) η)ᶜ ∧
          EqOn (J t).symm id (e.symm '' closedBall (0 : ℝ × ℝ) η)ᶜ) ∧
        ∃ c : OpenPartialHomeomorph M (ℝ × ℝ),
          c.source = e.source ∧ ball (0 : ℝ × ℝ) (η / 16) ⊆ c.target ∧
          ContMDiffOn I 𝓘(ℝ, ℝ × ℝ) ∞ c c.source ∧
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ c.symm c.target ∧
          (∀ p, c.symm p = e.symm (p.1, Real.smoothAbs δ p.1 + p.2)) ∧
          ∀ p ∈ ball (0 : ℝ × ℝ) (η / 16),
            J 1 (e.symm (p.1, |p.1| + p.2)) = c.symm p := by
  obtain ⟨δ, hδ, hδη, D, hD, hDi, hD0, hDfix, _, d, hd, hframe, _⟩ :=
    exists_isotopy_smoothing_framed_corner hη
  have hfix (t : ℝ) : EqOn (D t) id (closedBall (0 : ℝ × ℝ) η)ᶜ ∧
      EqOn (D t).symm id (closedBall (0 : ℝ × ℝ) η)ᶜ :=
    ⟨(hDfix t).1.mono (compl_subset_compl.mpr ball_subset_closedBall),
      (hDfix t).2.mono (compl_subset_compl.mpr ball_subset_closedBall)⟩
  obtain ⟨J, hJ, hJi, hJe, hJfix⟩ := e.exists_conjugate_homeomorph_family
    D hD hDi (isCompact_closedBall (0 : ℝ × ℝ) η) hηe hfix
  let c := e.trans d.symm.toHomeomorph.toOpenPartialHomeomorph
  have hcsource : c.source = e.source := by
    ext x
    change (x ∈ e.source ∧ True) ↔ x ∈ e.source
    simp only [and_true]
  have hpcoords (p : ℝ × ℝ) (hp : p ∈ ball (0 : ℝ × ℝ) (η / 16)) :
      |p.1| < η / 16 ∧ |p.2| < η / 16 := by
    simpa only [mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      max_lt_iff] using hp
  have hold (p : ℝ × ℝ) (hp : p ∈ ball (0 : ℝ × ℝ) (η / 16)) :
      (p.1, |p.1| + p.2) ∈ e.target := by
    apply hηe
    rw [mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs, max_le_iff]
    have hx := hpcoords p hp
    have hy := abs_add_le |p.1| p.2
    rw [abs_abs] at hy
    constructor <;> linarith [hx.1, hx.2]
  have hnew (p : ℝ × ℝ) (hp : p ∈ ball (0 : ℝ × ℝ) (η / 16)) : d p ∈ e.target := by
    apply hηe
    rw [hd, mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs, max_le_iff]
    have hx := hpcoords p hp
    have hg := Real.smoothAbs.sub_abs_mem_Icc hδ p.1
    have hn : 0 ≤ Real.smoothAbs δ p.1 := by linarith [abs_nonneg p.1, hg.1]
    have hy := abs_add_le (Real.smoothAbs δ p.1) p.2
    rw [abs_of_nonneg hn] at hy
    constructor <;> linarith [hx.1, hx.2, hg.2]
  have hctarget : ball (0 : ℝ × ℝ) (η / 16) ⊆ c.target :=
    fun p hp => ⟨trivial, hnew p hp⟩
  have hcsmooth : ContMDiffOn I 𝓘(ℝ, ℝ × ℝ) ∞ c c.source := by
    change ContMDiffOn I 𝓘(ℝ, ℝ × ℝ) ∞ (fun x => d.symm (e x)) c.source
    exact d.symm.contMDiff.comp_contMDiffOn (he.mono (fun _ hx => hx.1))
  have hcis : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ c.symm c.target := by
    change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun p => e.symm (d p)) c.target
    exact hei.comp d.contMDiff.contMDiffOn (fun _ hp => hp.2)
  refine ⟨δ, hδ, hδη, J, hJ, hJi, ?_, ?_, hJfix,
    c, hcsource, hctarget, hcsmooth, hcis, ?_, ?_⟩
  · apply Homeomorph.ext
    intro x
    rw [(hJe 0 x).1, hD0]
    by_cases hx : x ∈ e.source
    · rw [e.conjugateMap_of_mem _ hx]
      exact e.left_inv hx
    · exact e.conjugateMap_of_notMem _ hx
  · exact (isCompact_closedBall (0 : ℝ × ℝ) η).image_of_continuousOn
      (e.continuousOn_symm.mono hηe)
  · intro p
    change e.symm (d p) = _
    rw [hd]
  · intro p hp
    rw [(hJe 1 _).1, e.conjugateMap_of_mem _ (e.map_target (hold p hp)),
      e.right_inv (hold p hp), hframe p.1 p.2 (by linarith [(hpcoords p hp).2])]
    rfl

end DifferentialGeometry.Manifold
