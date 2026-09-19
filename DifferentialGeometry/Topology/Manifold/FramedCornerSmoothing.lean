/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.LocalizedGraph
import DifferentialGeometry.Topology.Diffeomorph.Graph
import DifferentialGeometry.Analysis.Calculus.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Relative ambient smoothing of a polygonal corner and its transverse framing. -/

open Set Metric
open scoped ContDiff Manifold NNReal

namespace DifferentialGeometry.Manifold

theorem exists_isotopy_smoothing_framed_corner {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η / 8 ∧
      ∃ H : ℝ → (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
        Continuous (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2) ∧
        Continuous (fun z : ℝ × (ℝ × ℝ) => (H z.1).symm z.2) ∧
        H 0 = Homeomorph.refl (ℝ × ℝ) ∧
        (∀ t, EqOn (H t) id (ball (0 : ℝ × ℝ) η)ᶜ ∧
          EqOn (H t).symm id (ball (0 : ℝ × ℝ) η)ᶜ) ∧
        (∀ t p, dist (H t p) p < η) ∧
        ∃ d : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
          (∀ p, d p = (p.1, Real.smoothAbs δ p.1 + p.2)) ∧
          (∀ x u, |u| ≤ η / 8 → H 1 (x, |x| + u) = d (x, u)) ∧
          H 1 ≠ Homeomorph.refl (ℝ × ℝ) := by
  let b : ContDiffBump (0 : ℝ) := ⟨η / 8, η / 4, by positivity, by linarith⟩
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    b.contDiff (show (∞ : ℕ∞ω) ≠ 0 by simp)
  let δ : ℝ := min (η / 16) (1 / (8 * ((B : ℝ) + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδη : δ ≤ η / 16 := min_le_left _ _
  have hδB : δ * (8 * ((B : ℝ) + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 8 * ((B : ℝ) + 1))).mp (min_le_right _ _)
  have hnorm (x : ℝ) : ‖Real.smoothAbs δ x - |x|‖ ≤ 2 * δ := by
    rw [Real.norm_of_nonneg (Real.smoothAbs.sub_abs_mem_Icc hδ x).1]
    exact (Real.smoothAbs.sub_abs_mem_Icc hδ x).2
  have hsmall (x : ℝ) : (B : ℝ) * ‖Real.smoothAbs δ x - |x|‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hnorm x) B.coe_nonneg).trans (by nlinarith)
  have hfixed : EqOn (Real.smoothAbs δ) (abs : ℝ → ℝ) (closedBall (0 : ℝ) δ)ᶜ := by
    intro x hx
    apply Real.smoothAbs.eq_abs_of_le hδ
    have hx' : δ < |x| := by
      simpa only [mem_compl_iff, mem_closedBall, Real.dist_eq, sub_zero, not_le] using hx
    exact hx'.le
  obtain ⟨H, hH, hHi, hH0, hformula, hframe, hdist, J, hJdef, hJ, hfix⟩ :=
    Homeomorph.exists_isotopy_graphOn_of_small_sub continuous_abs
      (Real.smoothAbs.contDiff δ).continuous (isCompact_closedBall (0 : ℝ) δ)
      hfixed b hB hsmall
  have hJball : J ⊆ ball (0 : ℝ × ℝ) η := by
    rw [hJdef]
    rintro _ ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
    have hx' : |x| ≤ δ := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hx
    have hu' : |u| ≤ η / 4 := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hu
    change (x, u + |x|) ∈ ball (0 : ℝ × ℝ) η
    rw [mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
      max_lt_iff]
    refine ⟨by linarith, ?_⟩
    have hb := abs_add_le u |x|
    rw [abs_abs] at hb
    linarith
  let d : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) :=
    Diffeomorph.graphShear contDiff_zero_fun (Real.smoothAbs.contDiff δ)
  have hd (p : ℝ × ℝ) : d p = (p.1, Real.smoothAbs δ p.1 + p.2) := by
    rw [Diffeomorph.graphShear_apply]
    simp only [sub_zero, add_comm]
  have hlast (x u : ℝ) (hu : |u| ≤ η / 8) : H 1 (x, |x| + u) = d (x, u) := by
    rw [hframe 1 x u hu, Real.smoothTransition.one, one_mul, hd]
    congr 1
    ring
  refine ⟨δ, hδ, by linarith, H, hH, hHi, hH0, ?_, ?_, d, hd, hlast, ?_⟩
  · intro t
    exact ⟨(hfix t).1.mono (compl_subset_compl.mpr hJball),
      (hfix t).2.mono (compl_subset_compl.mpr hJball)⟩
  · intro t p
    have hp : (H t p).1 = p.1 := by rw [hformula]
    rw [Prod.dist_eq, hp, dist_self, max_eq_right dist_nonneg]
    exact ((hdist t p).trans (hnorm p.1)).trans_lt (by linarith)
  · intro hId
    have habs : Real.smoothAbs δ = (abs : ℝ → ℝ) := by
      funext x
      have h := hlast x 0 (by rw [abs_zero]; positivity)
      rw [hId, hd] at h
      simpa only [Homeomorph.refl_apply, add_zero, id_eq] using congrArg Prod.snd h.symm
    apply not_differentiableAt_abs_zero
    rw [← habs]
    exact (Real.smoothAbs.contDiff δ).differentiable (by simp) 0

end DifferentialGeometry.Manifold
