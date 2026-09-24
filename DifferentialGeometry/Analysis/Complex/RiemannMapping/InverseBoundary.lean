import DifferentialGeometry.Analysis.Complex.RiemannMapping.BoundaryHomeomorphism
import DifferentialGeometry.Analysis.Complex.SmoothImageCircle
import DifferentialGeometry.Analysis.Complex.HolomorphicBoundaryRegularity
import Mathlib.Analysis.Calculus.ContDiff.RCLike

section

noncomputable section

open Set Metric
open DifferentialGeometry.Geometry
open scoped ContDiff NNReal

namespace Complex

theorem exists_bilipschitz_riemann_map_comp_extension_of_buffered_disk
    (W f : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hWsource : W.source = ball (0 : ℂ) r)
    (hW : ContDiffOn ℝ ∞ W W.source) (hWi : ContDiffOn ℝ ∞ W.symm W.target)
    (hfsource : f.source = W '' ball (0 : ℂ) 1)
    (hftarget : f.target = ball (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f f.source) :
    ∃ (C D : ℝ≥0) (H : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1),
      LipschitzWith C H ∧ LipschitzWith D H.symm ∧
      ContDiffOn ℝ ∞ (fun z => (H.symm (diskRetraction z) : ℂ)) (closedBall (0 : ℂ) 1) ∧
      (∀ z (hz : z ∈ ball (0 : ℂ) 1),
        (H ⟨z, ball_subset_closedBall hz⟩ : ℂ) = f (W z)) ∧
      (∀ z (hz : z ∈ ball (0 : ℂ) 1),
        (H.symm ⟨z, ball_subset_closedBall hz⟩ : ℂ) = W.symm (f.symm z)) := by
  obtain ⟨C, H, hHLip, hH, hHi⟩ :=
    exists_lipschitz_homeomorph_riemann_map_comp_of_buffered_disk
      W f hr hWsource hW hWi hfsource hftarget hf
  have hclosed : closedBall (0 : ℂ) 1 ⊆ W.source := by
    rw [hWsource]
    exact closedBall_subset_ball hr
  let v : ℂ → ℂ := fun z => (H.symm (diskRetraction z) : ℂ)
  let U : ℂ → ℂ := W ∘ v
  have hvc : Continuous v := continuous_subtype_val.comp
    (H.symm.continuous.comp diskRetraction_lipschitz.continuous)
  have hvsource (z : ℂ) : v z ∈ W.source := hclosed (H.symm (diskRetraction z)).property
  have hUc : Continuous U := W.continuousOn.comp_continuous hvc hvsource
  have hUeq (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : U z = f.symm z := by
    change W (H.symm (diskRetraction z)) = f.symm z
    rw [diskRetraction_coe ⟨z, ball_subset_closedBall hz⟩, hHi z hz]
    apply W.right_inv
    obtain ⟨x, hx, hxf⟩ := hfsource ▸ f.map_target (hftarget ▸ hz)
    rw [← hxf]
    exact W.map_source (hclosed (ball_subset_closedBall hx))
  have hUi : DifferentiableOn ℂ U (ball (0 : ℂ) 1) := by
    have hi := differentiableOn_symm_of_differentiableOn f hf
    rw [hftarget] at hi
    exact hi.congr hUeq
  obtain ⟨γ, hγ, hγs, hγd, hγrange⟩ := exists_regular_parametrization_image_circle
    W (sphere_subset_closedBall.trans hclosed) hW (hWi.differentiableOn (by simp))
  have htrace (z : ℂ) (hz : ‖z‖ = 1) : U z ∈ range γ := by
    rw [hγrange]
    refine ⟨v z, ?_, rfl⟩
    apply mem_sphere_zero_iff_norm.mpr
    apply le_antisymm (mem_closedBall_zero_iff.mp (H.symm (diskRetraction z)).property)
    by_contra! hlt
    have hvi : v z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hlt
    have hh : (H (H.symm (diskRetraction z)) : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [hH _ hvi]
      exact hftarget ▸ f.map_source (hfsource ▸ mem_image_of_mem W hvi)
    have hzcl : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz.le
    rw [H.apply_symm_apply, diskRetraction_coe ⟨z, hzcl⟩] at hh
    exact (ne_of_lt (mem_ball_zero_iff.mp hh)) hz
  have hUs : ContDiffOn ℝ ∞ U (closedBall (0 : ℂ) 1) :=
    contDiffOn_closedDisk_of_differentiableOn_of_embedded_loop
      Real.two_pi_pos hγ hγs hγd hUc.continuousOn hUi htrace
  have hvs : ContDiffOn ℝ ∞ v (closedBall (0 : ℂ) 1) :=
    (hWi.comp hUs (fun z _ => W.map_source (hvsource z))).congr
      (fun z _ => (W.left_inv (hvsource z)).symm)
  obtain ⟨D, hD⟩ := hvs.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ℂ) 1) (isCompact_closedBall (0 : ℂ) 1)
  have hDLip : LipschitzWith D H.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (H.symm x : ℂ) (H.symm y : ℂ) ≤ (D : ℝ) * dist (x : ℂ) (y : ℂ)
    simpa only [v, diskRetraction_coe] using hD.dist_le_mul x x.2 y y.2
  exact ⟨C, D, H, hHLip, hDLip, hvs, hH, hHi⟩

end Complex

end

end
