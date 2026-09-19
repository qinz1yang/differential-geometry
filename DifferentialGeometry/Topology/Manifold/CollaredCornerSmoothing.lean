/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.FramedCornerSmoothing

/-! Supported smoothing of a framed corner preserving the collar depth. -/

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Manifold

theorem exists_isotopy_smoothing_collared_corner {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η / 8 ∧
      ∃ K : ℝ → ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ),
        Continuous (fun z : ℝ × ((ℝ × ℝ) × ℝ) => K z.1 z.2) ∧
        Continuous (fun z : ℝ × ((ℝ × ℝ) × ℝ) => (K z.1).symm z.2) ∧
        K 0 = Homeomorph.refl ((ℝ × ℝ) × ℝ) ∧
        (∀ t p, (K t p).2 = p.2) ∧
        (∀ t, EqOn (K t) id (ball (0 : (ℝ × ℝ) × ℝ) η)ᶜ ∧
          EqOn (K t).symm id (ball (0 : (ℝ × ℝ) × ℝ) η)ᶜ) ∧
        (∀ t p, dist (K t p) p < η) ∧
        ∃ d : ((ℝ × ℝ) × ℝ) ≃ₘ[ℝ] ((ℝ × ℝ) × ℝ),
          (∀ p, d p = ((p.1.1, Real.smoothAbs δ p.1.1 + p.1.2), p.2)) ∧
          (∀ x u z, |u| ≤ η / 8 → |z| ≤ η / 8 →
            K 1 ((x, |x| + u), z) = d ((x, u), z)) ∧
          K 1 ≠ Homeomorph.refl ((ℝ × ℝ) × ℝ) := by
  obtain ⟨δ, hδ, hδη, H, hH, hHi, hH0, hfix, hdist, d, hd, hframe, hne⟩ :=
    exists_isotopy_smoothing_framed_corner hη
  let b : ContDiffBump (0 : ℝ) := ⟨η / 8, η / 4, by positivity, by linarith⟩
  have hK : Continuous (fun q : ℝ × ((ℝ × ℝ) × ℝ) =>
      (H (q.1 * b q.2.2) q.2.1, q.2.2)) :=
    (hH.comp ((continuous_fst.mul (b.continuous.comp continuous_snd.snd)).prodMk
      continuous_snd.fst)).prodMk continuous_snd.snd
  have hKi : Continuous (fun q : ℝ × ((ℝ × ℝ) × ℝ) =>
      ((H (q.1 * b q.2.2)).symm q.2.1, q.2.2)) :=
    (hHi.comp ((continuous_fst.mul (b.continuous.comp continuous_snd.snd)).prodMk
      continuous_snd.fst)).prodMk continuous_snd.snd
  let K (t : ℝ) : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ) :=
    { toFun := fun p => (H (t * b p.2) p.1, p.2)
      invFun := fun p => ((H (t * b p.2)).symm p.1, p.2)
      left_inv := fun _ => by simp only [Homeomorph.symm_apply_apply]
      right_inv := fun _ => by simp only [Homeomorph.apply_symm_apply]
      continuous_toFun := hK.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := hKi.comp (continuous_const.prodMk continuous_id) }
  have hK0 : K 0 = Homeomorph.refl ((ℝ × ℝ) × ℝ) := by
    apply Homeomorph.ext
    intro p
    change (H (0 * b p.2) p.1, p.2) = p
    rw [zero_mul, hH0]
    rfl
  have hKfix (t : ℝ) (p : (ℝ × ℝ) × ℝ)
      (hp : p ∉ ball (0 : (ℝ × ℝ) × ℝ) η) : K t p = p := by
    change (H (t * b p.2) p.1, p.2) = p
    by_cases hx : p.1 ∈ ball (0 : ℝ × ℝ) η
    · have hz : η ≤ dist p.2 0 := by
        apply le_of_not_gt
        intro hz
        apply hp
        change dist p 0 < η
        rw [Prod.dist_eq]
        exact max_lt hx hz
      rw [b.zero_of_le_dist (by change η / 4 ≤ dist p.2 0; linarith), mul_zero, hH0]
      rfl
    · rw [(hfix (t * b p.2)).1 hx]
      rfl
  let d₃ : ((ℝ × ℝ) × ℝ) ≃ₘ[ℝ] ((ℝ × ℝ) × ℝ) :=
    { toEquiv := d.toEquiv.prodCongr (Equiv.refl ℝ)
      contMDiff_toFun := ((d.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff
      contMDiff_invFun := ((d.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff }
  refine ⟨δ, hδ, hδη, K, hK, hKi, hK0, fun _ _ => rfl, ?_, ?_, d₃, ?_, ?_, ?_⟩
  · intro t
    refine ⟨fun p hp => hKfix t p hp, ?_⟩
    intro p hp
    apply (K t).injective
    rw [(K t).apply_symm_apply]
    exact (hKfix t p hp).symm
  · intro t p
    change dist (H (t * b p.2) p.1, p.2) p < η
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hdist _ _
  · intro p
    change (d p.1, p.2) = _
    rw [hd]
  · intro x u z hu hz
    have hb : b z = 1 := b.one_of_mem_closedBall (by simpa [Real.dist_eq] using hz)
    change (H (1 * b z) (x, |x| + u), z) = (d (x, u), z)
    rw [hb, one_mul, hframe x u hu]
  · intro hId
    apply hne
    apply Homeomorph.ext
    intro p
    have h := congrArg (fun e : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ) =>
      (e (p, 0)).1) hId
    change H (1 * b 0) p = p at h
    have hb : b 0 = 1 :=
      b.one_of_mem_closedBall (by simp only [mem_closedBall, dist_self]; exact b.rIn_pos.le)
    rwa [hb, one_mul] at h

end DifferentialGeometry.Manifold
