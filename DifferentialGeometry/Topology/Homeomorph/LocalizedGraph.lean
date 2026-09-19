/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.LipschitzFamily
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Compactly supported ambient isotopies between nearby continuous framed graphs. -/

open Set Metric
open scoped ContDiff NNReal

namespace Homeomorph

theorem exists_isotopy_graphOn_of_small_sub
    {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) {K : Set X} (hK : IsCompact K)
    (hfixed : EqOn g f Kᶜ) (b : ContDiffBump (0 : ℝ))
    {B : ℝ≥0} (hB : LipschitzWith B b)
    (hsmall : ∀ x, (B : ℝ) * ‖g x - f x‖ ≤ 1 / 2) :
    ∃ H : ℝ → (X × ℝ) ≃ₜ (X × ℝ),
      Continuous (fun z : ℝ × (X × ℝ) => H z.1 z.2) ∧
      Continuous (fun z : ℝ × (X × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Homeomorph.refl (X × ℝ) ∧
      (∀ t p, H t p = (p.1, p.2 +
        b (p.2 - f p.1) * (Real.smoothTransition t * (g p.1 - f p.1)))) ∧
      (∀ t x u, |u| ≤ b.rIn →
        H t (x, f x + u) = (x, f x + u + Real.smoothTransition t * (g x - f x))) ∧
      (∀ t p, dist (H t p).2 p.2 ≤ ‖g p.1 - f p.1‖) ∧
      ∃ J : Set (X × ℝ),
        J = (fun p : X × ℝ => (p.1, p.2 + f p.1)) ''
          (K ×ˢ closedBall (0 : ℝ) b.rOut) ∧
        IsCompact J ∧ ∀ t, EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  let G : (ℝ × X) × ℝ → ℝ := fun z =>
    b (z.2 - f z.1.2) * (Real.smoothTransition z.1.1 * (g z.1.2 - f z.1.2))
  have hG : Continuous G :=
    (b.continuous.comp (continuous_snd.sub (hf.comp continuous_fst.snd))).mul
      ((Real.smoothTransition.continuous.comp continuous_fst.fst).mul
        ((hg.comp continuous_fst.snd).sub (hf.comp continuous_fst.snd)))
  have hLip (p : ℝ × X) : LipschitzWith (1 / 2) (fun y => G (p, y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hb := hB.dist_le_mul (y - f p.2) (z - f p.2)
    rw [dist_sub_right] at hb
    have ht : ‖Real.smoothTransition p.1 * (g p.2 - f p.2)‖ ≤ ‖g p.2 - f p.2‖ := by
      rw [norm_mul, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)
    change dist (b (y - f p.2) * _) (b (z - f p.2) * _) ≤ _
    rw [dist_eq_norm, ← sub_mul, norm_mul, ← dist_eq_norm]
    calc
      _ ≤ ((B : ℝ) * dist y z) * ‖g p.2 - f p.2‖ :=
        mul_le_mul hb ht (norm_nonneg _) (by positivity)
      _ = ((B : ℝ) * ‖g p.2 - f p.2‖) * dist y z := by ring
      _ ≤ (1 / 2) * dist y z := mul_le_mul_of_nonneg_right (hsmall p.2) dist_nonneg
      _ = ((1 / 2 : ℝ≥0) : ℝ) * dist y z := by norm_num
  obtain ⟨e, he, hEf, hEi⟩ := exists_addLipschitz_family hG hLip (by norm_num)
  have hF : Continuous (fun z : ℝ × (X × ℝ) => (z.2.1, e (z.1, z.2.1) z.2.2)) :=
    continuous_snd.fst.prodMk
      (hEf.comp ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd))
  have hI : Continuous (fun z : ℝ × (X × ℝ) =>
      (z.2.1, (e (z.1, z.2.1)).symm z.2.2)) :=
    continuous_snd.fst.prodMk
      (hEi.comp ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd))
  let H (t : ℝ) : (X × ℝ) ≃ₜ (X × ℝ) :=
    { toEquiv := Equiv.prodCongrRight (fun x => (e (t, x)).toEquiv)
      continuous_toFun := hF.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := hI.comp (continuous_const.prodMk continuous_id) }
  have hformula (t : ℝ) (p : X × ℝ) : H t p =
      (p.1, p.2 + b (p.2 - f p.1) *
        (Real.smoothTransition t * (g p.1 - f p.1))) := by
    change (p.1, e (t, p.1) p.2) = _
    rw [he]
  have hzero : H 0 = Homeomorph.refl (X × ℝ) := by
    apply Homeomorph.ext
    intro p
    change H 0 p = p
    rw [hformula]
    simp only [Real.smoothTransition.zero, zero_mul, mul_zero, add_zero, Prod.eta]
  have hframe (t : ℝ) (x : X) (u : ℝ) (hu : |u| ≤ b.rIn) :
      H t (x, f x + u) =
        (x, f x + u + Real.smoothTransition t * (g x - f x)) := by
    have hb : b u = 1 := b.one_of_mem_closedBall (by simpa [Real.dist_eq] using hu)
    rw [hformula]
    simp only [add_sub_cancel_left, hb, one_mul]
  let J : Set (X × ℝ) := (fun p : X × ℝ => (p.1, p.2 + f p.1)) ''
    (K ×ˢ closedBall (0 : ℝ) b.rOut)
  have hJ : IsCompact J := (hK.prod (isCompact_closedBall (0 : ℝ) b.rOut)).image
    (continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst)))
  have hfix (t : ℝ) (p : X × ℝ) (hp : p ∉ J) : H t p = p := by
    have hz : b (p.2 - f p.1) * (g p.1 - f p.1) = 0 := by
      by_cases hx : p.1 ∈ K
      · have hout : b.rOut ≤ dist (p.2 - f p.1) 0 := by
          by_contra hn
          apply hp
          exact ⟨(p.1, p.2 - f p.1), ⟨hx, (not_le.mp hn).le⟩,
            Prod.ext rfl (sub_add_cancel _ _)⟩
        rw [b.zero_of_le_dist hout, zero_mul]
      · rw [hfixed hx, sub_self, mul_zero]
    rw [hformula]
    refine Prod.ext (by rfl) ?_
    change p.2 + _ = p.2
    calc
      _ = p.2 + Real.smoothTransition t *
          (b (p.2 - f p.1) * (g p.1 - f p.1)) := by ring
      _ = p.2 := by rw [hz, mul_zero, add_zero]
  refine ⟨H, hF, hI, hzero, hformula, hframe, ?_, J, rfl, hJ, ?_⟩
  · intro t p
    rw [hformula]
    change dist (p.2 + _) p.2 ≤ _
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, Real.norm_of_nonneg b.nonneg,
      Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_of_le_one_left
      (mul_nonneg (Real.smoothTransition.nonneg _) (norm_nonneg _)) b.le_one).trans
        (mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _))
  · intro t
    refine ⟨fun p hp => hfix t p hp, ?_⟩
    intro p hp
    apply (H t).injective
    rw [(H t).apply_symm_apply]
    exact (hfix t p hp).symm

end Homeomorph
