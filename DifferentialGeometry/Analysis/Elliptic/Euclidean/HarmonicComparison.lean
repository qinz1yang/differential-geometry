import DifferentialGeometry.Analysis.Elliptic.Euclidean.MaximumPrinciple
import DifferentialGeometry.Analysis.Elliptic.Euclidean.QuadraticGrowth
import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
import Mathlib.Analysis.Normed.Module.Normalize

open Set InnerProductSpace
open scoped Topology InnerProductSpace

namespace DifferentialGeometry.Analysis

theorem norm_sub_harmonic_le_of_norm_laplacian_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {s : Set E} {f h : E → F} {H : E → ℝ} {β δ : ℝ}
    (hs : IsOpen s) (hcompact : IsCompact (closure s))
    (hf : ContinuousOn f (closure s)) (hd : ∀ x ∈ s, ContDiffAt ℝ 2 f x)
    (hh : HarmonicContOnCl h s) (hH : HarmonicContOnCl H s)
    (hβ : 0 ≤ β) (hsmall : β * δ < 1)
    (hbound : ∀ x ∈ s, ‖f x‖ ≤ δ)
    (hΔ : ∀ x ∈ s, ‖Laplacian.laplacian f x‖ ≤
      β * (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x))
    (htrace : ∀ x ∈ frontier s, h x = f x)
    (htrace_sq : ∀ x ∈ frontier s, H x = ‖f x‖ ^ 2) :
    ∀ x ∈ closure s, ‖f x - h x‖ + β / (2 * (1 - β * δ)) * ‖f x‖ ^ 2 ≤
      β / (2 * (1 - β * δ)) * H x := by
  let c := β / (2 * (1 - β * δ))
  have hden : 0 < 2 * (1 - β * δ) := by linarith
  have hc : 0 ≤ c := div_nonneg hβ hden.le
  have hcoeff : c * (2 * (1 - β * δ)) = β := div_mul_cancel₀ β hden.ne'
  have hcmp (l : F) (hl : ‖l‖ ≤ 1) : ∀ x ∈ closure s,
      c * ‖f x‖ ^ 2 + ⟪l, f x - h x⟫_ℝ - c * H x ≤ 0 := by
    refine le_of_laplacian_nonneg_of_le_frontier hcompact ?_ ?_ ?_ ?_
    · exact (((continuousOn_const.mul (hf.norm.pow 2)).add
        (continuousOn_const.inner (hf.sub hh.continuousOn))).sub
        (continuousOn_const.mul hH.continuousOn)).upperSemicontinuousOn
    · intro x hx
      have hxs : x ∈ s := hs.interior_eq ▸ hx
      exact ((contDiffAt_const.mul ((hd x hxs).norm_sq ℝ)).add
        (contDiffAt_const.inner ℝ ((hd x hxs).sub (hh.contDiffAt hxs)))).sub
        (contDiffAt_const.mul (hH.contDiffAt hxs))
    · intro x hx
      have hxs : x ∈ s := hs.interior_eq ▸ hx
      have hfd := hd x hxs
      have hhd := hh.contDiffAt hxs
      have hHd := hH.contDiffAt hxs
      have hhl : Laplacian.laplacian h x = 0 := (hh.harmonicOnNhd x hxs).2.self_of_nhds
      have hHl : Laplacian.laplacian H x = 0 := (hH.harmonicOnNhd x hxs).2.self_of_nhds
      have he : Laplacian.laplacian
          (fun y => c * ‖f y‖ ^ 2 + ⟪l, f y - h y⟫_ℝ - c * H y) x =
          c * Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x +
            ⟪l, Laplacian.laplacian f x⟫_ℝ := by
        change Laplacian.laplacian
          (((fun y => c * ‖f y‖ ^ 2) + ((innerSL ℝ l) ∘ (f - h))) - c • H) x = _
        have hn : ContDiffAt ℝ 2 (fun y => c * ‖f y‖ ^ 2) x :=
          contDiffAt_const.mul (hfd.norm_sq ℝ)
        have hi : ContDiffAt ℝ 2 ((innerSL ℝ l) ∘ (f - h)) x :=
          (innerSL ℝ l).contDiff.contDiffAt.comp x (hfd.sub hhd)
        have hC : ContDiffAt ℝ 2 (c • H) x := contDiffAt_const.smul hHd
        erw [(hn.add hi).laplacian_sub hC, hn.laplacian_add hi]
        erw [(hfd.sub hhd).laplacian_CLM_comp_left (l := innerSL ℝ l)]
        change Laplacian.laplacian (c • fun y => ‖f y‖ ^ 2) x +
          ⟪l, Laplacian.laplacian (f - h) x⟫_ℝ - Laplacian.laplacian (c • H) x = _
        erw [laplacian_smul c (hfd.norm_sq ℝ), laplacian_smul c hHd,
          hfd.laplacian_sub hhd, hhl, hHl]
        simp
      rw [he]
      let G := (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x)
      have hG : 0 ≤ G := by
        exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg
      have hn := hfd.le_laplacian_norm_sq_of_norm_laplacian_le (hΔ x hxs)
      have hbn := mul_le_mul_of_nonneg_left (hbound x hxs) hβ
      have hlow : 2 * (1 - β * δ) * G ≤
          Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x := by
        nlinarith [mul_nonneg hG (sub_nonneg.mpr hbn)]
      have hmul := mul_le_mul_of_nonneg_left hlow hc
      have hi := (abs_le.mp (abs_real_inner_le_norm l (Laplacian.laplacian f x))).1
      have hil := mul_le_mul_of_nonneg_right hl (norm_nonneg (Laplacian.laplacian f x))
      have hD := hΔ x hxs
      have heq : c * (2 * (1 - β * δ) * G) = β * G := by rw [← mul_assoc, hcoeff]
      rw [heq] at hmul
      nlinarith only [hmul, hi, hil, hD]
    · intro x hx
      rw [htrace x hx, sub_self, inner_zero_right, htrace_sq x hx]
      ring_nf
      exact le_rfl
  intro x hx
  let w := f x - h x
  let l := NormedSpace.normalize w
  have hl : ‖l‖ ≤ 1 := by
    by_cases hw : w = 0
    · simp [l, hw]
    · exact (NormedSpace.norm_normalize hw).le
  have hi : ⟪l, w⟫_ℝ = ‖w‖ := by
    by_cases hw : w = 0
    · simp [hw]
    · simp [l, NormedSpace.normalize, real_inner_smul_left,
        sq, norm_ne_zero_iff.mpr hw]
  have hhx := hcmp l hl x hx
  change c * ‖f x‖ ^ 2 + ⟪l, w⟫_ℝ - c * H x ≤ 0 at hhx
  rw [hi] at hhx
  change ‖w‖ + c * ‖f x‖ ^ 2 ≤ c * H x
  linarith

end DifferentialGeometry.Analysis
