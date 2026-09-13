import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Gradient
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import DifferentialGeometry.Analysis.Complex.SquareRoot
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

theorem contDiffOn_one_closure_of_sq_gradient_add_eq
    {s : Set ℂ} (hs : Convex ℝ s) (ho : IsOpen s)
    {f : ℂ → ℝ} {a q : ℂ → ℂ}
    (hf : ContinuousOn f (closure s)) (hd : ContDiffOn ℝ 1 f s)
    (ha : ContinuousOn a (closure s)) (hq : ContinuousOn q (closure s))
    (hsq : EqOn (fun y => (gradient f y + a y) ^ 2) q s) :
    ContDiffOn ℝ 1 f (closure s) := by
  have hD : ContinuousOn (fderiv ℝ f) s := by
    intro z hz
    exact ((hd z hz).contDiffAt (ho.mem_nhds hz)).continuousAt_fderiv (by norm_num) |>.continuousWithinAt
  have hg : ContinuousOn (fun y => gradient f y + a y) s :=
    ((toDual ℝ ℂ).symm.continuous.comp_continuousOn hD).add (ha.mono subset_closure)
  obtain ⟨v, hv, he, _⟩ := Complex.exists_continuousOn_extension_of_sq_eq hs hg hq hsq
  let D (z : ℂ) : ℂ →L[ℝ] ℝ := toDual ℝ ℂ (v z - a z)
  have hDc : ContinuousOn D (closure s) := (toDual ℝ ℂ).continuous.comp_continuousOn (hv.sub ha)
  have hDe : EqOn (fderiv ℝ f) D s := by
    intro z hz
    dsimp only [D]
    rw [he hz, add_sub_cancel_right]
    exact ((toDual ℝ ℂ).apply_symm_apply (fderiv ℝ f z)).symm
  have hhas (z : ℂ) (hz : z ∈ closure s) : HasFDerivWithinAt f (D z) (closure s) z := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (hd.differentiableOn (by norm_num)) hs ho
      (fun y hy => (hf y hy).mono subset_closure)
    have hh : Tendsto D (𝓝[s] z) (𝓝 (D z)) := (hDc z hz).mono subset_closure
    apply (tendsto_congr' (show fderiv ℝ f =ᶠ[𝓝[s] z] D from ?_)).mpr hh
    filter_upwards [self_mem_nhdsWithin] with y hy using hDe hy
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt (by simp : (0 : ℕ∞ω) ≠ ∞)]
  intro z hz
  refine ⟨closure s, ?_, by simp, D, hhas, contDiffOn_zero.mpr hDc⟩
  simpa only [insert_eq_of_mem hz] using (self_mem_nhdsWithin : closure s ∈ 𝓝[closure s] z)

private theorem complex_sq_add_eq_of_conformal_pair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : B.toBilinForm.IsSymm)
    (v w t : V) (p q : ℝ) (ht : B t t ≠ 0)
    (horth : B (v + p • t) (w + q • t) = 0)
    (heq : B (v + p • t) (v + p • t) = B (w + q • t) (w + q • t)) :
    ((p : ℂ) + (q : ℂ) * Complex.I +
      ((B v t / B t t : ℝ) : ℂ) + ((B w t / B t t : ℝ) : ℂ) * Complex.I) ^ 2 =
    (((B v t / B t t) ^ 2 - (B w t / B t t) ^ 2 - (B v v - B w w) / B t t : ℝ) : ℂ) +
      ((2 * (B v t / B t t) * (B w t / B t t) - 2 * B v w / B t t : ℝ) : ℂ) * Complex.I := by
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul] at horth heq
  rw [show B t w = B w t from hB.eq t w] at horth
  rw [show B t v = B v t from hB.eq t v,
    show B t w = B w t from hB.eq t w] at heq
  apply Complex.ext <;>
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add, add_zero, sub_zero]
  · field_simp
    nlinarith only [congrArg (fun r : ℝ => r * B t t) heq]
  · field_simp
    nlinarith only [congrArg (fun r : ℝ => r * B t t) horth]

theorem contDiffOn_one_closure_of_conformal_pair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set ℂ} (hs : Convex ℝ s) (ho : IsOpen s)
    {f : ℂ → ℝ} (hf : ContinuousOn f (closure s)) (hd : ContDiffOn ℝ 1 f s)
    {B : ℂ → V →L[ℝ] V →L[ℝ] ℝ} {v w t : ℂ → V}
    (hB : ContinuousOn B (closure s)) (hv : ContinuousOn v (closure s))
    (hw : ContinuousOn w (closure s)) (ht : ContinuousOn t (closure s))
    (hBs : ∀ z ∈ s, (B z).toBilinForm.IsSymm)
    (hBt : ∀ z ∈ closure s, B z (t z) (t z) ≠ 0)
    (horth : ∀ z ∈ s, B z (v z + fderiv ℝ f z 1 • t z)
      (w z + fderiv ℝ f z Complex.I • t z) = 0)
    (heq : ∀ z ∈ s, B z (v z + fderiv ℝ f z 1 • t z)
      (v z + fderiv ℝ f z 1 • t z) = B z (w z + fderiv ℝ f z Complex.I • t z)
      (w z + fderiv ℝ f z Complex.I • t z)) :
    ContDiffOn ℝ 1 f (closure s) := by
  let k (z : ℂ) := B z (t z) (t z)
  let a (z : ℂ) := B z (v z) (t z) / k z
  let b (z : ℂ) := B z (w z) (t z) / k z
  let A (z : ℂ) := (a z : ℂ) + (b z : ℂ) * Complex.I
  let Q (z : ℂ) := ((a z ^ 2 - b z ^ 2 - (B z (v z) (v z) - B z (w z) (w z)) / k z : ℝ) : ℂ) +
    ((2 * a z * b z - 2 * B z (v z) (w z) / k z : ℝ) : ℂ) * Complex.I
  have hkc : ContinuousOn k (closure s) := (hB.clm_apply ht).clm_apply ht
  have hac : ContinuousOn a (closure s) := ((hB.clm_apply hv).clm_apply ht).div hkc hBt
  have hbc : ContinuousOn b (closure s) := ((hB.clm_apply hw).clm_apply ht).div hkc hBt
  have hAc : ContinuousOn A (closure s) :=
    (Complex.continuous_ofReal.comp_continuousOn hac).add
      ((Complex.continuous_ofReal.comp_continuousOn hbc).mul_const _)
  have hQr : ContinuousOn (fun z => a z ^ 2 - b z ^ 2 -
      (B z (v z) (v z) - B z (w z) (w z)) / k z) (closure s) :=
    ((hac.pow 2).sub (hbc.pow 2)).sub
      ((((hB.clm_apply hv).clm_apply hv).sub ((hB.clm_apply hw).clm_apply hw)).div hkc hBt)
  have hQi : ContinuousOn (fun z => 2 * a z * b z - 2 * B z (v z) (w z) / k z) (closure s) :=
    ((hac.const_mul 2).mul hbc).sub ((((hB.clm_apply hv).clm_apply hw).const_mul 2).div hkc hBt)
  have hQc : ContinuousOn Q (closure s) :=
    (Complex.continuous_ofReal.comp_continuousOn hQr).add
      ((Complex.continuous_ofReal.comp_continuousOn hQi).mul_const _)
  apply contDiffOn_one_closure_of_sq_gradient_add_eq hs ho hf hd hAc hQc
  intro z hz
  have hh := complex_sq_add_eq_of_conformal_pair (B z) (hBs z hz)
    (v z) (w z) (t z) (fderiv ℝ f z 1) (fderiv ℝ f z Complex.I)
    (hBt z (subset_closure hz)) (horth z hz) (heq z hz)
  change (gradient f z + A z) ^ 2 = Q z
  dsimp only [A, Q, a, b, k]
  simpa only [← gradient_complex_re, ← gradient_complex_im, Complex.re_add_im, add_assoc] using hh


end DifferentialGeometry.Analysis
