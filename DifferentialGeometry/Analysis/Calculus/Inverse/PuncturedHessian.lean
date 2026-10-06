import DifferentialGeometry.Analysis.Calculus.Inverse.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem norm_second_fderiv_symm_le
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hi : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    {y : ℂ} (hy : y ∈ e.target)
    (he2 : ContDiffAt ℝ 2 (e : ℂ → ℂ) (e.symm y))
    (hi2 : ContDiffAt ℝ 2 (e.symm : ℂ → ℂ) y) :
    ‖fderiv ℝ (fderiv ℝ (e.symm : ℂ → ℂ)) y‖ ≤
      ‖fderiv ℝ (fderiv ℝ (e : ℂ → ℂ)) (e.symm y)‖ *
        ‖fderiv ℝ (e.symm : ℂ → ℂ) y‖ ^ 3 := by
  have hed := (he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt_one
  have hid := (hi.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt_one
  have hDe := ((he2.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt).comp
    y hid.hasFDerivAt
  have hDi := (hi2.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hprod := hDe.clm_comp hDi
  have heq : (fun q : ℂ => (fderiv ℝ (e : ℂ → ℂ) (e.symm q)).comp
      (fderiv ℝ (e.symm : ℂ → ℂ) q)) =ᶠ[𝓝 y]
        fun _ => ContinuousLinearMap.id ℝ ℂ := by
    filter_upwards [e.open_target.mem_nhds hy] with q hq
    exact e.fderiv_comp_symm_eq_id hq
      ((he.contDiffAt (e.open_source.mem_nhds (e.map_target hq))).differentiableAt_one)
      ((hi.contDiffAt (e.open_target.mem_nhds hq)).differentiableAt_one)
  have hzero := (hprod.congr_of_eventuallyEq heq.symm).unique
    (hasFDerivAt_const (ContinuousLinearMap.id ℝ ℂ) y)
  have hleft : (fderiv ℝ (e.symm : ℂ → ℂ) y).comp
      (fderiv ℝ (e : ℂ → ℂ) (e.symm y)) = ContinuousLinearMap.id ℝ ℂ := by
    have hh := e.symm.fderiv_comp_symm_eq_id (e.map_target hy)
      (show DifferentiableAt ℝ (e.symm : ℂ → ℂ) (e (e.symm y)) by
        rw [e.right_inv hy]
        exact hid) hed
    simpa only [e.symm_symm, e.right_inv hy] using hh
  have hcancel (v w : ℂ) :
      fderiv ℝ (fderiv ℝ (e.symm : ℂ → ℂ)) y v w =
        -(fderiv ℝ (e.symm : ℂ → ℂ) y)
          (fderiv ℝ (fderiv ℝ (e : ℂ → ℂ)) (e.symm y)
            (fderiv ℝ (e.symm : ℂ → ℂ) y v)
            (fderiv ℝ (e.symm : ℂ → ℂ) y w)) := by
    have hsum := congrArg (fun L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ => L v w) hzero
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, add_apply, zero_apply] at hsum
    have hh := congrArg (fderiv ℝ (e.symm : ℂ → ℂ) y) hsum
    have hleft_apply (z : ℂ) :
        fderiv ℝ (e.symm : ℂ → ℂ) y
          (fderiv ℝ (e : ℂ → ℂ) (e.symm y) z) = z :=
      congrArg (fun L : ℂ →L[ℝ] ℂ => L z) hleft
    simp only [Function.comp_apply, map_add, map_zero, hleft_apply] at hh
    exact eq_neg_of_add_eq_zero_left hh
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [hcancel, norm_neg]
  let D := fderiv ℝ (e.symm : ℂ → ℂ) y
  let B := fderiv ℝ (fderiv ℝ (e : ℂ → ℂ)) (e.symm y)
  change ‖D (B (D v) (D w))‖ ≤ (‖B‖ * ‖D‖ ^ 3 * ‖v‖) * ‖w‖
  calc
    _ ≤ ‖D‖ * ‖B (D v) (D w)‖ := D.le_opNorm _
    _ ≤ ‖D‖ * (‖B‖ * ‖D v‖ * ‖D w‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm₂ _ _) (norm_nonneg _)
    _ ≤ ‖D‖ * (‖B‖ * (‖D‖ * ‖v‖) * (‖D‖ * ‖w‖)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (D.le_opNorm v) (norm_nonneg _))
        (D.le_opNorm w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- For the supplied coordinate homeomorphism, a bounded punctured forward
Hessian gives a bounded punctured inverse Hessian. The inverse is unchanged,
and no second derivative at the center is assumed in either direction. -/
theorem exists_eventually_norm_second_fderiv_symm_le
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (hea : e a = 0)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hi : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (he2 : ContDiffOn ℝ 2 (e : ℂ → ℂ) (e.source \ {a}))
    (hi2 : ContDiffOn ℝ 2 (e.symm : ℂ → ℂ) (e.target \ {0}))
    (hbound : ∃ C > 0, ∀ᶠ z in 𝓝[≠] a,
      ‖fderiv ℝ (fderiv ℝ (e : ℂ → ℂ)) z‖ ≤ C) :
    ∃ K > 0, ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ (e.symm : ℂ → ℂ)) w‖ ≤ K := by
  obtain ⟨C, hC, hCb⟩ := hbound
  have h0 : (0 : ℂ) ∈ e.target := hea ▸ e.map_source ha
  have hi0 : e.symm 0 = a := by rw [← hea]; exact e.left_inv ha
  have hi1 : ContDiffAt ℝ 1 (e.symm : ℂ → ℂ) 0 :=
    hi.contDiffAt (e.open_target.mem_nhds h0)
  have hneq {w : ℂ} (hw : w ∈ e.target) (hw0 : w ≠ 0) : e.symm w ≠ a := by
    intro h
    apply hw0
    exact (e.right_inv hw).symm.trans ((congrArg e h).trans hea)
  have ht : Tendsto (e.symm : ℂ → ℂ) (𝓝[≠] (0 : ℂ)) (𝓝[≠] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [hi0] using hi1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds h0),
        (self_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ≠ 0)] with w hw hw0
      exact hneq hw hw0
  let D := ‖fderiv ℝ (e.symm : ℂ → ℂ) 0‖ + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hDb : ∀ᶠ w in 𝓝 (0 : ℂ), ‖fderiv ℝ (e.symm : ℂ → ℂ) w‖ ≤ D := by
    have hh : ∀ᶠ w in 𝓝 (0 : ℂ), ‖fderiv ℝ (e.symm : ℂ → ℂ) w‖ < D :=
      (hi1.continuousAt_fderiv one_ne_zero).norm.eventually (gt_mem_nhds (by
        dsimp only [D]
        linarith))
    exact hh.mono fun _ hw => hw.le
  refine ⟨C * D ^ 3, by positivity, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds h0),
    (self_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ≠ 0), ht.eventually hCb,
    hDb.filter_mono nhdsWithin_le_nhds] with w hw hw0 hwC hwD
  have hwe : ContDiffAt ℝ 2 (e : ℂ → ℂ) (e.symm w) :=
    he2.contDiffAt ((e.open_source.sdiff isClosed_singleton).mem_nhds
      ⟨e.map_target hw, hneq hw hw0⟩)
  have hwi : ContDiffAt ℝ 2 (e.symm : ℂ → ℂ) w :=
    hi2.contDiffAt ((e.open_target.sdiff isClosed_singleton).mem_nhds ⟨hw, hw0⟩)
  exact (norm_second_fderiv_symm_le e he hi hw hwe hwi).trans
    (mul_le_mul hwC (pow_le_pow_left₀ (norm_nonneg _) hwD 3)
      (pow_nonneg (norm_nonneg _) 3) hC.le)

end DifferentialGeometry.Analysis
