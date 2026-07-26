import DifferentialGeometry.Analysis.ODE.IndexFormNegative
import DifferentialGeometry.Analysis.Calculus.CutoffProfile
import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

/-!
# Smoothing a negative split index direction

This module smooths a value-matched pair of negative index-form directions
across its interior junction.  The construction stays in the fixed Hilbert
space of the abstract Jacobi ODE.  Its key estimate is first-order: the
`1 / δ` derivative of the transition weight is multiplied by the difference
of the two fields, which is `O(δ)` because their values agree at the junction.
-/

open Set intervalIntegral MeasureTheory
open scoped ContDiff RealInnerProductSpace Topology

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private def scaleCoeff (L : ℝ) (R : ℝ → F →L[ℝ] F) (t : ℝ) : F →L[ℝ] F :=
  L ^ 2 • R (L * t)

private def scaleField (L : ℝ) (W : ℝ → F) (t : ℝ) : F :=
  W (L * t)

private def scaleDeriv (L : ℝ) (V : ℝ → F) (t : ℝ) : F :=
  L • V (L * t)

private theorem indexForm_scale
    (L a b : ℝ) (R : ℝ → F →L[ℝ] F) (W V Z U : ℝ → F) :
    indexForm (scaleCoeff L R) a b
        (scaleField L W) (scaleDeriv L V)
        (scaleField L Z) (scaleDeriv L U) =
      L * indexForm R (L * a) (L * b) W V Z U := by
  unfold indexForm
  have hpoint (t : ℝ) :
      indexIntegrand (scaleCoeff L R)
          (scaleField L W) (scaleDeriv L V)
          (scaleField L Z) (scaleDeriv L U) t =
        L ^ 2 * indexIntegrand R W V Z U (L * t) := by
    simp only [indexIntegrand, scaleCoeff, scaleField, scaleDeriv,
      ContinuousLinearMap.smul_apply, real_inner_smul_left,
      real_inner_smul_right]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  calc
    L ^ 2 * ∫ t in a..b, indexIntegrand R W V Z U (L * t) =
        L * (L * ∫ t in a..b, indexIntegrand R W V Z U (L * t)) := by ring
    _ = L * ∫ t in L * a..L * b, indexIntegrand R W V Z U t := by
      congr 1
      simpa only [smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left
          (f := fun t => indexIntegrand R W V Z U t) (a := a) (b := b) L)

private def splitWeight (c δ t : ℝ) : ℝ :=
  DifferentialGeometry.Analysis.CutoffProfile.value
    (1 + (t - (c - δ)) / (2 * δ))

private def smoothSplice (c δ : ℝ) (W₀ W₁ : ℝ → F) : ℝ → F :=
  fun t =>
    splitWeight c δ t • W₀ t +
      (1 - splitWeight c δ t) • W₁ t

private theorem splitWeight_contDiff {c δ : ℝ} :
    ContDiff ℝ ∞ (splitWeight c δ) := by
  unfold splitWeight
  apply DifferentialGeometry.Analysis.CutoffProfile.contDiff.comp
  fun_prop

private theorem splitWeight_mem {c δ t : ℝ} :
    splitWeight c δ t ∈ Icc (0 : ℝ) 1 :=
  DifferentialGeometry.Analysis.CutoffProfile.mem_Icc _

private theorem splitWeight_one {c δ t : ℝ} (hδ : 0 < δ)
    (ht : t ≤ c - δ) :
    splitWeight c δ t = 1 := by
  apply DifferentialGeometry.Analysis.CutoffProfile.one_of_le_one
  have hquot :
      (t - (c - δ)) / (2 * δ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

private theorem splitWeight_zero {c δ t : ℝ} (hδ : 0 < δ)
    (ht : c + δ ≤ t) :
    splitWeight c δ t = 0 := by
  apply DifferentialGeometry.Analysis.CutoffProfile.zero_of_two_le
  have hquot :
      1 ≤ (t - (c - δ)) / (2 * δ) :=
    (le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr (by linarith)
  linarith

private theorem splitWeight_hasDeriv {c δ t : ℝ} :
    HasDerivAt (splitWeight c δ)
      (deriv DifferentialGeometry.Analysis.CutoffProfile.value
          (1 + (t - (c - δ)) / (2 * δ)) * (1 / (2 * δ))) t := by
  have harg :
      HasDerivAt (fun s : ℝ => 1 + (s - (c - δ)) / (2 * δ))
        (1 / (2 * δ)) t := by
    convert (hasDerivAt_const t 1).add
      (((hasDerivAt_id t).sub_const (c - δ)).div_const (2 * δ)) using 1
    ring
  have hvalue :
      HasDerivAt DifferentialGeometry.Analysis.CutoffProfile.value
        (deriv DifferentialGeometry.Analysis.CutoffProfile.value
          (1 + (t - (c - δ)) / (2 * δ)))
        (1 + (t - (c - δ)) / (2 * δ)) :=
    ((DifferentialGeometry.Analysis.CutoffProfile.contDiff.differentiable
      (by simp)).differentiableAt).hasDerivAt
  simpa only [splitWeight] using hvalue.comp t harg

private theorem splitWeight_deriv {c δ t : ℝ} :
    deriv (splitWeight c δ) t =
      deriv DifferentialGeometry.Analysis.CutoffProfile.value
          (1 + (t - (c - δ)) / (2 * δ)) * (1 / (2 * δ)) :=
  splitWeight_hasDeriv.deriv

private theorem splitWeight_deriv_le
    {c δ Cη t : ℝ} (hδ : 0 < δ)
    (hCη : ∀ s : ℝ,
      |deriv DifferentialGeometry.Analysis.CutoffProfile.value s| ≤ Cη) :
    |deriv (splitWeight c δ) t| ≤ Cη / (2 * δ) := by
  rw [splitWeight_deriv, abs_mul, abs_of_pos
    (by positivity : 0 < (1 / (2 * δ) : ℝ))]
  simpa only [div_eq_mul_inv, one_mul] using
    (mul_le_mul_of_nonneg_right
      (hCη (1 + (t - (c - δ)) / (2 * δ)))
      (by positivity : 0 ≤ (2 * δ)⁻¹))

private theorem splice_contDiff
    {c δ : ℝ} {W₀ W₁ : ℝ → F}
    (hW₀ : ContDiff ℝ ∞ W₀)
    (hW₁ : ContDiff ℝ ∞ W₁) :
    ContDiff ℝ ∞ (smoothSplice c δ W₀ W₁) := by
  unfold smoothSplice
  exact ((splitWeight_contDiff).smul hW₀).add
    ((contDiff_const.sub splitWeight_contDiff).smul hW₁)

private theorem splice_deriv
    {c δ : ℝ} {W₀ W₁ : ℝ → F}
    (hW₀ : ContDiff ℝ ∞ W₀)
    (hW₁ : ContDiff ℝ ∞ W₁)
    (t : ℝ) :
    deriv (smoothSplice c δ W₀ W₁) t =
        splitWeight c δ t • deriv W₀ t
      + (1 - splitWeight c δ t) • deriv W₁ t
      + deriv (splitWeight c δ) t • (W₀ t - W₁ t) := by
  have hη :
      HasDerivAt (splitWeight c δ)
        (deriv (splitWeight c δ) t) t :=
    (splitWeight_contDiff.differentiable (by simp) t).hasDerivAt
  have h₀ : HasDerivAt W₀ (deriv W₀ t) t :=
    (hW₀.differentiable (by simp) t).hasDerivAt
  have h₁ : HasDerivAt W₁ (deriv W₁ t) t :=
    (hW₁.differentiable (by simp) t).hasDerivAt
  have h :=
    (hη.smul h₀).add (((hasDerivAt_const t 1).sub hη).smul h₁)
  change deriv (splitWeight c δ • W₀ +
    ((fun _ : ℝ => (1 : ℝ)) - splitWeight c δ) • W₁) t = _
  rw [h.deriv]
  simp only [Pi.sub_apply]
  module

private theorem splice_eq_left
    {c δ t : ℝ} {W₀ W₁ : ℝ → F}
    (hδ : 0 < δ) (ht : t ≤ c - δ) :
    smoothSplice c δ W₀ W₁ t = W₀ t := by
  unfold smoothSplice
  rw [splitWeight_one hδ ht]
  simp

private theorem splice_eq_right
    {c δ t : ℝ} {W₀ W₁ : ℝ → F}
    (hδ : 0 < δ) (ht : c + δ ≤ t) :
    smoothSplice c δ W₀ W₁ t = W₁ t := by
  unfold smoothSplice
  rw [splitWeight_zero hδ ht]
  simp

private theorem splice_deriv_left
    {c δ t : ℝ} {W₀ W₁ : ℝ → F}
    (hδ : 0 < δ) (ht : t < c - δ) :
    deriv (smoothSplice c δ W₀ W₁) t = deriv W₀ t := by
  have heq : smoothSplice c δ W₀ W₁ =ᶠ[𝓝 t] W₀ := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact splice_eq_left hδ hs.le
  exact heq.deriv_eq

private theorem splice_deriv_right
    {c δ t : ℝ} {W₀ W₁ : ℝ → F}
    (hδ : 0 < δ) (ht : c + δ < t) :
    deriv (smoothSplice c δ W₀ W₁) t = deriv W₁ t := by
  have heq : smoothSplice c δ W₀ W₁ =ᶠ[𝓝 t] W₁ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact splice_eq_right hδ hs.le
  exact heq.deriv_eq

private theorem exists_global_ext
    {A B : ℝ} {W : ℝ → F}
    (hA : A < 0) (hB : 1 < B)
    (hW : ContDiffOn ℝ ∞ W (Ioo A B)) :
    ∃ Wg : ℝ → F,
      ContDiff ℝ ∞ Wg ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Wg t = W t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, deriv Wg t = deriv W t) := by
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo A B := by
    intro t ht
    exact ⟨hA.trans_le ht.1, ht.2.trans_lt hB⟩
  obtain ⟨χ, hχ, -, hχone, hχsupp, -⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact
      isCompact_Icc isOpen_Ioo hsub
  let Wg : ℝ → F := fun t => χ t • W t
  have hWg : ContDiff ℝ ∞ Wg := by
    exact DifferentialGeometry.Analysis.contDiff_cutoff_smul
      isOpen_Ioo hχ hχsupp hW
  refine ⟨Wg, hWg, ?_, ?_⟩
  · intro t ht
    have hχt :
        χ =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) :=
      hχone.filter_mono (nhds_le_nhdsSet ht)
    change χ t • W t = W t
    rw [hχt.self_of_nhds, one_smul]
  · intro t ht
    have hχt :
        χ =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) :=
      hχone.filter_mono (nhds_le_nhdsSet ht)
    have hWgW : Wg =ᶠ[𝓝 t] W := by
      filter_upwards [hχt] with s hs
      change χ s • W s = W s
      rw [hs, one_smul]
    exact hWgW.deriv_eq

private theorem exists_norm_bound
    {G : Type*} [NormedAddCommGroup G]
    {f : ℝ → G}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ C := by
  have hnorm : ContinuousOn (fun t : ℝ => ‖f t‖) (Icc (0 : ℝ) 1) :=
    continuous_norm.comp_continuousOn hf
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hnorm
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hC ⟨t, ht, rfl⟩).trans (le_max_left _ _)

private theorem deriv_continuous {W : ℝ → F}
    (hW : ContDiff ℝ ∞ W) :
    Continuous (deriv W) :=
  (hW.of_le (by simp)).continuous_deriv_one

private theorem int_index_self
    {R : ℝ → F →L[ℝ] F} {W : ℝ → F} {a b : ℝ}
    (hR : ContinuousOn R (Icc (0 : ℝ) 1))
    (hW : ContDiff ℝ ∞ W)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (indexIntegrand R W (deriv W) W (deriv W)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact ((deriv_continuous hW).continuousOn.inner
      (deriv_continuous hW).continuousOn).sub
    (((hR.mono (uIcc_subset_Icc ha hb)).clm_apply
      hW.continuous.continuousOn).inner hW.continuous.continuousOn)

private theorem index_splice_left
    {R : ℝ → F →L[ℝ] F} {c δ : ℝ} {W₀ W₁ : ℝ → F}
    (hδ : 0 < δ) (hδc : δ < min c (1 - c)) :
    indexForm R 0 (c - δ)
        (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
        (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) =
      indexForm R 0 (c - δ) W₀ (deriv W₀) W₀ (deriv W₀) := by
  unfold indexForm
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards
    [MeasureTheory.Measure.ae_ne MeasureTheory.volume (c - δ)] with t htne ht
  have h0le : (0 : ℝ) ≤ c - δ := by
    have hδltc : δ < c := hδc.trans_le (min_le_left _ _)
    linarith
  rw [uIoc_of_le h0le] at ht
  have htlt : t < c - δ := lt_of_le_of_ne ht.2 htne
  unfold indexIntegrand
  rw [splice_eq_left hδ htlt.le,
    splice_deriv_left hδ htlt]

private theorem index_splice_right
    {R : ℝ → F →L[ℝ] F} {c δ : ℝ} {W₀ W₁ : ℝ → F}
    (hδ : 0 < δ) (hδc : δ < min c (1 - c)) :
    indexForm R (c + δ) 1
        (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
        (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) =
      indexForm R (c + δ) 1 W₁ (deriv W₁) W₁ (deriv W₁) := by
  unfold indexForm
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards
    [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with t _ ht
  have hle1 : c + δ ≤ (1 : ℝ) := by
    have hδlt1c : δ < 1 - c := hδc.trans_le (min_le_right _ _)
    linarith
  rw [uIoc_of_le hle1] at ht
  unfold indexIntegrand
  rw [splice_eq_right hδ ht.1.le,
    splice_deriv_right hδ ht.1]

private theorem integrand_abs_le
    {R : ℝ → F →L[ℝ] F} {W V : ℝ → F}
    {KR KW KV t : ℝ}
    (hKR : 0 ≤ KR) (hKW : 0 ≤ KW) (hKV : 0 ≤ KV)
    (hRt : ‖R t‖ ≤ KR) (hWt : ‖W t‖ ≤ KW) (hVt : ‖V t‖ ≤ KV) :
    |indexIntegrand R W V W V t| ≤ KV ^ 2 + KR * KW ^ 2 := by
  have hRW : ‖R t (W t)‖ ≤ KR * KW :=
    ((R t).le_opNorm (W t)).trans
      (mul_le_mul hRt hWt (norm_nonneg _) hKR)
  have hVV : ‖V t‖ * ‖V t‖ ≤ KV * KV := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hVt)
      (add_nonneg hKV (norm_nonneg (V t)))]
  have hRWW : ‖R t (W t)‖ * ‖W t‖ ≤ (KR * KW) * KW :=
    mul_le_mul hRW hWt (norm_nonneg _) (mul_nonneg hKR hKW)
  unfold indexIntegrand
  calc
    |⟪V t, V t⟫ - ⟪R t (W t), W t⟫|
        ≤ |⟪V t, V t⟫| + |⟪R t (W t), W t⟫| := abs_sub _ _
    _ ≤ ‖V t‖ * ‖V t‖ + ‖R t (W t)‖ * ‖W t‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ KV * KV + (KR * KW) * KW := add_le_add hVV hRWW
    _ = KV ^ 2 + KR * KW ^ 2 := by ring

private theorem index_abs_le
    {R : ℝ → F →L[ℝ] F} {W V : ℝ → F}
    {a b KR KW KV : ℝ}
    (hKR : 0 ≤ KR) (hKW : 0 ≤ KW) (hKV : 0 ≤ KV)
    (hR : ∀ t ∈ uIcc a b, ‖R t‖ ≤ KR)
    (hW : ∀ t ∈ uIcc a b, ‖W t‖ ≤ KW)
    (hV : ∀ t ∈ uIcc a b, ‖V t‖ ≤ KV) :
    |indexForm R a b W V W V| ≤
      (KV ^ 2 + KR * KW ^ 2) * |b - a| := by
  unfold indexForm
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := indexIntegrand R W V W V)
      (C := KV ^ 2 + KR * KW ^ 2)
      (fun t ht => by
        simpa only [Real.norm_eq_abs] using
          integrand_abs_le hKR hKW hKV
          (hR t (uIoc_subset_uIcc ht))
          (hW t (uIoc_subset_uIcc ht))
          (hV t (uIoc_subset_uIcc ht)))
  simpa only [Real.norm_eq_abs] using hbound

private theorem splice_norm_le
    {c δ N₀ N₁ t : ℝ} {W₀ W₁ : ℝ → F}
    (hN₀ : 0 ≤ N₀) (hN₁ : 0 ≤ N₁)
    (hW₀ : ‖W₀ t‖ ≤ N₀) (hW₁ : ‖W₁ t‖ ≤ N₁) :
    ‖smoothSplice c δ W₀ W₁ t‖ ≤ N₀ + N₁ := by
  have hη := splitWeight_mem (c := c) (δ := δ) (t := t)
  unfold smoothSplice
  calc
    ‖splitWeight c δ t • W₀ t + (1 - splitWeight c δ t) • W₁ t‖
        ≤ ‖splitWeight c δ t • W₀ t‖
            + ‖(1 - splitWeight c δ t) • W₁ t‖ := norm_add_le _ _
    _ = splitWeight c δ t * ‖W₀ t‖
          + (1 - splitWeight c δ t) * ‖W₁ t‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη.1,
        abs_of_nonneg (sub_nonneg.mpr hη.2)]
    _ ≤ N₀ + N₁ := by
      have hleft :
          splitWeight c δ t * ‖W₀ t‖ ≤ N₀ :=
        (mul_le_mul_of_nonneg_left hW₀ hη.1).trans
          (mul_le_of_le_one_left hN₀ hη.2)
      have hright :
          (1 - splitWeight c δ t) * ‖W₁ t‖ ≤ N₁ :=
        (mul_le_mul_of_nonneg_left hW₁ (sub_nonneg.mpr hη.2)).trans
          (mul_le_of_le_one_left hN₁ (by linarith [hη.1]))
      linarith

private theorem splice_diff_le
    {c δ M₀ M₁ t : ℝ} {W₀ W₁ : ℝ → F}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hδc : δ < min c (1 - c))
    (hW₀ : ContDiff ℝ ∞ W₀)
    (hW₁ : ContDiff ℝ ∞ W₁)
    (hM₀ : ∀ s ∈ Icc (0 : ℝ) 1, ‖deriv W₀ s‖ ≤ M₀)
    (hM₁ : ∀ s ∈ Icc (0 : ℝ) 1, ‖deriv W₁ s‖ ≤ M₁)
    (hmatch : W₀ c = W₁ c)
    (ht : t ∈ Icc (c - δ) (c + δ)) :
    ‖W₀ t - W₁ t‖ ≤ (M₀ + M₁) * δ := by
  have hδltc : δ < c := hδc.trans_le (min_le_left _ _)
  have hδlt1c : δ < 1 - c := hδc.trans_le (min_le_right _ _)
  have ht01 : t ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hc01 : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
  have hdiff₀ :
      ‖W₀ t - W₀ c‖ ≤ M₀ * ‖t - c‖ :=
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun s _ => hW₀.differentiable (by simp) s)
      hM₀ hc01 ht01
  have hdiff₁ :
      ‖W₁ c - W₁ t‖ ≤ M₁ * ‖c - t‖ :=
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun s _ => hW₁.differentiable (by simp) s)
      hM₁ ht01 hc01
  have htc : ‖t - c‖ ≤ δ := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hct : ‖c - t‖ ≤ δ := by
    calc
      ‖c - t‖ = ‖-(t - c)‖ := by congr 1; ring
      _ = ‖t - c‖ := norm_neg _
      _ ≤ δ := htc
  calc
    ‖W₀ t - W₁ t‖ =
        ‖(W₀ t - W₀ c) + (W₁ c - W₁ t)‖ := by
          rw [hmatch]
          congr 1
          abel
    _ ≤ ‖W₀ t - W₀ c‖ + ‖W₁ c - W₁ t‖ := norm_add_le _ _
    _ ≤ M₀ * ‖t - c‖ + M₁ * ‖c - t‖ :=
      add_le_add hdiff₀ hdiff₁
    _ ≤ M₀ * δ + M₁ * δ := by
      gcongr
      · exact (norm_nonneg _).trans (hM₀ c hc01)
      · exact (norm_nonneg _).trans (hM₁ c hc01)
    _ = (M₀ + M₁) * δ := by ring

private theorem exists_deriv_bound
    {c : ℝ} {W₀ W₁ : ℝ → F}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hW₀ : ContDiff ℝ ∞ W₀)
    (hW₁ : ContDiff ℝ ∞ W₁)
    (hmatch : W₀ c = W₁ c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ < min c (1 - c) →
        ∀ t ∈ Icc (c - δ) (c + δ),
          ‖deriv (smoothSplice c δ W₀ W₁) t‖ ≤ C := by
  obtain ⟨Cη, hCη, hη, -⟩ :=
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds
  obtain ⟨M₀, hM₀, hM₀bound⟩ :=
    exists_norm_bound (deriv_continuous hW₀).continuousOn
  obtain ⟨M₁, hM₁, hM₁bound⟩ :=
    exists_norm_bound (deriv_continuous hW₁).continuousOn
  let M : ℝ := M₀ + M₁
  let C : ℝ := (Cη + 1) * M
  have hM : 0 ≤ M := add_nonneg hM₀ hM₁
  have hC : 0 ≤ C := mul_nonneg (by linarith) hM
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδc t ht
  have hηmem := splitWeight_mem (c := c) (δ := δ) (t := t)
  have hdiff :
      ‖W₀ t - W₁ t‖ ≤ M * δ := by
    simpa only [M] using
      splice_diff_le hc hδc hW₀ hW₁ hM₀bound hM₁bound hmatch ht
  have hηderiv :
      |deriv (splitWeight c δ) t| ≤ Cη / (2 * δ) :=
    splitWeight_deriv_le hδ hη
  have hcross :
      |deriv (splitWeight c δ) t| * ‖W₀ t - W₁ t‖ ≤ Cη * M := by
    calc
      |deriv (splitWeight c δ) t| * ‖W₀ t - W₁ t‖
          ≤ (Cη / (2 * δ)) * (M * δ) := by
            exact mul_le_mul hηderiv hdiff (norm_nonneg _)
              (div_nonneg hCη (by positivity))
      _ = Cη * M / 2 := by field_simp [hδ.ne']
      _ ≤ Cη * M := by nlinarith [mul_nonneg hCη hM]
  rw [splice_deriv hW₀ hW₁]
  calc
    ‖splitWeight c δ t • deriv W₀ t
        + (1 - splitWeight c δ t) • deriv W₁ t
        + deriv (splitWeight c δ) t • (W₀ t - W₁ t)‖
      ≤ ‖splitWeight c δ t • deriv W₀ t‖
          + ‖(1 - splitWeight c δ t) • deriv W₁ t‖
          + ‖deriv (splitWeight c δ) t • (W₀ t - W₁ t)‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) le_rfl)
    _ = |splitWeight c δ t| * ‖deriv W₀ t‖
          + |1 - splitWeight c δ t| * ‖deriv W₁ t‖
          + |deriv (splitWeight c δ) t| * ‖W₀ t - W₁ t‖ := by
            simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ M₀ + M₁ + Cη * M := by
      have ht01 : t ∈ Icc (0 : ℝ) 1 := by
        have hδltc : δ < c := hδc.trans_le (min_le_left _ _)
        have hδlt1c : δ < 1 - c := hδc.trans_le (min_le_right _ _)
        constructor <;> linarith [ht.1, ht.2]
      have hηabs : |splitWeight c δ t| = splitWeight c δ t :=
        abs_of_nonneg hηmem.1
      have h1ηabs :
          |1 - splitWeight c δ t| = 1 - splitWeight c δ t :=
        abs_of_nonneg (sub_nonneg.mpr hηmem.2)
      rw [hηabs, h1ηabs]
      have hleft :
          splitWeight c δ t * ‖deriv W₀ t‖ ≤ M₀ :=
        (mul_le_mul_of_nonneg_left (hM₀bound t ht01) hηmem.1).trans
          (mul_le_of_le_one_left hM₀ hηmem.2)
      have hright :
          (1 - splitWeight c δ t) * ‖deriv W₁ t‖ ≤ M₁ := by
        refine (mul_le_mul_of_nonneg_left (hM₁bound t ht01)
          (sub_nonneg.mpr hηmem.2)).trans ?_
        exact mul_le_of_le_one_left hM₁ (by linarith [hηmem.1])
      linarith
    _ = C := by simp only [C, M]; ring

private theorem exists_splice_error
    {R : ℝ → F →L[ℝ] F} {c : ℝ} {W₀ W₁ : ℝ → F}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hR : ContinuousOn R (Icc (0 : ℝ) 1))
    (hW₀ : ContDiff ℝ ∞ W₀)
    (hW₁ : ContDiff ℝ ∞ W₁)
    (hmatch : W₀ c = W₁ c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ < min c (1 - c) →
        |indexForm R 0 1
              (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
              (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) -
            (indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) +
              indexForm R c 1 W₁ (deriv W₁) W₁ (deriv W₁))| ≤ C * δ := by
  obtain ⟨KR, hKR, hRbound⟩ := exists_norm_bound hR
  obtain ⟨N₀, hN₀, hN₀bound⟩ :=
    exists_norm_bound hW₀.continuous.continuousOn
  obtain ⟨N₁, hN₁, hN₁bound⟩ :=
    exists_norm_bound hW₁.continuous.continuousOn
  obtain ⟨M₀, hM₀, hM₀bound⟩ :=
    exists_norm_bound (deriv_continuous hW₀).continuousOn
  obtain ⟨M₁, hM₁, hM₁bound⟩ :=
    exists_norm_bound (deriv_continuous hW₁).continuousOn
  obtain ⟨D, hD, hDbound⟩ :=
    exists_deriv_bound hc hW₀ hW₁ hmatch
  let Csp : ℝ := D ^ 2 + KR * (N₀ + N₁) ^ 2
  let C₀ : ℝ := M₀ ^ 2 + KR * N₀ ^ 2
  let C₁ : ℝ := M₁ ^ 2 + KR * N₁ ^ 2
  let C : ℝ := 2 * Csp + C₀ + C₁
  have hCsp : 0 ≤ Csp := by
    dsimp [Csp]
    positivity
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδc
  have hδltc : δ < c := hδc.trans_le (min_le_left _ _)
  have hδlt1c : δ < 1 - c := hδc.trans_le (min_le_right _ _)
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
  have hlI : c - δ ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hrI : c + δ ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hlr : c - δ ≤ c + δ := by linarith
  have hWsp :
      ContDiff ℝ ∞ (smoothSplice c δ W₀ W₁) :=
    splice_contDiff hW₀ hW₁
  have hsp :
      |indexForm R (c - δ) (c + δ)
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))| ≤
        Csp * (2 * δ) := by
    have hraw := index_abs_le
      (R := R)
      (W := smoothSplice c δ W₀ W₁)
      (V := deriv (smoothSplice c δ W₀ W₁))
      (a := c - δ) (b := c + δ)
      hKR (add_nonneg hN₀ hN₁) hD
      (fun t ht => hRbound t (uIcc_subset_Icc hlI hrI ht))
      (fun t ht =>
        splice_norm_le hN₀ hN₁
          (hN₀bound t (uIcc_subset_Icc hlI hrI ht))
          (hN₁bound t (uIcc_subset_Icc hlI hrI ht)))
      (fun t ht => hDbound δ hδ hδc t (by
        simpa only [uIcc_of_le hlr] using ht))
    calc
      |indexForm R (c - δ) (c + δ)
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))|
          ≤ Csp * |(c + δ) - (c - δ)| := by
            simpa only [Csp] using hraw
      _ = Csp * (2 * δ) := by
        rw [abs_of_pos (by linarith : 0 < (c + δ) - (c - δ))]
        ring
  have hleft :
      |indexForm R (c - δ) c W₀ (deriv W₀) W₀ (deriv W₀)| ≤
        C₀ * δ := by
    have hraw := index_abs_le
      (R := R) (W := W₀) (V := deriv W₀)
      (a := c - δ) (b := c)
      hKR hN₀ hM₀
      (fun t ht => hRbound t (uIcc_subset_Icc hlI hcI ht))
      (fun t ht => hN₀bound t (uIcc_subset_Icc hlI hcI ht))
      (fun t ht => hM₀bound t (uIcc_subset_Icc hlI hcI ht))
    calc
      |indexForm R (c - δ) c W₀ (deriv W₀) W₀ (deriv W₀)|
          ≤ C₀ * |c - (c - δ)| := by
            simpa only [C₀] using hraw
      _ = C₀ * δ := by
        rw [abs_of_pos (by linarith : 0 < c - (c - δ))]
        ring
  have hright :
      |indexForm R c (c + δ) W₁ (deriv W₁) W₁ (deriv W₁)| ≤
        C₁ * δ := by
    have hraw := index_abs_le
      (R := R) (W := W₁) (V := deriv W₁)
      (a := c) (b := c + δ)
      hKR hN₁ hM₁
      (fun t ht => hRbound t (uIcc_subset_Icc hcI hrI ht))
      (fun t ht => hN₁bound t (uIcc_subset_Icc hcI hrI ht))
      (fun t ht => hM₁bound t (uIcc_subset_Icc hcI hrI ht))
    calc
      |indexForm R c (c + δ) W₁ (deriv W₁) W₁ (deriv W₁)|
          ≤ C₁ * |(c + δ) - c| := by
            simpa only [C₁] using hraw
      _ = C₁ * δ := by
        rw [abs_of_pos (by linarith : 0 < (c + δ) - c)]
        ring
  have hS0l := int_index_self hR hWsp h0I hlI
  have hSlr := int_index_self hR hWsp hlI hrI
  have hS0r := int_index_self hR hWsp h0I hrI
  have hSr1 := int_index_self hR hWsp hrI h1I
  have hSsplit₀ :
      indexForm R 0 (c - δ)
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) +
        indexForm R (c - δ) (c + δ)
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) =
        indexForm R 0 (c + δ)
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) :=
    intervalIntegral.integral_add_adjacent_intervals hS0l hSlr
  have hSsplit₁ :
      indexForm R 0 (c + δ)
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) +
        indexForm R (c + δ) 1
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) =
        indexForm R 0 1
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) :=
    intervalIntegral.integral_add_adjacent_intervals hS0r hSr1
  have hSdecomp :
      indexForm R 0 1
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) =
        indexForm R 0 (c - δ)
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) +
          indexForm R (c - δ) (c + δ)
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) +
          indexForm R (c + δ) 1
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) := by
    linarith
  have hW₀0l := int_index_self hR hW₀ h0I hlI
  have hW₀lc := int_index_self hR hW₀ hlI hcI
  have hW₁cr := int_index_self hR hW₁ hcI hrI
  have hW₁r1 := int_index_self hR hW₁ hrI h1I
  have hW₀decomp :
      indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) =
        indexForm R 0 (c - δ) W₀ (deriv W₀) W₀ (deriv W₀) +
          indexForm R (c - δ) c W₀ (deriv W₀) W₀ (deriv W₀) := by
    have h :=
      intervalIntegral.integral_add_adjacent_intervals hW₀0l hW₀lc
    exact h.symm
  have hW₁decomp :
      indexForm R c 1 W₁ (deriv W₁) W₁ (deriv W₁) =
        indexForm R c (c + δ) W₁ (deriv W₁) W₁ (deriv W₁) +
          indexForm R (c + δ) 1 W₁ (deriv W₁) W₁ (deriv W₁) := by
    have h :=
      intervalIntegral.integral_add_adjacent_intervals hW₁cr hW₁r1
    exact h.symm
  have herr :
      indexForm R 0 1
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) -
          (indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) +
            indexForm R c 1 W₁ (deriv W₁) W₁ (deriv W₁)) =
        indexForm R (c - δ) (c + δ)
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
            (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) -
          (indexForm R (c - δ) c W₀ (deriv W₀) W₀ (deriv W₀) +
            indexForm R c (c + δ) W₁ (deriv W₁) W₁ (deriv W₁)) := by
    rw [hSdecomp, hW₀decomp, hW₁decomp,
      index_splice_left hδ hδc,
      index_splice_right hδ hδc]
    ring
  rw [herr]
  calc
    |indexForm R (c - δ) (c + δ)
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
          (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁)) -
        (indexForm R (c - δ) c W₀ (deriv W₀) W₀ (deriv W₀) +
          indexForm R c (c + δ) W₁ (deriv W₁) W₁ (deriv W₁))|
        ≤ |indexForm R (c - δ) (c + δ)
              (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
              (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))| +
            |indexForm R (c - δ) c W₀ (deriv W₀) W₀ (deriv W₀) +
              indexForm R c (c + δ) W₁ (deriv W₁) W₁ (deriv W₁)| :=
          abs_sub _ _
    _ ≤ |indexForm R (c - δ) (c + δ)
              (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))
              (smoothSplice c δ W₀ W₁) (deriv (smoothSplice c δ W₀ W₁))| +
            (|indexForm R (c - δ) c W₀ (deriv W₀) W₀ (deriv W₀)| +
              |indexForm R c (c + δ) W₁ (deriv W₁) W₁ (deriv W₁)|) := by
          gcongr
          exact abs_add_le _ _
    _ ≤ Csp * (2 * δ) + (C₀ * δ + C₁ * δ) := by
          gcongr
    _ = C * δ := by
      simp only [C]
      ring

/-- A value-matched pair of locally smooth split fields with negative total
index can be smoothed across the junction without losing negativity. -/
theorem exists_smooth_indexForm_neg_of_split
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {R : ℝ → F →L[ℝ] F}
    {A B c : ℝ} {W₀ W₁ : ℝ → F}
    (hA : A < 0) (hB : 1 < B)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hR : ContinuousOn R (Set.Icc (0 : ℝ) 1))
    (hW₀ : ContDiffOn ℝ ∞ W₀ (Set.Ioo A B))
    (hW₁ : ContDiffOn ℝ ∞ W₁ (Set.Ioo A B))
    (hW₀_zero : W₀ 0 = 0)
    (hW₁_zero : W₁ 1 = 0)
    (hmatch : W₀ c = W₁ c)
    (hneg :
      indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) +
          indexForm R c 1 W₁ (deriv W₁) W₁ (deriv W₁) < 0) :
    ∃ W : ℝ → F,
      ContDiff ℝ ∞ W ∧
      W 0 = 0 ∧
      W 1 = 0 ∧
      indexForm R 0 1 W (deriv W) W (deriv W) < 0 := by
  obtain ⟨W₀g, hW₀g, hW₀val, hW₀deriv⟩ :=
    exists_global_ext hA hB hW₀
  obtain ⟨W₁g, hW₁g, hW₁val, hW₁deriv⟩ :=
    exists_global_ext hA hB hW₁
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
  have hW₀g_zero : W₀g 0 = 0 :=
    (hW₀val 0 h0I).trans hW₀_zero
  have hW₁g_zero : W₁g 1 = 0 :=
    (hW₁val 1 h1I).trans hW₁_zero
  have hmatchg : W₀g c = W₁g c := by
    rw [hW₀val c hcI, hW₁val c hcI]
    exact hmatch
  have hindex₀ :
      indexForm R 0 c W₀g (deriv W₀g) W₀g (deriv W₀g) =
        indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) := by
    unfold indexForm
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht01 : t ∈ Icc (0 : ℝ) 1 :=
      uIcc_subset_Icc h0I hcI ht
    unfold indexIntegrand
    rw [hW₀val t ht01, hW₀deriv t ht01]
  have hindex₁ :
      indexForm R c 1 W₁g (deriv W₁g) W₁g (deriv W₁g) =
        indexForm R c 1 W₁ (deriv W₁) W₁ (deriv W₁) := by
    unfold indexForm
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht01 : t ∈ Icc (0 : ℝ) 1 :=
      uIcc_subset_Icc hcI h1I ht
    unfold indexIntegrand
    rw [hW₁val t ht01, hW₁deriv t ht01]
  have hnegg :
      indexForm R 0 c W₀g (deriv W₀g) W₀g (deriv W₀g) +
          indexForm R c 1 W₁g (deriv W₁g) W₁g (deriv W₁g) < 0 := by
    rw [hindex₀, hindex₁]
    exact hneg
  obtain ⟨C, hC, herror⟩ :=
    exists_splice_error hc hR hW₀g hW₁g hmatchg
  let S : ℝ :=
    indexForm R 0 c W₀g (deriv W₀g) W₀g (deriv W₀g) +
      indexForm R c 1 W₁g (deriv W₁g) W₁g (deriv W₁g)
  have hS : S < 0 := by
    simpa only [S] using hnegg
  obtain ⟨ε, hε, hCε⟩ :=
    exists_pos_mul_lt (neg_pos.mpr hS) C
  have hminc : 0 < min c (1 - c) := by
    exact lt_min hc.1 (by linarith [hc.2])
  have hmin : 0 < min ε (min c (1 - c)) :=
    lt_min hε hminc
  obtain ⟨δ, hδ, hδmin⟩ := exists_between hmin
  have hδε : δ < ε :=
    hδmin.trans_le (min_le_left _ _)
  have hδc : δ < min c (1 - c) :=
    hδmin.trans_le (min_le_right _ _)
  have hCδ : C * δ < -S :=
    (mul_le_mul_of_nonneg_left hδε.le hC).trans_lt hCε
  have herr := herror δ hδ hδc
  have hfinal :
      indexForm R 0 1
          (smoothSplice c δ W₀g W₁g) (deriv (smoothSplice c δ W₀g W₁g))
          (smoothSplice c δ W₀g W₁g) (deriv (smoothSplice c δ W₀g W₁g)) < 0 := by
    have hle :
        indexForm R 0 1
              (smoothSplice c δ W₀g W₁g) (deriv (smoothSplice c δ W₀g W₁g))
              (smoothSplice c δ W₀g W₁g) (deriv (smoothSplice c δ W₀g W₁g)) -
            S ≤
          |indexForm R 0 1
                (smoothSplice c δ W₀g W₁g) (deriv (smoothSplice c δ W₀g W₁g))
                (smoothSplice c δ W₀g W₁g) (deriv (smoothSplice c δ W₀g W₁g)) -
              S| :=
      le_abs_self _
    have herrS :
        |indexForm R 0 1
              (smoothSplice c δ W₀g W₁g) (deriv (smoothSplice c δ W₀g W₁g))
              (smoothSplice c δ W₀g W₁g) (deriv (smoothSplice c δ W₀g W₁g)) -
            S| ≤ C * δ := by
      simpa only [S] using herr
    linarith
  refine ⟨smoothSplice c δ W₀g W₁g,
    splice_contDiff hW₀g hW₁g, ?_, ?_, hfinal⟩
  · rw [splice_eq_left hδ (by
      have hδltc : δ < c := hδc.trans_le (min_le_left _ _)
      linarith)]
    exact hW₀g_zero
  · rw [splice_eq_right hδ (by
      have hδlt1c : δ < 1 - c := hδc.trans_le (min_le_right _ _)
      linarith)]
    exact hW₁g_zero

private theorem smooth_split_to
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {R : ℝ → F →L[ℝ] F}
    {L c : ℝ} {W₀ W₁ : ℝ → F}
    (hL : 0 < L)
    (hc : c ∈ Ioo (0 : ℝ) L)
    (hR : ContinuousOn R (Icc (0 : ℝ) L))
    (hW₀ : ContDiff ℝ ∞ W₀)
    (hW₁ : ContDiff ℝ ∞ W₁)
    (hW₀_zero : W₀ 0 = 0)
    (hW₁_zero : W₁ L = 0)
    (hmatch : W₀ c = W₁ c)
    (hneg :
      indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) +
          indexForm R c L W₁ (deriv W₁) W₁ (deriv W₁) < 0) :
    ∃ W : ℝ → F,
      ContDiff ℝ ∞ W ∧
      W 0 = 0 ∧
      W L = 0 ∧
      indexForm R 0 L W (deriv W) W (deriv W) < 0 := by
  let R₁ : ℝ → F →L[ℝ] F := scaleCoeff L R
  let W₀₁ : ℝ → F := scaleField L W₀
  let W₁₁ : ℝ → F := scaleField L W₁
  have hLne : L ≠ 0 := hL.ne'
  have hc₁ : c / L ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hc.1 hL
    · exact (div_lt_one hL).mpr hc.2
  have hmap : MapsTo (fun t : ℝ => L * t) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) L) := by
    intro t ht
    constructor
    · exact mul_nonneg hL.le ht.1
    · calc
        L * t ≤ L * 1 := mul_le_mul_of_nonneg_left ht.2 hL.le
        _ = L := mul_one L
  have hR₁ : ContinuousOn R₁ (Icc (0 : ℝ) 1) := by
    exact ContinuousOn.smul continuousOn_const
      (hR.comp (continuous_const.mul continuous_id).continuousOn hmap)
  have hW₀₁ : ContDiff ℝ ∞ W₀₁ := by
    exact hW₀.comp (contDiff_const.mul contDiff_id)
  have hW₁₁ : ContDiff ℝ ∞ W₁₁ := by
    exact hW₁.comp (contDiff_const.mul contDiff_id)
  have scale_deriv
      (W : ℝ → F) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
      deriv (scaleField L W) t = scaleDeriv L (deriv W) t := by
    have houter :
        HasDerivAt W (deriv W (L * t)) (L * t) :=
      (hW.differentiable (by simp)).differentiableAt.hasDerivAt
    have hinner : HasDerivAt (fun s : ℝ => L * s) L t :=
      hasDerivAt_const_mul L
    simpa only [scaleField, scaleDeriv] using
      (houter.scomp t hinner).deriv
  have hdW₀₁ : deriv W₀₁ = scaleDeriv L (deriv W₀) := by
    funext t
    exact scale_deriv W₀ hW₀ t
  have hdW₁₁ : deriv W₁₁ = scaleDeriv L (deriv W₁) := by
    funext t
    exact scale_deriv W₁ hW₁ t
  have hLc : L * (c / L) = c := by
    field_simp
  have hindex₀ :
      indexForm R₁ 0 (c / L) W₀₁ (deriv W₀₁) W₀₁ (deriv W₀₁) =
        L * indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) := by
    rw [hdW₀₁]
    simpa only [R₁, W₀₁, mul_zero, hLc] using
      indexForm_scale L 0 (c / L) R W₀ (deriv W₀) W₀ (deriv W₀)
  have hindex₁ :
      indexForm R₁ (c / L) 1 W₁₁ (deriv W₁₁) W₁₁ (deriv W₁₁) =
        L * indexForm R c L W₁ (deriv W₁) W₁ (deriv W₁) := by
    rw [hdW₁₁]
    simpa only [R₁, W₁₁, hLc, mul_one] using
      indexForm_scale L (c / L) 1 R W₁ (deriv W₁) W₁ (deriv W₁)
  have hneg₁ :
      indexForm R₁ 0 (c / L) W₀₁ (deriv W₀₁) W₀₁ (deriv W₀₁) +
          indexForm R₁ (c / L) 1 W₁₁ (deriv W₁₁) W₁₁ (deriv W₁₁) < 0 := by
    rw [hindex₀, hindex₁]
    nlinarith [mul_neg_of_pos_of_neg hL hneg]
  have hW₀₁_zero : W₀₁ 0 = 0 := by
    simpa only [W₀₁, scaleField, mul_zero] using hW₀_zero
  have hW₁₁_zero : W₁₁ 1 = 0 := by
    simpa only [W₁₁, scaleField, mul_one] using hW₁_zero
  have hmatch₁ : W₀₁ (c / L) = W₁₁ (c / L) := by
    simpa only [W₀₁, W₁₁, scaleField, hLc] using hmatch
  obtain ⟨W₁, hW₁, hW₁_zero, hW₁_one, hW₁_neg⟩ :=
    exists_smooth_indexForm_neg_of_split
      (A := -1) (B := 2) (c := c / L)
      (W₀ := W₀₁) (W₁ := W₁₁)
      (by norm_num) (by norm_num) hc₁ hR₁
      hW₀₁.contDiffOn hW₁₁.contDiffOn
      hW₀₁_zero hW₁₁_zero hmatch₁ hneg₁
  let W : ℝ → F := scaleField L⁻¹ W₁
  have hW : ContDiff ℝ ∞ W := by
    exact hW₁.comp (contDiff_const.mul contDiff_id)
  have back_deriv (t : ℝ) :
      deriv W t = scaleDeriv L⁻¹ (deriv W₁) t := by
    have houter :
        HasDerivAt W₁ (deriv W₁ (L⁻¹ * t)) (L⁻¹ * t) :=
      (hW₁.differentiable (by simp)).differentiableAt.hasDerivAt
    have hinner : HasDerivAt (fun s : ℝ => L⁻¹ * s) L⁻¹ t :=
      hasDerivAt_const_mul L⁻¹
    simpa only [W, scaleField, scaleDeriv] using
      (houter.scomp t hinner).deriv
  have hfield : scaleField L W = W₁ := by
    funext t
    simp [scaleField, W, hLne]
  have hderiv : scaleDeriv L (deriv W) = deriv W₁ := by
    funext t
    simp [scaleDeriv, back_deriv, smul_smul, hLne]
  have hindex :
      indexForm R₁ 0 1 W₁ (deriv W₁) W₁ (deriv W₁) =
        L * indexForm R 0 L W (deriv W) W (deriv W) := by
    simpa only [R₁, mul_zero, mul_one, hfield, hderiv] using
      indexForm_scale L 0 1 R W (deriv W) W (deriv W)
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · simpa only [W, scaleField, mul_zero] using hW₁_zero
  · have hback : L⁻¹ * L = 1 := inv_mul_cancel₀ hLne
    simpa only [W, scaleField, hback] using hW₁_one
  · have hmul_neg :
        L * indexForm R 0 L W (deriv W) W (deriv W) < 0 := by
      rwa [← hindex]
    exact lt_of_mul_lt_mul_left (by simpa using hmul_neg) hL.le

/-- A Jacobi solution on `[0, L]` whose position field is globally smooth
produces a globally smooth endpoint-vanishing field with negative index. -/
theorem IsJacobiSolOn.exists_smooth_neg_on
    [CompleteSpace F]
    {R : ℝ → F →L[ℝ] F} {L c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R 0 L y v)
    (hc : c ∈ Ioo (0 : ℝ) L)
    (hR : ContinuousOn R (Icc (0 : ℝ) L))
    (hSym : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hySmooth : ContDiff ℝ ∞ y)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) L, deriv y t = v t)
    (hy0 : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ Icc (0 : ℝ) L, y t ≠ 0) :
    ∃ W : ℝ → F,
      ContDiff ℝ ∞ W ∧
      W 0 = 0 ∧
      W L = 0 ∧
      indexForm R 0 L W (deriv W) W (deriv W) < 0 := by
  obtain ⟨s, hs⟩ :=
    hsol.exists_split_neg_on hc hR hSym hy0 hyc hne
  let Z : ℝ → F := indexTestFieldTo L (v c)
  let DZ : ℝ → F := indexTestDerivTo L (v c)
  let W₀ : ℝ → F := y + s • Z
  let W₁ : ℝ → F := s • Z
  have hZSmooth : ContDiff ℝ ∞ Z := by
    simpa only [Z] using testFieldTo_smooth L (v c)
  have hW₀Smooth : ContDiff ℝ ∞ W₀ := by
    simpa only [W₀] using hySmooth.add (hZSmooth.const_smul s)
  have hW₁Smooth : ContDiff ℝ ∞ W₁ := by
    simpa only [W₁] using hZSmooth.const_smul s
  have hZd (t : ℝ) : HasDerivAt Z (DZ t) t := by
    simpa only [Z, DZ] using testFieldTo_deriv L (v c) t
  have hyDeriv (t : ℝ) : HasDerivAt y (deriv y t) t :=
    (hySmooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hW₀d (t : ℝ) :
      HasDerivAt W₀ (deriv y t + s • DZ t) t := by
    simpa only [W₀] using (hyDeriv t).add ((hZd t).const_smul s)
  have hW₁d (t : ℝ) :
      HasDerivAt W₁ (s • DZ t) t := by
    simpa only [W₁] using (hZd t).const_smul s
  have hdW₀ (t : ℝ) : deriv W₀ t = deriv y t + s • DZ t :=
    (hW₀d t).deriv
  have hdW₁ (t : ℝ) : deriv W₁ t = s • DZ t :=
    (hW₁d t).deriv
  have hW₀_zero : W₀ 0 = 0 := by
    simp [W₀, Z, indexTestFieldTo, hy0]
  have hW₁_zero : W₁ L = 0 := by
    simp [W₁, Z, indexTestFieldTo]
  have hmatch : W₀ c = W₁ c := by
    simp [W₀, W₁, hyc]
  have h0c : Icc (0 : ℝ) c ⊆ Icc (0 : ℝ) L :=
    Icc_subset_Icc le_rfl hc.2.le
  have hindex₀ :
      indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) =
        indexForm R 0 c
          (y + s • Z) (v + s • DZ)
          (y + s • Z) (v + s • DZ) := by
    unfold indexForm
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hc.1.le] at ht
    unfold indexIntegrand
    rw [hdW₀ t, hderiv t (h0c ht)]
    rfl
  have hindex₁ :
      indexForm R c L W₁ (deriv W₁) W₁ (deriv W₁) =
        indexForm R c L
          (s • Z) (s • DZ)
          (s • Z) (s • DZ) := by
    unfold indexForm
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hc.2.le] at ht
    unfold indexIntegrand
    rw [hdW₁ t]
    rfl
  have hneg :
      indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) +
          indexForm R c L W₁ (deriv W₁) W₁ (deriv W₁) < 0 := by
    rw [hindex₀, hindex₁]
    simpa only [Z, DZ] using hs
  exact smooth_split_to (W₀ := W₀) (W₁ := W₁)
    (hc.1.trans hc.2) hc hR hW₀Smooth hW₁Smooth
    hW₀_zero hW₁_zero hmatch hneg

/-- Unit-interval compatibility wrapper for `IsJacobiSolOn.exists_smooth_neg_on`. -/
theorem IsJacobiSolOn.exists_smooth_neg
    [CompleteSpace F]
    {R : ℝ → F →L[ℝ] F} {c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R 0 1 y v)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hR : ContinuousOn R (Icc (0 : ℝ) 1))
    (hSym : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hySmooth : ContDiff ℝ ∞ y)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, deriv y t = v t)
    (hy0 : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ Icc (0 : ℝ) 1, y t ≠ 0) :
    ∃ W : ℝ → F,
      ContDiff ℝ ∞ W ∧
      W 0 = 0 ∧
      W 1 = 0 ∧
      indexForm R 0 1 W (deriv W) W (deriv W) < 0 :=
  hsol.exists_smooth_neg_on hc hR hSym hySmooth hderiv hy0 hyc hne

end DifferentialGeometry.Analysis.ODE
