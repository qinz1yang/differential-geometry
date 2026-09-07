-- Modified 2026-09-07: Mathlib 4.33 elaboration compatibility
import DifferentialGeometry.External.DeGiorgi.PositivePart

/-!
# Nonnegative smooth density in `H₀¹`

This file refines the approximation data carried by `MemH01`: a pointwise
nonnegative function admits smooth, compactly supported, pointwise nonnegative
approximants with the same weak-gradient witness.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

private def posReg (n : ℕ) (t : ℝ) : ℝ :=
  t * Real.smoothTransition (((n : ℝ) + 1) * t)

private theorem posReg_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (posReg n) := by
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ((n : ℝ) + 1) * t) :=
    contDiff_const.mul contDiff_id
  exact contDiff_id.mul (Real.smoothTransition.contDiff.comp harg)

private theorem posReg_nonneg (n : ℕ) (t : ℝ) : 0 ≤ posReg n t := by
  by_cases ht : t ≤ 0
  · rw [posReg, Real.smoothTransition.zero_of_nonpos]
    · simp
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
  · exact mul_nonneg (le_of_not_ge ht) (Real.smoothTransition.nonneg _)

private theorem posReg_eq_zero (n : ℕ) {t : ℝ} (ht : t ≤ 0) :
    posReg n t = 0 := by
  rw [posReg, Real.smoothTransition.zero_of_nonpos]
  · simp
  · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) ht

private theorem posReg_le_posPart (n : ℕ) (t : ℝ) :
    posReg n t ≤ max t 0 := by
  by_cases ht : t ≤ 0
  · simp [posReg_eq_zero n ht, max_eq_right ht]
  · rw [max_eq_left (le_of_not_ge ht)]
    exact mul_le_of_le_one_right (le_of_not_ge ht) (Real.smoothTransition.le_one _)

private theorem posReg_tendsto (t : ℝ) :
    Tendsto (fun n => posReg n t) atTop (nhds (max t 0)) := by
  by_cases ht : t ≤ 0
  · exact tendsto_const_nhds.congr'
      (Eventually.of_forall fun (n : ℕ) => by simp [max_eq_right ht, posReg_eq_zero n ht])
  · have ht' : 0 < t := lt_of_not_ge ht
    have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ ((n : ℝ) + 1) * t := by
      have hge : ∀ᶠ n : ℕ in atTop, (⌈1 / t⌉₊ : ℕ) ≤ n :=
        eventually_ge_atTop _
      filter_upwards [hge] with n hn
      have hceil : 1 / t ≤ (n : ℝ) := by
        exact (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))
      have hone : 1 ≤ (n : ℝ) * t := by
        calc
          1 = (1 / t) * t := by field_simp
          _ ≤ (n : ℝ) * t := mul_le_mul_of_nonneg_right hceil ht'.le
      nlinarith
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp [posReg, Real.smoothTransition.one_of_one_le hn, max_eq_left ht'.le]

private theorem exists_st_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).continuous_deriv_one
  obtain ⟨m, -, hm⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) hcont.norm.continuousOn
  let C := |deriv Real.smoothTransition m|
  refine ⟨C, abs_nonneg _, fun t => ?_⟩
  by_cases ht0 : t < 0
  · have heq : Real.smoothTransition =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht0] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    rw [heq.deriv_eq, deriv_const, abs_zero]
    exact abs_nonneg _
  · by_cases ht1 : 1 < t
    · have heq : Real.smoothTransition =ᶠ[nhds t] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds ht1] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [heq.deriv_eq, deriv_const, abs_zero]
      exact abs_nonneg _
    · push Not at ht0 ht1
      exact Filter.eventually_principal.mp hm t ⟨ht0, ht1⟩

private theorem posReg_deriv (n : ℕ) (t : ℝ) :
    deriv (posReg n) t =
      Real.smoothTransition (((n : ℝ) + 1) * t) +
        (((n : ℝ) + 1) * t) * deriv Real.smoothTransition (((n : ℝ) + 1) * t) := by
  have hst : DifferentiableAt ℝ Real.smoothTransition (((n : ℝ) + 1) * t) :=
    Real.smoothTransition.contDiff.differentiable one_ne_zero _
  have hlin : HasDerivAt (fun s : ℝ => ((n : ℝ) + 1) * s) ((n : ℝ) + 1) t := by
    simpa using (hasDerivAt_id t).const_mul ((n : ℝ) + 1)
  have hcomp : HasDerivAt
      (fun s : ℝ => Real.smoothTransition (((n : ℝ) + 1) * s))
      (deriv Real.smoothTransition (((n : ℝ) + 1) * t) * ((n : ℝ) + 1)) t :=
    hst.hasDerivAt.comp t hlin
  have hmul := (hasDerivAt_id t).mul hcomp
  have hfun :
      (fun s : ℝ => s * Real.smoothTransition (((n : ℝ) + 1) * s)) =
        id * fun s : ℝ => Real.smoothTransition (((n : ℝ) + 1) * s) := by
    funext s
    rfl
  change deriv (fun s : ℝ => s * Real.smoothTransition (((n : ℝ) + 1) * s)) t = _
  rw [hfun, hmul.deriv]
  simp only [id_eq]
  ring

private theorem posReg_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, |deriv (posReg n) t| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_st_bound
  refine ⟨1 + C, by linarith, fun n t => ?_⟩
  let s := ((n : ℝ) + 1) * t
  rw [posReg_deriv]
  calc
    |Real.smoothTransition s + s * deriv Real.smoothTransition s|
        ≤ |Real.smoothTransition s| + |s * deriv Real.smoothTransition s| := abs_add_le _ _
    _ ≤ 1 + C := by
      have hfirst : |Real.smoothTransition s| ≤ 1 := by
        rw [abs_of_nonneg (Real.smoothTransition.nonneg s)]
        exact Real.smoothTransition.le_one s
      have hsecond : |s * deriv Real.smoothTransition s| ≤ C := by
        by_cases hs0 : s < 0
        · have heq : Real.smoothTransition =ᶠ[nhds s] fun _ => (0 : ℝ) := by
            filter_upwards [Iio_mem_nhds hs0] with y hy
            exact Real.smoothTransition.zero_of_nonpos hy.le
          rw [heq.deriv_eq, deriv_const, mul_zero, abs_zero]
          exact hC
        · by_cases hs1 : 1 < s
          · have heq : Real.smoothTransition =ᶠ[nhds s] fun _ => (1 : ℝ) := by
              filter_upwards [Ioi_mem_nhds hs1] with y hy
              exact Real.smoothTransition.one_of_one_le hy.le
            rw [heq.deriv_eq, deriv_const, mul_zero, abs_zero]
            exact hC
          · push Not at hs0 hs1
            rw [abs_mul]
            calc
              |s| * |deriv Real.smoothTransition s| ≤ 1 * C :=
                mul_le_mul (by simpa [abs_of_nonneg hs0] using hs1) (hbound s)
                  (abs_nonneg _) zero_le_one
              _ = C := one_mul C
      linarith

private theorem reg_deriv_tendsto (t : ℝ) :
    Tendsto (fun n => deriv (posReg n) t) atTop
      (nhds (if 0 < t then 1 else 0)) := by
  by_cases ht : 0 < t
  · have hev : ∀ᶠ n : ℕ in atTop, 1 < ((n : ℝ) + 1) * t := by
      have hgt : ∀ᶠ n : ℕ in atTop, (⌈1 / t⌉₊ : ℕ) < n :=
        eventually_gt_atTop _
      filter_upwards [hgt] with n hn
      have hceil : 1 / t < (n : ℝ) :=
        lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
      have hone : 1 < (n : ℝ) * t := by
        calc
          1 = (1 / t) * t := by field_simp
          _ < (n : ℝ) * t := mul_lt_mul_of_pos_right hceil ht
      nlinarith
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    have heq : Real.smoothTransition =ᶠ[nhds (((n : ℝ) + 1) * t)] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hn] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    simp [posReg_deriv, ht, Real.smoothTransition.one_of_one_le hn.le, heq.deriv_eq]
  · have ht' : t ≤ 0 := le_of_not_gt ht
    have hzero : ∀ n, deriv (posReg n) t = 0 := by
      intro n
      by_cases ht0 : t < 0
      · have heq : posReg n =ᶠ[nhds t] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds ht0] with y hy
          exact posReg_eq_zero n hy.le
        rw [heq.deriv_eq, deriv_const]
      · have ht0 : t = 0 := le_antisymm ht' (le_of_not_gt ht0)
        subst t
        simp [posReg_deriv]
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => by simp [ht, hzero n])

omit [NeZero d] in
private theorem lp_zero_of_dom
    {F : ℕ → E → ℝ} {H : E → ℝ} {mu : Measure E}
    (hH : MemLp H 2 mu)
    (hF : ∀ n, AEStronglyMeasurable (F n) mu)
    (hdom : ∀ n, ∀ᵐ x ∂mu, |F n x| ≤ H x)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => F n x) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 mu) atTop (nhds 0) := by
  have huiH : UnifIntegrable (fun _ : ℕ => H) 2 mu :=
    MeasureTheory.unifIntegrable_const (by norm_num) (by simp) hH
  have huiF : UnifIntegrable F 2 mu := by
    intro e he
    obtain ⟨delta, hdelta, hsmall⟩ := huiH he
    refine ⟨delta, hdelta, fun n s hs hmus => ?_⟩
    exact (eLpNorm_mono_ae_real <| by
      filter_upwards [hdom n] with x hx
      by_cases hxs : x ∈ s <;> simp [hxs, hx]).trans (hsmall 0 s hs hmus)
  have hutH : UnifTight (fun _ : ℕ => H) 2 mu :=
    MeasureTheory.unifTight_const (by simp) hH
  have hutF : UnifTight F 2 mu := by
    intro e he
    obtain ⟨s, hmus, hsmall⟩ := hutH he
    refine ⟨s, hmus, fun n => ?_⟩
    exact (eLpNorm_mono_ae_real <| by
      filter_upwards [hdom n] with x hx
      by_cases hxs : x ∈ sᶜ <;> simp [hxs, hx]).trans (hsmall 0)
  have h := MeasureTheory.tendsto_Lp_of_tendsto_ae
    (p := (2 : ℝ≥0∞)) (μ := mu) (by norm_num) (by simp) hF
    (MeasureTheory.MemLp.zero' (p := (2 : ℝ≥0∞)) (μ := mu)) huiF hutF hlim
  refine h.congr' (Eventually.of_forall fun n => ?_)
  exact eLpNorm_congr_ae (Eventually.of_forall fun x => by simp)

omit [NeZero d] in
private theorem reg_comp_data
    {Omega : Set E} {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ q : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (q n)) ∧
      (∀ n, HasCompactSupport (q n)) ∧
      (∀ n, tsupport (q n) ⊆ tsupport f) ∧
      (∀ n x, 0 ≤ q n x) ∧
      Tendsto (fun n => eLpNorm (fun x => q n x - max (f x) 0) 2 (volume.restrict Omega))
        atTop (nhds 0) ∧
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm
          (fun x => (fderiv ℝ (q n) x) (EuclideanSpace.single i 1) -
            if 0 < f x then (fderiv ℝ f x) (EuclideanSpace.single i 1) else 0)
          2 (volume.restrict Omega)) atTop (nhds 0) := by
  classical
  let q : ℕ → E → ℝ := fun n x => posReg n (f x)
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (posReg_contDiff n).comp hf
  · intro n
    exact hfc.mono fun x hx => by
      contrapose! hx
      have hfx : f x = 0 := not_ne_iff.mp hx
      simp [q, hfx, posReg_eq_zero]
  · intro n
    rw [tsupport, tsupport]
    exact closure_mono (fun x hx => by
      contrapose! hx
      have hfx : f x = 0 := not_ne_iff.mp hx
      simp [q, hfx, posReg_eq_zero])
  · intro n x
    exact posReg_nonneg n (f x)
  · apply lp_zero_of_dom
    · exact ((hf.continuous.memLp_of_hasCompactSupport hfc).norm).restrict Omega
    · intro n
      exact ((posReg_contDiff n).comp hf).continuous.aestronglyMeasurable.sub
        ((hf.continuous.max continuous_const).aestronglyMeasurable)
    · intro n
      filter_upwards with x
      have hle := posReg_le_posPart n (f x)
      have hnonneg := posReg_nonneg n (f x)
      have hmax : 0 ≤ max (f x) 0 := le_max_right _ _
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [neg_sub]
      calc
        max (f x) 0 - posReg n (f x) ≤ max (f x) 0 := sub_le_self _ hnonneg
        _ ≤ |f x| := max_le (le_abs_self _) (abs_nonneg _)
        _ = ‖f x‖ := by rw [Real.norm_eq_abs]
    · filter_upwards with x
      simpa [q] using (posReg_tendsto (f x)).sub_const (max (f x) 0)
  · intro i
    obtain ⟨C, hC, hCb⟩ := posReg_deriv_bound
    let df : E → ℝ := fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)
    have hdf_smooth : ContDiff ℝ (⊤ : ℕ∞) df :=
      (hf.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
    apply lp_zero_of_dom
    · exact ((hdf_smooth.continuous.memLp_of_hasCompactSupport
        (hfc.fderiv_apply (𝕜 := ℝ) _)).norm.const_mul (C + 1)).restrict Omega
    · intro n
      exact ((((posReg_contDiff n).comp hf).fderiv_right
        (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const).continuous
        |>.aestronglyMeasurable.sub <| by
          exact hdf_smooth.continuous.aestronglyMeasurable.piecewise
            (measurableSet_lt continuous_const.measurable hf.continuous.measurable)
            stronglyMeasurable_const.aestronglyMeasurable
    · intro n
      filter_upwards with x
      have hfdcomp :
          (fderiv ℝ (q n) x) (EuclideanSpace.single i 1) =
            deriv (posReg n) (f x) * df x := by
        rw [show q n = posReg n ∘ f by rfl,
          fderiv_comp x ((posReg_contDiff n).differentiable (by simp) _)
            (hf.differentiable (by simp) x), ContinuousLinearMap.comp_apply,
          fderiv_eq_deriv_mul]
      rw [hfdcomp]
      by_cases hx : 0 < f x
      · simp only [hx, if_true]
        change |deriv (posReg n) (f x) * df x - df x| ≤ (C + 1) * ‖df x‖
        nth_rewrite 2 [← one_mul (df x)]
        rw [← sub_mul, abs_mul]
        rw [Real.norm_eq_abs]
        calc
          |deriv (posReg n) (f x) - 1| * |df x| ≤ (C + 1) * |df x| := by
            gcongr
            exact (abs_sub _ _).trans (add_le_add (hCb n (f x)) (by norm_num))
          _ = (C + 1) * |df x| := rfl
      · simp only [hx, if_false, sub_zero, abs_mul]
        exact mul_le_mul_of_nonneg_right (hCb n (f x)) (abs_nonneg _)
          |>.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
    · filter_upwards with x
      have hfdcomp (n : ℕ) :
          (fderiv ℝ (q n) x) (EuclideanSpace.single i 1) =
            deriv (posReg n) (f x) * df x := by
        rw [show q n = posReg n ∘ f by rfl,
          fderiv_comp x ((posReg_contDiff n).differentiable (by simp) _)
            (hf.differentiable (by simp) x), ContinuousLinearMap.comp_apply,
          fderiv_eq_deriv_mul]
      simp_rw [hfdcomp]
      simpa [df] using
        ((reg_deriv_tendsto (f x)).mul_const (df x)).sub_const
          (if 0 < f x then df x else 0)

namespace MemH01

/-- A pointwise nonnegative `H₀¹` function has pointwise nonnegative smooth
compactly supported approximants, converging together with the weak gradient
carried by one `MemW1pWitness`. -/
theorem nonneg_approx
    {Omega : Set E} (hOmega : IsOpen Omega) {phi : E → ℝ}
    (hphi : MemH01 phi Omega) (hphi_nonneg : ∀ x, 0 ≤ phi x) :
    ∃ (hw : MemW1pWitness 2 phi Omega) (psi : ℕ → E → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (psi n)) ∧
      (∀ n, HasCompactSupport (psi n)) ∧
      (∀ n, tsupport (psi n) ⊆ Omega) ∧
      (∀ n x, 0 ≤ psi n x) ∧
      Tendsto (fun n => eLpNorm (fun x => psi n x - phi x) 2 (volume.restrict Omega))
        atTop (nhds 0) ∧
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm
          (fun x => (fderiv ℝ (psi n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          2 (volume.restrict Omega)) atTop (nhds 0) := by
  classical
  let mu : Measure E := volume.restrict Omega
  rcases hphi.2 with
    ⟨hw, f, hf_smooth, hf_compact, hf_sub, hf_fun, hf_grad⟩
  have hphi_max : (fun x => max (phi x) 0) = phi := by
    funext x
    exact max_eq_left (hphi_nonneg x)
  have hpos_fun :
      Tendsto (fun n => eLpNorm (fun x => max (f n x) 0 - phi x) 2 mu)
        atTop (nhds 0) := by
    have hbound : ∀ n,
        eLpNorm (fun x => max (f n x) 0 - phi x) 2 mu ≤
          eLpNorm (fun x => f n x - phi x) 2 mu := by
      intro n
      refine eLpNorm_mono ?_
      intro x
      simpa [Real.norm_eq_abs, max_eq_left (hphi_nonneg x)] using
        abs_max_sub_max_le_abs (f n x) (phi x) 0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa [mu] using hf_fun) (fun _ => bot_le) hbound
  have hzero := hw.weakGrad_ae_eq_zero_on_zeroSet hOmega
  let rawGrad : ℕ → Fin d → E → ℝ := fun n i x =>
    if 0 < f n x then (fderiv ℝ (f n) x) (EuclideanSpace.single i 1) else 0
  have hf_pos (n : ℕ) : MeasurableSet {x | 0 < f n x} :=
    measurableSet_lt continuous_const.measurable (hf_smooth n).continuous.measurable
  have hphi_pos : NullMeasurableSet {x | 0 < phi x} mu :=
    AEStronglyMeasurable.nullMeasurableSet_lt (μ := mu)
      stronglyMeasurable_const.aestronglyMeasurable hw.memLp.aestronglyMeasurable
  have hraw_meas (n : ℕ) (i : Fin d) : AEStronglyMeasurable (rawGrad n i) mu := by
    have hd : AEStronglyMeasurable
        (fun x => (fderiv ℝ (f n) x) (EuclideanSpace.single i 1)) mu :=
      (((hf_smooth n).fderiv_right
        (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const).continuous
        |>.aestronglyMeasurable
    convert hd.indicator (hf_pos n) using 1
    funext x
    simp only [rawGrad, Set.indicator_apply, Set.mem_ofPred_eq]
  have hraw_grad : ∀ i : Fin d,
      Tendsto (fun n => eLpNorm (fun x => rawGrad n i x - hw.weakGrad x i) 2 mu)
        atTop (nhds 0) := by
    intro i
    let A : ℕ → E → ℝ := fun n x =>
      if 0 < f n x then
        (fderiv ℝ (f n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i
      else 0
    let B : ℕ → E → ℝ := fun n x =>
      (if 0 < f n x then hw.weakGrad x i else 0) -
        (if 0 < phi x then hw.weakGrad x i else 0)
    have hA : Tendsto (fun n => eLpNorm (A n) 2 mu) atTop (nhds 0) := by
      have hbound : ∀ n, eLpNorm (A n) 2 mu ≤
          eLpNorm
            (fun x => (fderiv ℝ (f n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 mu := by
        intro n
        refine eLpNorm_mono ?_
        intro x
        by_cases hx : 0 < f n x <;> simp [A, hx]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds (by simpa [mu] using hf_grad i) (fun _ => bot_le) hbound
    have hB : Tendsto (fun n => eLpNorm (B n) 2 mu) atTop (nhds 0) := by
      simpa [B, mu] using
        tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm
          (μ := mu) (u := phi) (G := fun x => hw.weakGrad x i) (ψ := f)
          (fun n => (hf_smooth n).continuous.aestronglyMeasurable.restrict)
          hw.memLp.aestronglyMeasurable (hw.weakGrad_component_memLp i)
          (hzero i) (by simpa [mu] using hf_fun)
    have hAe : ∀ n, (fun x => rawGrad n i x - hw.weakGrad x i) =ᵐ[mu]
        (fun x => A n x + B n x) := by
      intro n
      filter_upwards [hzero i] with x hx
      by_cases hfx : 0 < f n x <;> by_cases hpx : 0 < phi x
      · simp [rawGrad, A, B, hfx, hpx]
      · have hphiz : phi x = 0 := le_antisymm (le_of_not_gt hpx) (hphi_nonneg x)
        have hg := hx hphiz
        simp [rawGrad, A, B, hfx, hpx, hg]
      · simp [rawGrad, A, B, hfx, hpx]
      · have hphiz : phi x = 0 := le_antisymm (le_of_not_gt hpx) (hphi_nonneg x)
        have hg := hx hphiz
        simp [rawGrad, A, B, hfx, hpx, hg]
    have hbound : ∀ n,
        eLpNorm (fun x => rawGrad n i x - hw.weakGrad x i) 2 mu ≤
          eLpNorm (A n) 2 mu + eLpNorm (B n) 2 mu := by
      intro n
      rw [eLpNorm_congr_ae (hAe n)]
      apply eLpNorm_add_le
      · have hd : AEStronglyMeasurable
            (fun x => (fderiv ℝ (f n) x) (EuclideanSpace.single i 1) -
              hw.weakGrad x i) mu :=
          ((((hf_smooth n).fderiv_right
            (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const).continuous
            |>.aestronglyMeasurable).sub (hw.weakGrad_component_memLp i).aestronglyMeasurable
        convert hd.indicator (hf_pos n) using 1
        funext x
        simp only [A, Set.indicator_apply, Set.mem_ofPred_eq]
      · have hG := (hw.weakGrad_component_memLp i).aestronglyMeasurable
        convert (hG.indicator (hf_pos n)).sub (hG.indicator₀ hphi_pos) using 1
        funext x
        simp only [B, Pi.sub_apply, Set.indicator_apply, Set.mem_ofPred_eq]
      · norm_num
    have hupper : Tendsto (fun n => eLpNorm (A n) 2 mu + eLpNorm (B n) 2 mu)
        atTop (nhds 0) := by simpa using hA.add hB
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => bot_le) hbound
  have hreg : ∀ n, ∃ q : ℕ → E → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (q k)) ∧
      (∀ k, HasCompactSupport (q k)) ∧
      (∀ k, tsupport (q k) ⊆ tsupport (f n)) ∧
      (∀ k x, 0 ≤ q k x) ∧
      Tendsto (fun k => eLpNorm (fun x => q k x - max (f n x) 0) 2 mu)
        atTop (nhds 0) ∧
      ∀ i : Fin d, Tendsto (fun k => eLpNorm
        (fun x => (fderiv ℝ (q k) x) (EuclideanSpace.single i 1) - rawGrad n i x)
        2 mu) atTop (nhds 0) := by
    intro n
    simpa [mu, rawGrad] using
      reg_comp_data (Omega := Omega) (hf_smooth n) (hf_compact n)
  choose q hq_smooth hq_compact hq_sub hq_nonneg hq_fun hq_grad using hreg
  let eps : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have heps_pos : ∀ n, 0 < eps n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hgood : ∀ n, ∃ k,
      eLpNorm (fun x => q n k x - max (f n x) 0) 2 mu ≤ eps n ∧
      ∀ i : Fin d,
        eLpNorm
          (fun x => (fderiv ℝ (q n k) x) (EuclideanSpace.single i 1) - rawGrad n i x)
          2 mu ≤ eps n := by
    intro n
    have hfun_event : ∀ᶠ k in atTop,
        eLpNorm (fun x => q n k x - max (f n x) 0) 2 mu ≤ eps n :=
      ENNReal.tendsto_nhds_zero.1 (hq_fun n) (eps n) (heps_pos n)
    have hgrad_event : ∀ᶠ k in atTop, ∀ i : Fin d,
        eLpNorm
          (fun x => (fderiv ℝ (q n k) x) (EuclideanSpace.single i 1) - rawGrad n i x)
          2 mu ≤ eps n := by
      rw [Filter.eventually_all]
      intro i
      exact ENNReal.tendsto_nhds_zero.1 (hq_grad n i) (eps n) (heps_pos n)
    exact (hfun_event.and hgrad_event).exists
  choose k hk_fun hk_grad using hgood
  let psi : ℕ → E → ℝ := fun n => q n (k n)
  refine ⟨hw, psi, fun n => hq_smooth n (k n), fun n => hq_compact n (k n), ?_,
    fun n x => hq_nonneg n (k n) x, ?_, ?_⟩
  · intro n
    exact (hq_sub n (k n)).trans (hf_sub n)
  · have hbound : ∀ n,
        eLpNorm (fun x => psi n x - phi x) 2 mu ≤
          eps n + eLpNorm (fun x => max (f n x) 0 - phi x) 2 mu := by
      intro n
      have hfirst : AEStronglyMeasurable
          (fun x => psi n x - max (f n x) 0) mu :=
        (hq_smooth n (k n)).continuous.aestronglyMeasurable.sub
          ((hf_smooth n).continuous.max continuous_const).aestronglyMeasurable
      have hsecond : AEStronglyMeasurable
          (fun x => max (f n x) 0 - phi x) mu :=
        ((hf_smooth n).continuous.max continuous_const).aestronglyMeasurable.sub
          hw.memLp.aestronglyMeasurable
      have htri := eLpNorm_add_le hfirst hsecond (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have heq : (fun x => psi n x - phi x) =
          (fun x => (psi n x - max (f n x) 0) + (max (f n x) 0 - phi x)) := by
        funext x
        ring
      rw [heq]
      exact htri.trans (add_le_add (hk_fun n) le_rfl)
    have heps : Tendsto eps atTop (nhds 0) := by
      change Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (nhds 0)
      have h := ENNReal.tendsto_ofReal
        (by simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      convert h using 1 <;> simp only [ENNReal.ofReal_zero, one_div]
    have hupper : Tendsto
        (fun n => eps n + eLpNorm (fun x => max (f n x) 0 - phi x) 2 mu)
        atTop (nhds 0) := by simpa only [zero_add] using heps.add hpos_fun
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => bot_le) hbound
  · intro i
    have hbound : ∀ n,
        eLpNorm
            (fun x => (fderiv ℝ (psi n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 mu ≤
          eps n + eLpNorm (fun x => rawGrad n i x - hw.weakGrad x i) 2 mu := by
      intro n
      have hfirst : AEStronglyMeasurable
          (fun x => (fderiv ℝ (psi n) x) (EuclideanSpace.single i 1) - rawGrad n i x) mu :=
        ((((hq_smooth n (k n)).fderiv_right
          (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const).continuous
          |>.aestronglyMeasurable).sub (hraw_meas n i)
      have hsecond : AEStronglyMeasurable
          (fun x => rawGrad n i x - hw.weakGrad x i) mu :=
        (hraw_meas n i).sub (hw.weakGrad_component_memLp i).aestronglyMeasurable
      have htri := eLpNorm_add_le hfirst hsecond (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have heq :
          (fun x => (fderiv ℝ (psi n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) =
          (fun x =>
            ((fderiv ℝ (psi n) x) (EuclideanSpace.single i 1) - rawGrad n i x) +
              (rawGrad n i x - hw.weakGrad x i)) := by
        funext x
        ring
      rw [heq]
      exact htri.trans (add_le_add (hk_grad n i) le_rfl)
    have heps : Tendsto eps atTop (nhds 0) := by
      change Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (nhds 0)
      have h := ENNReal.tendsto_ofReal
        (by simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      convert h using 1 <;> simp only [ENNReal.ofReal_zero, one_div]
    have hupper : Tendsto
        (fun n => eps n +
          eLpNorm (fun x => rawGrad n i x - hw.weakGrad x i) 2 mu)
        atTop (nhds 0) := by simpa only [zero_add] using heps.add (hraw_grad i)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => bot_le) hbound

end MemH01

end DeGiorgi
