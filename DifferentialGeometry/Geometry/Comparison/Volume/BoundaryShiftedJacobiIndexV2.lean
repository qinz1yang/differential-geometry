import DifferentialGeometry.Analysis.ODE.IndexForm.SmoothNegativeDirection

set_option autoImplicit false

open Set
open scoped ContDiff RealInnerProductSpace Topology

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Analysis.ODE

private theorem x124_exists_norm_bound
    {F : Type*} [NormedAddCommGroup F] {f : ℝ → F}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ C := by
  have hnorm : ContinuousOn (fun t : ℝ => ‖f t‖) (Icc (0 : ℝ) 1) :=
    continuous_norm.comp_continuousOn hf
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hnorm
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hC ⟨t, ht, rfl⟩).trans (le_max_left _ _)

private theorem x124_index_abs_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {R : ℝ → F →L[ℝ] F} {W V : ℝ → F} {a b KR KW KV : ℝ}
    (hKR : 0 ≤ KR) (hKW : 0 ≤ KW) (hKV : 0 ≤ KV)
    (hR : ∀ t ∈ uIcc a b, ‖R t‖ ≤ KR)
    (hW : ∀ t ∈ uIcc a b, ‖W t‖ ≤ KW)
    (hV : ∀ t ∈ uIcc a b, ‖V t‖ ≤ KV) :
    |indexForm R a b W V W V| ≤ (KV ^ 2 + KR * KW ^ 2) * |b - a| := by
  have hpoint {t : ℝ} (ht : t ∈ uIcc a b) :
      |indexIntegrand R W V W V t| ≤ KV ^ 2 + KR * KW ^ 2 := by
    have hRW : ‖R t (W t)‖ ≤ KR * KW :=
      ((R t).le_opNorm (W t)).trans
        (mul_le_mul (hR t ht) (hW t ht) (norm_nonneg _) hKR)
    have hVV : ‖V t‖ * ‖V t‖ ≤ KV * KV := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hV t ht))
        (add_nonneg hKV (norm_nonneg (V t)))]
    have hRWW : ‖R t (W t)‖ * ‖W t‖ ≤ (KR * KW) * KW :=
      mul_le_mul hRW (hW t ht) (norm_nonneg _) (mul_nonneg hKR hKW)
    unfold indexIntegrand
    calc
      |⟪V t, V t⟫ - ⟪R t (W t), W t⟫|
          ≤ |⟪V t, V t⟫| + |⟪R t (W t), W t⟫| := abs_sub _ _
      _ ≤ ‖V t‖ * ‖V t‖ + ‖R t (W t)‖ * ‖W t‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ ≤ KV * KV + (KR * KW) * KW := add_le_add hVV hRWW
      _ = KV ^ 2 + KR * KW ^ 2 := by ring
  unfold indexForm
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := indexIntegrand R W V W V) (C := KV ^ 2 + KR * KW ^ 2)
    (fun t ht => by
      simpa only [Real.norm_eq_abs] using hpoint (uIoc_subset_uIcc ht))
  simpa only [Real.norm_eq_abs] using hbound

private theorem x124_affine_indexForm
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {R : ℝ → F →L[ℝ] F} {W V : ℝ → F} (a ℓ s t : ℝ) :
    indexForm (fun q => ℓ ^ 2 • R (a + ℓ * q)) s t
        (fun q => W (a + ℓ * q)) (fun q => ℓ • V (a + ℓ * q))
        (fun q => W (a + ℓ * q)) (fun q => ℓ • V (a + ℓ * q)) =
      ℓ * indexForm R (a + ℓ * s) (a + ℓ * t) W V W V := by
  have hpoint (q : ℝ) :
      indexIntegrand (fun q => ℓ ^ 2 • R (a + ℓ * q))
          (fun q => W (a + ℓ * q)) (fun q => ℓ • V (a + ℓ * q))
          (fun q => W (a + ℓ * q)) (fun q => ℓ • V (a + ℓ * q)) q =
        ℓ ^ 2 * indexIntegrand R W V W V (a + ℓ * q) := by
    simp only [indexIntegrand, smul_apply, real_inner_smul_left, real_inner_smul_right]
    ring
  unfold indexForm
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  calc
    ℓ ^ 2 * (∫ q in s..t, indexIntegrand R W V W V (a + ℓ * q)) =
        ℓ * (ℓ * ∫ q in s..t, indexIntegrand R W V W V (a + ℓ * q)) := by ring
    _ = ℓ * ∫ q in a + ℓ * s..a + ℓ * t, indexIntegrand R W V W V q := by
      have hchange := intervalIntegral.smul_integral_comp_add_mul
        (a := s) (b := t) (fun q => indexIntegrand R W V W V q) ℓ a
      simpa only [smul_eq_mul] using congrArg (fun x : ℝ => ℓ * x) hchange

private theorem x124_deriv_affine
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ ∞ f) (a ℓ t : ℝ) :
    deriv (fun q => f (a + ℓ * q)) t = ℓ • deriv f (a + ℓ * t) := by
  have houter : HasDerivAt f (deriv f (a + ℓ * t)) (a + ℓ * t) :=
    (hf.differentiable (by simp) (a + ℓ * t)).hasDerivAt
  have hinner : HasDerivAt (fun q : ℝ => a + ℓ * q) ℓ t := by
    convert (hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul ℓ) using 1
    · funext q
      simp only [Pi.add_apply, id_eq]
    · ring
  simpa [Function.comp_def] using (houter.scomp t hinner).deriv

/-- A negative Jacobi index direction can be moved off the zero endpoint.
This is the cutoff needed before applying nonnegative index on positive interior prefixes. -/
theorem IsJacobiFieldOn.exists_contDiff_indexForm_neg_shifted_actual
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {R : ℝ → F →L[ℝ] F} {c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiFieldOn R 0 1 y v)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hR : ContinuousOn R (Icc (0 : ℝ) 1))
    (hSym : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hy : ContDiff ℝ ∞ y) (hya : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ Icc (0 : ℝ) 1, y t ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ 2 * a < 1 ∧
      ∃ Z : ℝ → F, ContDiff ℝ ∞ Z ∧ Z a = 0 ∧ Z 1 = 0 ∧
        indexForm R a 1 Z (deriv Z) Z (deriv Z) < 0 := by
  obtain ⟨W, hW, hW0, hW1, hWneg⟩ :=
    hsol.exists_contDiff_indexForm_neg hc hR (fun t _ => hSym t) hy.contDiffOn
      isOpen_univ (subset_univ _) hya hyc hne
  have hDcont : ContinuousOn (deriv W) (Icc (0 : ℝ) 1) :=
    (hW.of_le (by simp)).continuous_deriv_one.continuousOn
  obtain ⟨KR, hKR, hKRbound⟩ := x124_exists_norm_bound hR
  obtain ⟨KW, hKW, hKWbound⟩ := x124_exists_norm_bound hW.continuous.continuousOn
  obtain ⟨KV, hKV, hKVbound⟩ := x124_exists_norm_bound hDcont
  let Cstart : ℝ := KV ^ 2 + KR * KW ^ 2
  let Cleft : ℝ := (2 * KV) ^ 2 + KR * (2 * KV) ^ 2
  let Ctotal : ℝ := 2 * Cstart + Cleft
  have hCstart : 0 ≤ Cstart := by dsimp [Cstart]; positivity
  have hCleft : 0 ≤ Cleft := by dsimp [Cleft]; positivity
  have hCtotal : 0 ≤ Ctotal := by dsimp [Ctotal]; positivity
  let ρ : ℝ := min (1 / 4) ((-indexForm R 0 1 W (deriv W) W (deriv W)) / (Ctotal + 1))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have hneg : 0 < -indexForm R 0 1 W (deriv W) W (deriv W) := neg_pos.mpr hWneg
    positivity
  obtain ⟨a, ha0, haρ⟩ := exists_between hρ
  have haSmall : a < 1 / 4 := haρ.trans_le (min_le_left _ _)
  have h2a : 2 * a < 1 := by linarith
  have hCbound : Ctotal * a < -indexForm R 0 1 W (deriv W) W (deriv W) := by
    have hfrac := haρ.trans_le (min_le_right _ _)
    have hmul := (lt_div_iff₀ (by positivity : 0 < Ctotal + 1)).mp hfrac
    nlinarith [mul_nonneg hCtotal ha0.le]
  let Q : ℝ → F := fun t => ((t - a) / a) • W (2 * a)
  have hQ : ContDiff ℝ ∞ Q := by
    unfold Q
    exact (((contDiff_id.sub contDiff_const).div_const a).smul_const (W (2 * a)))
  have hQder (t : ℝ) : deriv Q t = a⁻¹ • W (2 * a) := by
    have hlin : HasDerivAt (fun s : ℝ => (s - a) / a) (a⁻¹) t := by
      simpa [one_div] using ((hasDerivAt_id t).sub_const a).div_const a
    have hQd := hlin.smul_const (W (2 * a))
    simpa only [Q] using hQd.deriv
  have hWbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖W t‖ ≤ KW := hKWbound t ht
  have hVbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖deriv W t‖ ≤ KV := hKVbound t ht
  have hW2 : ‖W (2 * a)‖ ≤ KV * (2 * a) := by
    have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s _ => (hW.differentiable (by simp) s))
      (fun s hs => hVbound s hs) (convex_Icc (0 : ℝ) 1)
      (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
      (⟨by positivity, by linarith⟩ : 2 * a ∈ Icc (0 : ℝ) 1)
    rw [hW0, sub_zero] at hmean
    have haNonneg : 0 ≤ 2 * a := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg ha0.le] using hmean
  have hQbounds : ∀ t ∈ Icc a (2 * a), ‖Q t‖ ≤ 2 * KV * a := by
    intro t ht
    have hfac0 : 0 ≤ (t - a) / a := div_nonneg (by linarith [ht.1]) ha0.le
    have hfac1 : (t - a) / a ≤ 1 := (div_le_one ha0).2 (by linarith [ht.2])
    simp only [Q, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac0]
    have hprod := mul_le_mul_of_nonneg_right hfac1 (norm_nonneg (W (2 * a)))
    have hscale : 1 * ‖W (2 * a)‖ ≤ 2 * KV * a := by
      calc
        1 * ‖W (2 * a)‖ ≤ KV * (2 * a) := by simpa using hW2
        _ = 2 * KV * a := by ring
    calc
      (t - a) / a * ‖W (2 * a)‖ ≤ 1 * ‖W (2 * a)‖ := hprod
      _ ≤ 2 * KV * a := hscale
  have hQderBound : ∀ t ∈ Icc a (2 * a), ‖deriv Q t‖ ≤ 2 * KV := by
    intro t ht
    rw [hQder, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)]
    have hscale : ‖W (2 * a)‖ ≤ 2 * KV * a := by
      calc
        ‖W (2 * a)‖ ≤ KV * (2 * a) := hW2
        _ = 2 * KV * a := by ring
    calc
      a⁻¹ * ‖W (2 * a)‖ ≤ a⁻¹ * (2 * KV * a) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = 2 * KV := by field_simp
  have hleftAbs :
      |indexForm R a (2 * a) Q (deriv Q) Q (deriv Q)| ≤ Cleft * a := by
    have hR' : ∀ t ∈ uIcc a (2 * a), ‖R t‖ ≤ KR := by
      intro t ht
      rw [uIcc_of_le (by linarith : a ≤ 2 * a)] at ht
      exact hKRbound t ⟨by linarith [ht.1], ht.2.trans h2a.le⟩
    have hQ' : ∀ t ∈ uIcc a (2 * a), ‖Q t‖ ≤ 2 * KV * a := by
      intro t ht
      rw [uIcc_of_le (by linarith : a ≤ 2 * a)] at ht
      exact hQbounds t ht
    have hQD' : ∀ t ∈ uIcc a (2 * a), ‖deriv Q t‖ ≤ 2 * KV := by
      intro t ht
      rw [uIcc_of_le (by linarith : a ≤ 2 * a)] at ht
      exact hQderBound t ht
    have hraw := x124_index_abs_le hKR (by positivity) (by positivity) hR' hQ' hQD'
    have hlen : |2 * a - a| = a := by rw [show 2 * a - a = a by ring, abs_of_pos ha0]
    have hsmall : 2 * KV * a ≤ 2 * KV := by
      nlinarith [mul_nonneg (show 0 ≤ 2 * KV by positivity)
        (show 0 ≤ 1 - a by linarith [haSmall])]
    have hprod : (2 * KV * a) * (2 * KV * a) ≤ (2 * KV) * (2 * KV) :=
      mul_le_mul hsmall hsmall (by positivity) (by positivity)
    have hcoeff : (2 * KV) ^ 2 + KR * ((2 * KV * a) * (2 * KV * a)) ≤ Cleft := by
      dsimp [Cleft]
      have hprodKR := mul_le_mul_of_nonneg_left hprod hKR
      nlinarith [hprodKR]
    rw [hlen] at hraw
    have hcoeff' : (2 * KV) ^ 2 + KR * (2 * KV * a) ^ 2 ≤ Cleft := by
      simpa only [pow_two] using hcoeff
    have hraw' := hraw.trans (mul_le_mul_of_nonneg_right hcoeff' ha0.le)
    simpa [Cleft, hlen, pow_two, mul_assoc] using hraw'
  have hstartAbs :
      |indexForm R 0 (2 * a) W (deriv W) W (deriv W)| ≤ Cstart * (2 * a) := by
    have hR' : ∀ t ∈ uIcc 0 (2 * a), ‖R t‖ ≤ KR := by
      intro t ht
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] at ht
      exact hKRbound t ⟨ht.1, ht.2.trans h2a.le⟩
    have hW' : ∀ t ∈ uIcc 0 (2 * a), ‖W t‖ ≤ KW := by
      intro t ht
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] at ht
      exact hWbound t ⟨ht.1, ht.2.trans h2a.le⟩
    have hV' : ∀ t ∈ uIcc 0 (2 * a), ‖deriv W t‖ ≤ KV := by
      intro t ht
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] at ht
      exact hVbound t ⟨ht.1, ht.2.trans h2a.le⟩
    have hraw := x124_index_abs_le hKR hKW hKV hR' hW' hV'
    have hlen : |2 * a - 0| = 2 * a := by
      rw [sub_zero]
      exact abs_of_nonneg (by positivity)
    simpa [Cstart, hlen, abs_of_pos ha0] using hraw
  have hsplitW :
      indexForm R 0 1 W (deriv W) W (deriv W) =
        indexForm R 0 (2 * a) W (deriv W) W (deriv W) +
          indexForm R (2 * a) 1 W (deriv W) W (deriv W) := by
    have hRleft : ContinuousOn R (uIcc (0 : ℝ) (2 * a)) := by
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)]
      exact hR.mono (by intro t ht; exact ⟨ht.1, ht.2.trans h2a.le⟩)
    have hRright : ContinuousOn R (uIcc (2 * a) 1) := by
      rw [uIcc_of_le (by linarith : 2 * a ≤ 1)]
      exact hR.mono (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
    have hVleft : ContinuousOn (deriv W) (uIcc (0 : ℝ) (2 * a)) := by
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)]
      exact hDcont.mono (by intro t ht; exact ⟨ht.1, ht.2.trans h2a.le⟩)
    have hVright : ContinuousOn (deriv W) (uIcc (2 * a) 1) := by
      rw [uIcc_of_le (by linarith : 2 * a ≤ 1)]
      exact hDcont.mono (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
    have hI₁ : IntervalIntegrable (indexIntegrand R W (deriv W) W (deriv W))
        MeasureTheory.volume 0 (2*a) := by
      apply ContinuousOn.intervalIntegrable
      exact (contOn_indexIntegrand hRleft hW.continuous.continuousOn hVleft
        hW.continuous.continuousOn hVleft)
    have hI₂ : IntervalIntegrable (indexIntegrand R W (deriv W) W (deriv W))
        MeasureTheory.volume (2*a) 1 := by
      apply ContinuousOn.intervalIntegrable
      exact (contOn_indexIntegrand hRright hW.continuous.continuousOn hVright
        hW.continuous.continuousOn hVright)
    exact (indexForm_add_adjacent hI₁ hI₂).symm
  have hsumNeg :
      indexForm R a (2 * a) Q (deriv Q) Q (deriv Q) +
        indexForm R (2 * a) 1 W (deriv W) W (deriv W) < 0 := by
    rw [hsplitW] at hWneg
    have hupper :
        indexForm R a (2 * a) Q (deriv Q) Q (deriv Q) +
          indexForm R (2 * a) 1 W (deriv W) W (deriv W) ≤
          indexForm R 0 1 W (deriv W) W (deriv W) + Ctotal * a := by
      have hleft := hleftAbs
      have hstart := hstartAbs
      rw [abs_le] at hleft hstart
      nlinarith [hleft.2, hstart.1, hCbound]
    exact lt_of_le_of_lt hupper (by nlinarith [hCbound, hWneg])
  -- Reparameterize [a,1] to [0,1], splice the small ramp with the old negative field,
  -- then transport the clamped field back.
  let ℓ : ℝ := 1 - a
  have hℓ : 0 < ℓ := by dsimp [ℓ]; linarith
  let cp : ℝ := a / ℓ
  let Rp : ℝ → F →L[ℝ] F := fun t => ℓ ^ 2 • R (a + ℓ * t)
  let Wp : ℝ → F := fun t => Q (a + ℓ * t)
  let Vp : ℝ → F := fun t => W (a + ℓ * t)
  let dWp : ℝ → F := fun t => ℓ • deriv Q (a + ℓ * t)
  let dVp : ℝ → F := fun t => ℓ • deriv W (a + ℓ * t)
  have hWp : ContDiff ℝ ∞ Wp := hQ.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hVp : ContDiff ℝ ∞ Vp := hW.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hWpder : deriv Wp = dWp := by
    funext t
    simp [Wp, dWp, x124_deriv_affine hQ a ℓ t]
  have hVpder : deriv Vp = dVp := by
    funext t
    simp [Vp, dVp, x124_deriv_affine hW a ℓ t]
  have hRcont : ContinuousOn Rp (Icc (0 : ℝ) 1) := by
    have hpull : ContinuousOn (fun t => R (a + ℓ * t)) (Icc (0 : ℝ) 1) :=
      hR.comp (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
        (fun t ht => ⟨add_nonneg ha0.le (mul_nonneg hℓ.le ht.1), by
          have hmul : ℓ * t ≤ ℓ * 1 := mul_le_mul_of_nonneg_left ht.2 hℓ.le
          calc
            a + ℓ * t ≤ a + ℓ * 1 := by nlinarith [hmul]
            _ = 1 := by dsimp [ℓ]; ring⟩)
    have hconst : ContinuousOn (fun _ : ℝ => ℓ ^ 2) (Icc (0 : ℝ) 1) :=
      continuousOn_const
    change ContinuousOn ((fun _ : ℝ => ℓ ^ 2) • (fun t => R (a + ℓ * t))) _
    exact hconst.smul hpull
  have hCp : cp ∈ Ioo (0 : ℝ) 1 := by
    dsimp [cp, ℓ]
    constructor
    · positivity
    · rw [div_lt_one (by linarith : 0 < 1-a)]
      linarith
  have hWp0 : Wp 0 = 0 := by
    simp [Wp, Q, zero_smul]
  have hVp1 : Vp 1 = 0 := by
    simp [Vp, ℓ, hW1]
  have hmatch : Wp cp = Vp cp := by
    have hbirth : a + ℓ * cp = 2 * a := by
      dsimp [cp]
      field_simp [hℓ.ne']
      ring
    change Q (a + ℓ * cp) = W (a + ℓ * cp)
    rw [hbirth]
    change ((2 * a - a) / a) • W (2 * a) = W (2 * a)
    have hquot : (2 * a - a) / a = 1 := by
      rw [show 2 * a - a = a by ring]
      exact div_self ha0.ne'
    rw [hquot, one_smul]
  have hnegNorm :
      indexForm Rp 0 cp Wp (deriv Wp) Wp (deriv Wp) +
        indexForm Rp cp 1 Vp (deriv Vp) Vp (deriv Vp) < 0 := by
    rw [hWpder, hVpder]
    have hleft := x124_affine_indexForm
      (R := R) (W := Q) (V := deriv Q) a ℓ 0 cp
    have hright := x124_affine_indexForm
      (R := R) (W := W) (V := deriv W) a ℓ cp 1
    have hbirth : a + ℓ * cp = 2 * a := by
      dsimp [cp]
      field_simp [hℓ.ne']
      ring
    have htop : a + ℓ = 1 := by dsimp [ℓ]; ring
    have hleft' :
        indexForm Rp 0 cp Wp dWp Wp dWp =
          ℓ * indexForm R a (2 * a) Q (deriv Q) Q (deriv Q) := by
      simpa [Rp, Wp, dWp, hbirth] using hleft
    have hright' :
        indexForm Rp cp 1 Vp dVp Vp dVp =
          ℓ * indexForm R (2 * a) 1 W (deriv W) W (deriv W) := by
      simpa [Rp, Vp, dVp, hbirth, htop] using hright
    rw [hleft', hright']
    have : ℓ * (indexForm R a (2 * a) Q (deriv Q) Q (deriv Q) +
        indexForm R (2 * a) 1 W (deriv W) W (deriv W)) < 0 :=
      mul_neg_of_pos_of_neg hℓ hsumNeg
    simpa [cp, ℓ, mul_add] using this
  obtain ⟨S, hS, hS0, hS1, hSneg⟩ :=
    exists_smooth_indexForm_neg_of_split (F := F) (R := Rp)
      (A := -1) (B := 2) (c := cp) (W₀ := Wp) (W₁ := Vp)
      (by norm_num) (by norm_num) hCp hRcont
      hWp.contDiffOn hVp.contDiffOn hWp0 hVp1 hmatch hnegNorm
  let Z : ℝ → F := fun t => S ((t - a) / ℓ)
  have hZ : ContDiff ℝ ∞ Z := hS.comp ((contDiff_id.sub contDiff_const).div_const ℓ)
  have hZa : Z a = 0 := by simp [Z, hS0]
  have hZ1 : Z 1 = 0 := by
    have harg : (1 - a) / ℓ = 1 := by
      dsimp [ℓ]
      exact div_self (by linarith)
    simpa [Z, harg] using hS1
  have hZder : deriv Z = (fun t => ℓ⁻¹ • deriv S ((t - a) / ℓ)) := by
    funext t
    have harg : HasDerivAt (fun s : ℝ => (s-a)/ℓ) ℓ⁻¹ t := by
      simpa [one_div] using ((hasDerivAt_id t).sub_const a).div_const ℓ
    have houter : HasDerivAt S (deriv S ((t-a)/ℓ)) ((t-a)/ℓ) :=
      (hS.differentiable (by simp) ((t-a)/ℓ)).hasDerivAt
    have hcomp := houter.scomp t harg
    exact hcomp.deriv
  have hindexZ :
      indexForm Rp 0 1 S (deriv S) S (deriv S) =
        ℓ * indexForm R a 1 Z (deriv Z) Z (deriv Z) := by
    -- Apply the affine change of variables in the reverse direction.
    have hscale := x124_affine_indexForm
      (R := R) (W := Z) (V := deriv Z) a ℓ 0 1
    have hZfun : (fun t => Z (a + ℓ*t)) = S := by
      funext t
      change S ((a + ℓ * t - a) / ℓ) = S t
      have harg : (a + ℓ * t - a) / ℓ = t := by
        rw [add_sub_cancel_left]
        exact mul_div_cancel_left₀ t hℓ.ne'
      rw [harg]
    have hZdfun : (fun t => ℓ • deriv Z (a + ℓ*t)) = deriv S := by
      funext t
      rw [hZder]
      change ℓ • (ℓ⁻¹ • deriv S ((a + ℓ * t - a) / ℓ)) = deriv S t
      have harg : (a + ℓ * t - a) / ℓ = t := by
        rw [add_sub_cancel_left]
        exact mul_div_cancel_left₀ t hℓ.ne'
      rw [harg]
      simp [smul_smul, hℓ.ne']
    rw [hZfun, hZdfun] at hscale
    simpa [Rp, ℓ] using hscale
  have hindexZneg : indexForm R a 1 Z (deriv Z) Z (deriv Z) < 0 := by
    rw [hindexZ] at hSneg
    by_contra hnot
    have hnonneg : 0 ≤ indexForm R a 1 Z (deriv Z) Z (deriv Z) := le_of_not_gt hnot
    have hscaled : 0 ≤ ℓ * indexForm R a 1 Z (deriv Z) Z (deriv Z) :=
      mul_nonneg hℓ.le hnonneg
    linarith
  exact ⟨a, ha0, h2a, Z, hZ, hZa, hZ1, hindexZneg⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
