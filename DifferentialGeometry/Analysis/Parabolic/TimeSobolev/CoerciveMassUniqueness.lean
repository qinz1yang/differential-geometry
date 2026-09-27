import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDual

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {T : ℝ}

omit [CompleteSpace H] in
private theorem norm_toFunL2_le_of_initial_zero (hT : 0 ≤ T)
    (u : timeH1 H T) (hu : u.initial = 0) : ‖u.toFunL2‖ ≤ T * ‖u.deriv‖ := by
  have hb : ∀ t ∈ Icc (0 : ℝ) T, ‖u.toFun t‖ ≤ Real.sqrt T * ‖u.deriv‖ := by
    intro t ht
    simpa only [timeH1.trace0_apply, timeH1.timeDeriv_apply, hu, norm_zero, zero_add] using
      u.norm_toFun_le ht
  have h := norm_ofContinuousOn_le_of_bound u.continuousOn_toFun hb
  simpa only [timeH1.toFunL2, ← mul_assoc, Real.mul_self_sqrt hT] using h

theorem timeL2.eq_zero_of_coercive_mass_dual
    (hT : 0 ≤ T) (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (A : V →L[ℝ] V →L[ℝ] ℝ)
    (hAsym : ∀ x y, A x y = A y x) (hApos : ∀ x, 0 ≤ A x x)
    (u : timeL2 V T) (r : timeL2 H T) (D : timeH1 (V →L[ℝ] ℝ) T)
    (hD0 : D.initial = 0)
    (hDd : ∀ᵐ t ∂timeMeasure T, ∀ z,
      D.deriv t z = -A (u t) z + inner ℝ (r t) (J z))
    {c L : ℝ} (hsmall : L * T < c)
    (hmass : ∀ᵐ t ∂timeMeasure T, c * ‖J (u t)‖ ^ 2 ≤ D.toFun t (u t))
    (hr : ∀ᵐ t ∂timeMeasure T, ‖r t‖ ≤ L * ‖J (u t)‖) : u = 0 := by
  let U : timeH1 V T := timeH1.mk 0 u
  let P : timeH1 H T := timeH1.mk 0 r
  let Ju : timeL2 H T := J.compLpL 2 (timeMeasure T) u
  have hJu : Ju =ᵐ[timeMeasure T] fun t => J (u t) := J.coeFn_compLpL u
  let Jstar : H →L[ℝ] V →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ H) J
  obtain ⟨AU, hAU0, hAU, hAUd⟩ := exists_timeH1_comp_clm (-A) U
  obtain ⟨JP, hJP0, hJP, hJPd⟩ := exists_timeH1_comp_clm Jstar P
  have hD : D = AU + JP := by
    apply timeH1.ext
    · simp only [timeH1.initial_add, hAU0, hJP0, U, P, timeH1.initial_mk,
        map_zero, add_zero, hD0]
    · apply Lp.ext
      filter_upwards [hDd, hAUd, hJPd, Lp.coeFn_add AU.deriv JP.deriv] with t ht hAt hPt hadd
      rw [timeH1.deriv_add, hadd, Pi.add_apply, hAt, hPt]
      ext z
      exact ht z
  have hDval (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (z : V) :
      D.toFun t z = -A (U.toFun t) z + inner ℝ (P.toFun t) (J z) := by
    rw [hD, timeH1.toFun_add _ _ ht, hAU t ht, hJP t ht]
    rfl
  have hUmem : MemLp U.toFun 2 (timeMeasure T) := memLp_of_continuousOn U.continuousOn_toFun
  have hPmem : MemLp P.toFun 2 (timeMeasure T) := memLp_of_continuousOn P.continuousOn_toFun
  have hDm : MemLp D.toFun 2 (timeMeasure T) := memLp_of_continuousOn D.continuousOn_toFun
  have hAint : Integrable (fun t => A (U.toFun t) (u t)) (timeMeasure T) :=
    integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => A)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      hUmem (Lp.memLp u)
  have hDint : Integrable (fun t => D.toFun t (u t)) (timeMeasure T) :=
    integrable_bilinear_of_apply_aestronglyMeasurable
      (fun _ => ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ))
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      hDm (Lp.memLp u)
  have hPint : Integrable (fun t => inner ℝ (P.toFun t) (J (u t))) (timeMeasure T) :=
    integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => innerSL ℝ)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      hPmem (J.comp_memLp' (Lp.memLp u))
  obtain ⟨Q, hQ0, hQ, hQd⟩ := exists_timeH1_bilin A U U
  have hQint : (∫ t, Q.deriv t ∂timeMeasure T) =
      2 * ∫ t, A (U.toFun t) (u t) ∂timeMeasure T := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hQd] with t ht
    change Q.deriv t = 2 * A (U.toFun t) (u t)
    rw [ht]
    change A (u t) (U.toFun t) + A (U.toFun t) (u t) = _
    rw [hAsym]
    ring
  have hAenergy : 2 * (∫ t, A (U.toFun t) (u t) ∂timeMeasure T) =
      A (U.toFun T) (U.toFun T) := by
    have hi := Q.toFun_sub_toFun (t₀ := 0) (t₁ := T) ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩
    rw [intervalIntegral.integral_of_le hT, setIntegral_congr_set Ioc_ae_eq_Icc] at hi
    change _ = ∫ t, Q.deriv t ∂timeMeasure T at hi
    rw [hQint, hQ T ⟨hT, le_rfl⟩, timeH1.toFun_zero, hQ0] at hi
    simpa only [U, timeH1.initial_mk, map_zero, zero_apply, sub_zero] using hi.symm
  have henergy : (∫ t, D.toFun t (u t) ∂timeMeasure T) ≤
      ∫ t, inner ℝ (P.toFun t) (J (u t)) ∂timeMeasure T := by
    have hi : (∫ t, D.toFun t (u t) ∂timeMeasure T) =
        -(∫ t, A (U.toFun t) (u t) ∂timeMeasure T) +
          ∫ t, inner ℝ (P.toFun t) (J (u t)) ∂timeMeasure T := by
      rw [← integral_neg]
      have hi := integral_add hAint.neg hPint
      simp only [Pi.neg_apply] at hi
      rw [← hi]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hDval t ht (u t)
    rw [hi]
    have := hApos (U.toFun T)
    linarith only [hAenergy, this]
  have hrnorm : ‖r‖ ≤ L * ‖Ju‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hr, hJu] with t ht hJt
    simpa only [hJt] using ht
  have hpnorm : ‖P.toFunL2‖ ≤ T * ‖r‖ :=
    norm_toFunL2_le_of_initial_zero hT P rfl
  have hcross : (∫ t, inner ℝ (P.toFun t) (J (u t)) ∂timeMeasure T) ≤
      L * T * ‖Ju‖ ^ 2 := by
    have heq : (∫ t, inner ℝ (P.toFun t) (J (u t)) ∂timeMeasure T) =
        inner ℝ P.toFunL2 Ju := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coeFn_ofContinuousOn P.continuousOn_toFun, hJu] with t hpt hjt
      change inner ℝ (P.toFun t) (J (u t)) =
        inner ℝ (ofContinuousOn P.continuousOn_toFun t) (Ju t)
      rw [hpt, hjt]
    rw [heq]
    calc
      inner ℝ P.toFunL2 Ju ≤ ‖P.toFunL2‖ * ‖Ju‖ := real_inner_le_norm _ _
      _ ≤ (T * (L * ‖Ju‖)) * ‖Ju‖ :=
        mul_le_mul_of_nonneg_right
          (hpnorm.trans (mul_le_mul_of_nonneg_left hrnorm hT)) (norm_nonneg _)
      _ = L * T * ‖Ju‖ ^ 2 := by ring
  have hmassint : c * ‖Ju‖ ^ 2 ≤ ∫ t, D.toFun t (u t) ∂timeMeasure T := by
    have hi := integral_mono_ae ((J.comp_memLp' (Lp.memLp u)).norm.integrable_sq.const_mul c)
      hDint hmass
    rw [integral_const_mul] at hi
    have hn : (∫ t, ‖J (u t)‖ ^ 2 ∂timeMeasure T) = ‖Ju‖ ^ 2 := by
      rw [norm_sq_eq_integral]
      exact integral_congr_ae (hJu.symm.fun_comp fun z => ‖z‖ ^ 2)
    simp only [Function.comp_apply] at hi
    rwa [hn] at hi
  have hJunorm : ‖Ju‖ = 0 := by
    have hb := hmassint.trans (henergy.trans hcross)
    by_contra hn
    have hp : 0 < ‖Ju‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    exact (not_le.mpr hsmall) (le_of_mul_le_mul_right hb (sq_pos_of_pos hp))
  have hJuzero : Ju = 0 := norm_eq_zero.mp hJunorm
  apply Lp.ext
  filter_upwards [hJu, Lp.coeFn_zero (E := H) (p := 2) (μ := timeMeasure T),
    Lp.coeFn_zero (E := V) (p := 2) (μ := timeMeasure T)] with t hjt hht hvt
  simp only [Pi.zero_apply] at hht hvt
  rw [hvt]
  apply hJ
  rw [map_zero, ← hjt, hJuzero, hht]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
