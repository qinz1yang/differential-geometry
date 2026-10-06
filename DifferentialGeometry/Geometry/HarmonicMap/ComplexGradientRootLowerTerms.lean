import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientGraphResidualBounds
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientNormalizedConductivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Set Metric Filter Manifold Bundle DifferentialGeometry MeasureTheory
open DifferentialGeometry.Geometry DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped ContDiff Manifold Topology Interval


set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.Elementwise

private theorem root_lower_spin_bound (K : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Analysis.planarMatrixSpin K‖ ≤
      2 * ‖complexPlaneMatrixOperator K - ContinuousLinearMap.id ℝ ℂ‖ := by
  let D := complexPlaneMatrixOperator K - ContinuousLinearMap.id ℝ ℂ
  have heq : Analysis.planarMatrixSpin K = D 1 + Complex.I * D Complex.I := by
    apply Complex.ext <;>
      simp [Analysis.planarMatrixSpin, D, complexPlaneMatrixOperator, Complex.real_smul]
    all_goals ring
  have h1 : ‖D 1‖ ≤ ‖D‖ := by simpa using D.le_opNorm (1 : ℂ)
  have hI : ‖Complex.I * D Complex.I‖ ≤ ‖D‖ := by
    simpa only [norm_mul, Complex.norm_I, one_mul, mul_one] using D.le_opNorm Complex.I
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add h1 hI).trans_eq (by ring))

theorem DifferentialGeometry.Geometry.chartLeadingPlaneProjection_root_lower_term_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0)
    {N : E} (hN : chartLeadingPlaneProjection g p x b N = 0)
    (hunit : chartGramBilin g p x N N = 1)
    (L : ℂ →L[ℝ] E)
    (hL : ∀ w, L w = (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)) (c : ℂ)
    {m : ℕ} (hm : 1 ≤ m) {H : ℂ → ℝ}
    (hH : ContDiffAt ℝ 2 H 0) (hH0 : H 0 = 0) (hDH : fderiv ℝ H 0 = 0)
    (hHess : ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) :
    let Q := chartGramBilin g p x
    let proj := chartLeadingPlaneProjection g p x b
    let dirs : Fin 2 → ℂ := ![1, Complex.I]
    let Y : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) → E := fun q =>
      extChartAt 𝓘(ℝ, E) p x + L (q.1.1 - c) + q.1.2 • N
    let V : (ℂ →L[ℝ] ℝ) → Fin 2 → E := fun l i => L (dirs i) + l (dirs i) • N
    let G : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q i j =>
      chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y q)) (V q.2 i) (V q.2 j)
    let A : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q =>
      Analysis.planarConductivity (G q 0 0) (G q 1 1) (G q 0 1)
    let theta : (ℂ →L[ℝ] ℝ) → E →L[ℝ] ℝ := fun l => Q N - l.comp proj
    let Phi : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) → ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → ℝ :=
      fun T q => ∑ i : Fin 2, ∑ j : Fin 2,
        A q i j * (T (dirs i) (dirs j) +
          theta q.2 (chartChristoffelContraction g p (V q.2 i) (V q.2 j) (Y q)))
    let R : ℂ → (ℂ →L[ℝ] ℝ) := Analysis.complexPowerNormalizedGradient m H
    let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
    let T2 : ℂ → ℂ → (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := fun zeta w =>
      (fderiv ℝ R (zeta * w)).comp
        (ContinuousLinearMap.mul ℝ ℂ (((zeta * w) ^ m)⁻¹))
    let Jet : Type := ℝ × (ℂ →L[ℝ] ℝ)
    let J1 : ℂ → Jet := fun w => (H w, R w)
    let J2 : ℂ → ℂ → Jet := fun zeta w => (H (zeta * w), R (zeta * w))
    let J : ℂ → ℂ → ℝ → Jet := fun zeta w t => (1 - t) • J2 zeta w + t • J1 w
    let PhiRoot : ℂ → ℂ → Jet → ℝ := fun zeta w j =>
      Phi (T2 zeta w) ((P w, j.1), j.2)
    let duals : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]
    let betaRoot : ℂ → ℂ → Fin 2 → ℝ := fun zeta w i =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (PhiRoot zeta w) (J zeta w t) (0, duals i)
    let cRoot : ℂ → ℂ → ℝ := fun zeta w =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (PhiRoot zeta w) (J zeta w t) (1, 0)
    let A1 : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => A ((P w, H w), R w)
    let K : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => if w = 0 then 1 else
      Analysis.planarComplexMulMatrix ((w ^ m)⁻¹) * A1 w *
        Analysis.planarComplexMulMatrix (w ^ m)
    let bTilde : ℂ → ℂ → ℂ := fun zeta w =>
      star (w ^ m) * ((betaRoot zeta w 0 : ℂ) + (betaRoot zeta w 1 : ℂ) * Complex.I) -
        ((m : ℂ) / w) * Analysis.planarMatrixSpin (K w)
    let cTilde : ℂ → ℂ → ℝ := fun zeta w => ‖w ^ m‖ ^ 2 * cRoot zeta w
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧
      ∀ zeta : ℂ, zeta ^ (m + 1) = 1 →
        bTilde zeta 0 = 0 ∧ cTilde zeta 0 = 0 ∧
        ∀ w ∈ Metric.ball (0 : ℂ) ε,
          (w ≠ 0 →
            (∀ i : Fin 2, IntervalIntegrable
              (fun t => fderiv ℝ (PhiRoot zeta w) (J zeta w t) (0, duals i))
              volume 0 1) ∧
            IntervalIntegrable
              (fun t => fderiv ℝ (PhiRoot zeta w) (J zeta w t) (1, 0)) volume 0 1 ∧
            (∀ i : Fin 2, ‖w‖ ^ m * ‖betaRoot zeta w i‖ ≤ C * ‖w‖) ∧
            ‖w‖ ^ (2 * m) * ‖cRoot zeta w‖ ≤ C * ‖w‖ ^ m) ∧
          ‖bTilde zeta w‖ ≤ C * ‖w‖ ∧
          ‖cTilde zeta w‖ ≤ C * ‖w‖ ^ m
 := by
  classical
  intro Q proj dirs Y V G A theta Phi R P T2 Jet J1 J2 J PhiRoot duals betaRoot cRoot A1 K
    bTilde cTilde
  let q0 : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) := ((c, 0), 0)
  obtain ⟨rΦ, B, hrΦ, _hrΦ1, hB, hΦ⟩ :=
    chartLeadingPlaneProjection_graph_residual_jet_bounds g hsrc hb hnull hN hunit L hL c
  change ∀ q ∈ ball q0 rΦ, Y q ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
    0 < G q 0 0 * G q 1 1 - G q 0 1 ^ 2 ∧
    ∀ T : ℂ →L[ℝ] ℂ →L[ℝ] ℝ, ContDiffAt ℝ 1 (Phi T) q ∧
      ‖fderiv ℝ (fun j : Jet => Phi T ((q.1.1, j.1), j.2)) (q.1.2, q.2) (1, 0)‖ ≤
        B * (‖T‖ + 1) ∧
      ‖(fderiv ℝ (fun j : Jet => Phi T ((q.1.1, j.1), j.2)) (q.1.2, q.2)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℂ →L[ℝ] ℝ))‖ ≤
        B * (‖q - q0‖ * ‖T‖ + 1) at hΦ
  obtain ⟨hPζ, CJ, hCJ, hJnear⟩ :=
    chartLeadingPlaneProjection_interpolated_root_slope_bound
      g hsrc hb hnull hN hunit L hL c hm hH hH0 hDH hHess
  have hJdist : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖((P w, (J ζ w t).1), (J ζ w t).2) - q0‖ ≤ CJ * ‖w‖ := by
    filter_upwards [hJnear] with w hw
    intro ζ hζ t ht
    have hh := (hw ζ hζ t ht).2
    change ‖((1 - t) • ((P (ζ * w), H (ζ * w)), R (ζ * w)) +
      t • ((P w, H w), R w)) - q0‖ ≤ CJ * ‖w‖ at hh
    have heq : (1 - t) • ((P (ζ * w), H (ζ * w)), R (ζ * w)) +
        t • ((P w, H w), R w) = ((P w, (J ζ w t).1), (J ζ w t).2) := by
      apply Prod.ext
      · apply Prod.ext
        · change (1 - t) • P (ζ * w) + t • P w = P w
          have hP : P (ζ * w) = P w := hPζ ζ hζ w
          rw [hP, ← add_smul, sub_add_cancel, one_smul]
        · rfl
      · rfl
    simpa only [heq] using hh
  obtain ⟨_hR0, rR, hrR, KR, hKR, _hRsize, hDR, _hRLip⟩ :=
    Analysis.exists_normalized_gradient_bounds_of_hessian_order hm hH hDH hHess
  change ∀ v ∈ ball (0 : ℂ) rR, v ≠ 0 →
    DifferentiableAt ℝ R v ∧ ‖fderiv ℝ R v‖ ≤ KR at hDR
  obtain ⟨_hA0, _hKop, _hK0, _hKC1, _hDK0, CK, hCK, _hAnear, hKnear, _hphysical⟩ :=
    chartLeadingPlaneProjection_normalized_conductivity
      g hsrc hb hnull hN hunit L hL c hm hH hH0 hDH hHess
  have hKbound : ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖complexPlaneMatrixOperator (K w) - ContinuousLinearMap.id ℝ ℂ‖ ≤ CK * ‖w‖ ^ 2 := by
    filter_upwards [hKnear] with w hw
    exact hw.1
  have hsmall : ∀ᶠ w in 𝓝 (0 : ℂ), CJ * ‖w‖ < rΦ := by
    have hc : ContinuousAt (fun w : ℂ => CJ * ‖w‖) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa using hrΦ))
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ),
      w ∈ ball (0 : ℂ) rR ∧ CJ * ‖w‖ < rΦ ∧
      ‖complexPlaneMatrixOperator (K w) - ContinuousLinearMap.id ℝ ℂ‖ ≤ CK * ‖w‖ ^ 2 ∧
      ∀ ζ : ℂ, ζ ^ (m + 1) = 1 → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖((P w, (J ζ w t).1), (J ζ w t).2) - q0‖ ≤ CJ * ‖w‖ := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hrR, hsmall, hKbound, hJdist]
      with w hw hs hk hj
    exact ⟨hw, hs, hk, hj⟩
  obtain ⟨ε0, hε0, hεnear⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := min ε0 1
  let U := B * (CJ * KR + KR + 2)
  let C := 2 * U + 2 * (m : ℝ) * CK + 1
  have hU : 0 < U := by dsimp [U]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hUC : U ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hCK.le]
  have hUb : B * (CJ * KR + 1) ≤ U := by
    dsimp [U]
    nlinarith [mul_nonneg hB.le hKR.le]
  have hUc : B * (KR + 1) ≤ U := by
    dsimp [U]
    nlinarith [mul_nonneg hB.le (mul_nonneg hCJ.le hKR.le)]
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)
  refine ⟨ε, C, lt_min hε0 zero_lt_one, min_le_right _ _, hC, ?_⟩
  intro ζ hζ
  have hbzero : bTilde ζ 0 = 0 := by simp [bTilde, zero_pow hm0]
  have hczero : cTilde ζ 0 = 0 := by simp [cTilde, zero_pow hm0]
  refine ⟨hbzero, hczero, ?_⟩
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    simp only [hbzero, hczero, norm_zero, zero_pow hm0, mul_zero, le_refl,
      ne_eq, not_true_eq_false, false_implies, and_self]
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hr1 : ‖w‖ ≤ 1 := (show ‖w‖ < ε from by simpa using hw).le.trans
    (min_le_right ε0 1)
  have hwm := hεnear (ball_subset_ball (min_le_left ε0 1) hw)
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ (by omega)
  have hζw : ζ * w ∈ ball (0 : ℂ) rR := by
    simpa only [mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul] using hwm.1
  have hζw0 : ζ * w ≠ 0 := by
    have : 0 < ‖ζ * w‖ := by simpa [norm_mul, hζnorm] using hr
    exact norm_pos_iff.mp this
  have hTscaled : ‖w‖ ^ m * ‖T2 ζ w‖ ≤ KR := by
    have hh : ‖T2 ζ w‖ ≤ KR * (‖w‖ ^ m)⁻¹ := by
      calc
        _ ≤ ‖fderiv ℝ R (ζ * w)‖ *
            ‖ContinuousLinearMap.mul ℝ ℂ (((ζ * w) ^ m)⁻¹)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ KR * (‖w‖ ^ m)⁻¹ := by
          simpa only [ContinuousLinearMap.opNorm_mul_apply, norm_inv, norm_pow,
            norm_mul, hζnorm, one_mul] using
            mul_le_mul_of_nonneg_right (hDR (ζ * w) hζw hζw0).2
              (norm_nonneg (ContinuousLinearMap.mul ℝ ℂ (((ζ * w) ^ m)⁻¹)))
    calc
      _ ≤ ‖w‖ ^ m * (KR * (‖w‖ ^ m)⁻¹) :=
        mul_le_mul_of_nonneg_left hh (pow_nonneg hr.le m)
      _ = KR := by field_simp [ne_of_gt hr]
  have hpowr : ‖w‖ ^ m ≤ ‖w‖ := by
    simpa only [pow_one] using pow_le_pow_of_le_one hr.le hr1 hm
  have hpow1 : ‖w‖ ^ m ≤ 1 := hpowr.trans hr1
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ((P w, (J ζ w t).1), (J ζ w t).2) ∈ ball q0 rΦ := by
    rw [mem_ball, dist_eq_norm]
    exact (hwm.2.2.2 ζ hζ t ht).trans_lt hwm.2.1
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 (PhiRoot ζ w) (J ζ w t) ∧
      ‖fderiv ℝ (PhiRoot ζ w) (J ζ w t) (1, 0)‖ ≤ B * (‖T2 ζ w‖ + 1) ∧
      ‖(fderiv ℝ (PhiRoot ζ w) (J ζ w t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℂ →L[ℝ] ℝ))‖ ≤
        B * (CJ * ‖w‖ * ‖T2 ζ w‖ + 1) := by
    have hh := (hΦ _ (hq t ht)).2.2 (T2 ζ w)
    refine ⟨?_, hh.2.1, ?_⟩
    · exact ContDiffAt.comp (f := fun j : Jet => ((P w, j.1), j.2))
        (g := Phi (T2 ζ w)) (J ζ w t) hh.1 (by fun_prop)
    · have hnorm := mul_le_mul_of_nonneg_right
        (hwm.2.2.2 ζ hζ t ht) (norm_nonneg (T2 ζ w))
      exact hh.2.2.trans (mul_le_mul_of_nonneg_left
        (add_le_add hnorm (le_refl (1 : ℝ))) hB.le)
  have hJcont : Continuous (J ζ w) := by dsimp [J]; fun_prop
  have hDcont (v : Jet) : ContinuousOn
      (fun t => fderiv ℝ (PhiRoot ζ w) (J ζ w t) v) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((((hpoint t ht).1.continuousAt_fderiv one_ne_zero).comp
      hJcont.continuousAt).clm_apply continuousAt_const).continuousWithinAt
  have hbetaInt (i : Fin 2) : IntervalIntegrable
      (fun t => fderiv ℝ (PhiRoot ζ w) (J ζ w t) (0, duals i)) volume 0 1 :=
    (hDcont (0, duals i)).intervalIntegrable_of_Icc zero_le_one
  have hcInt : IntervalIntegrable
      (fun t => fderiv ℝ (PhiRoot ζ w) (J ζ w t) (1, 0)) volume 0 1 :=
    (hDcont (1, 0)).intervalIntegrable_of_Icc zero_le_one
  have hdual (i : Fin 2) : ‖duals i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    fin_cases i
    · simpa [duals] using Complex.abs_re_le_norm v
    · simpa [duals] using Complex.abs_im_le_norm v
  have hbeta (i : Fin 2) : ‖betaRoot ζ w i‖ ≤ B * (CJ * ‖w‖ * ‖T2 ζ w‖ + 1) := by
    have hbound : ∀ t ∈ uIoc (0 : ℝ) 1,
        ‖fderiv ℝ (PhiRoot ζ w) (J ζ w t) (0, duals i)‖ ≤
          B * (CJ * ‖w‖ * ‖T2 ζ w‖ + 1) := by
      intro t ht
      rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      let D := (fderiv ℝ (PhiRoot ζ w) (J ζ w t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℂ →L[ℝ] ℝ))
      change ‖D (duals i)‖ ≤ _
      exact ((D.le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg D) (hdual i))).trans (hpoint t ht').2.2
    simpa only [betaRoot, sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hc : ‖cRoot ζ w‖ ≤ B * (‖T2 ζ w‖ + 1) := by
    have hbound : ∀ t ∈ uIoc (0 : ℝ) 1,
        ‖fderiv ℝ (PhiRoot ζ w) (J ζ w t) (1, 0)‖ ≤ B * (‖T2 ζ w‖ + 1) := by
      intro t ht
      rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
      exact (hpoint t ⟨ht.1.le, ht.2⟩).2.1
    simpa only [cRoot, sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hbweighted (i : Fin 2) : ‖w‖ ^ m * ‖betaRoot ζ w i‖ ≤ U * ‖w‖ := by
    calc
      _ ≤ ‖w‖ ^ m * (B * (CJ * ‖w‖ * ‖T2 ζ w‖ + 1)) :=
        mul_le_mul_of_nonneg_left (hbeta i) (pow_nonneg hr.le m)
      _ = B * (CJ * ‖w‖ * (‖w‖ ^ m * ‖T2 ζ w‖) + ‖w‖ ^ m) := by ring
      _ ≤ B * (CJ * ‖w‖ * KR + ‖w‖) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hTscaled (by positivity)) hpowr) hB.le
      _ = (B * (CJ * KR + 1)) * ‖w‖ := by ring
      _ ≤ U * ‖w‖ := mul_le_mul_of_nonneg_right hUb hr.le
  have hcweighted : ‖w‖ ^ (2 * m) * ‖cRoot ζ w‖ ≤ U * ‖w‖ ^ m := by
    calc
      _ ≤ ‖w‖ ^ (2 * m) * (B * (‖T2 ζ w‖ + 1)) :=
        mul_le_mul_of_nonneg_left hc (pow_nonneg hr.le _)
      _ = B * (‖w‖ ^ m * (‖w‖ ^ m * ‖T2 ζ w‖) + ‖w‖ ^ m * ‖w‖ ^ m) := by
        rw [show 2 * m = m + m by omega, pow_add]
        ring
      _ ≤ B * (‖w‖ ^ m * KR + ‖w‖ ^ m) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hTscaled (pow_nonneg hr.le m))
          (mul_le_of_le_one_right (pow_nonneg hr.le m) hpow1)) hB.le
      _ = (B * (KR + 1)) * ‖w‖ ^ m := by ring
      _ ≤ U * ‖w‖ ^ m := mul_le_mul_of_nonneg_right hUc (pow_nonneg hr.le m)
  have hprincipal :
      ‖star (w ^ m) * ((betaRoot ζ w 0 : ℂ) + (betaRoot ζ w 1 : ℂ) * Complex.I)‖ ≤
        2 * U * ‖w‖ := by
    calc
      _ = ‖w‖ ^ m * ‖(betaRoot ζ w 0 : ℂ) + (betaRoot ζ w 1 : ℂ) * Complex.I‖ := by
        simp only [norm_mul, norm_star, norm_pow]
      _ ≤ ‖w‖ ^ m * (‖betaRoot ζ w 0‖ + ‖betaRoot ζ w 1‖) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr.le m)
        simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real] using
          norm_add_le (betaRoot ζ w 0 : ℂ) ((betaRoot ζ w 1 : ℂ) * Complex.I)
      _ = ‖w‖ ^ m * ‖betaRoot ζ w 0‖ + ‖w‖ ^ m * ‖betaRoot ζ w 1‖ := by ring
      _ ≤ U * ‖w‖ + U * ‖w‖ := add_le_add (hbweighted 0) (hbweighted 1)
      _ = 2 * U * ‖w‖ := by ring
  have hspin : ‖Analysis.planarMatrixSpin (K w)‖ ≤ 2 * CK * ‖w‖ ^ 2 :=
    (root_lower_spin_bound (K w)).trans
      ((mul_le_mul_of_nonneg_left hwm.2.2.1 (by norm_num)).trans_eq (by ring))
  have hcorrection : ‖((m : ℂ) / w) * Analysis.planarMatrixSpin (K w)‖ ≤
      (2 * (m : ℝ) * CK) * ‖w‖ := by
    calc
      _ = ((m : ℝ) / ‖w‖) * ‖Analysis.planarMatrixSpin (K w)‖ := by
        simp only [norm_mul, norm_div, Complex.norm_natCast]
      _ ≤ ((m : ℝ) / ‖w‖) * (2 * CK * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hspin (by positivity)
      _ = (2 * (m : ℝ) * CK) * ‖w‖ := by field_simp [ne_of_gt hr]
  refine ⟨fun _ => ⟨hbetaInt, hcInt, fun i => (hbweighted i).trans
      (mul_le_mul_of_nonneg_right hUC hr.le), hcweighted.trans
        (mul_le_mul_of_nonneg_right hUC (pow_nonneg hr.le m))⟩, ?_, ?_⟩
  · change ‖_ - _‖ ≤ _
    exact (norm_sub_le _ _).trans ((add_le_add hprincipal hcorrection).trans
      (by dsimp [C]; nlinarith))
  · change ‖‖w ^ m‖ ^ 2 * cRoot ζ w‖ ≤ _
    have heq : ‖‖w ^ m‖ ^ 2 * cRoot ζ w‖ = ‖w‖ ^ (2 * m) * ‖cRoot ζ w‖ := by
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), norm_pow]
      rw [← pow_mul, Nat.mul_comm]
    rw [heq]
    exact hcweighted.trans (mul_le_mul_of_nonneg_right hUC (pow_nonneg hr.le m))
