/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous.DifferenceQuotient
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.MetricDifferentiability

noncomputable section

open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

namespace DifferentialGeometry.QuasiconformalACL

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def transverseMeasure (ν : Measure (V × ℝ)) (a b : ℝ) : Measure V :=
  (ν.restrict (univ ×ˢ Icc a b)).map Prod.fst

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem transverseMeasure_apply (ν : Measure (V × ℝ)) (a b : ℝ)
    {s : Set V} (hs : MeasurableSet s) :
    transverseMeasure ν a b s = ν (s ×ˢ Icc a b) := by
  rw [transverseMeasure, Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (measurable_fst hs)]
  congr 1
  ext x
  simp

instance transverseMeasure_isFiniteMeasureOnCompacts (ν : Measure (V × ℝ))
    [IsFiniteMeasureOnCompacts ν] (a b : ℝ) :
    IsFiniteMeasureOnCompacts (transverseMeasure ν a b) where
  lt_top_of_isCompact K hK := by
    rw [transverseMeasure_apply ν a b hK.measurableSet]
    exact (hK.prod isCompact_Icc).measure_lt_top

theorem ae_ball_measure_bound (ρ σ : Measure V) [IsAddHaarMeasure ρ]
    [IsLocallyFiniteMeasure σ] :
    ∀ᵐ z ∂ρ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (σ (closedBall z r)).toReal ≤ C * r ^ Module.finrank ℝ V := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv σ ρ, Measure.rnDeriv_lt_top σ ρ]
    with z hz hfin
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfin.ne
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      σ (closedBall z r) / ρ (closedBall z r) < N :=
    hz.eventually (Iio_mem_nhds hN)
  refine ⟨(N : ℝ) * (ρ (ball (0 : V) 1)).toReal + 1, by positivity, ?_⟩
  filter_upwards [he, self_mem_nhdsWithin] with r hr hrpos
  have hr0 : 0 < r := hrpos
  have hb : σ (closedBall z r) ≤ (N : ℝ≥0∞) * ρ (closedBall z r) :=
    ((ENNReal.div_lt_iff
      (Or.inl (measure_closedBall_pos ρ z hr0).ne')
      (Or.inl measure_closedBall_lt_top.ne)).mp hr).le
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) measure_closedBall_lt_top.ne) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    addHaar_closedBall ρ z hr0.le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr0.le _)] at ht
  nlinarith [pow_nonneg hr0.le (Module.finrank ℝ V)]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem vertical_ball_fiber_bound (z : V) (w : V × ℝ) (a b : ℝ)
    {r : ℝ} (_hr : 0 < r) (hr1 : r < 1) :
    (volume.restrict (uIoc a b)) {t : ℝ | w ∈ closedBall (z, t) r} ≤
      (closedBall z r ×ˢ Icc (min a b - 1) (max a b + 1)).indicator
        (fun _ => ENNReal.ofReal (2 * r)) w := by
  have hfiber : MeasurableSet {t : ℝ | w ∈ closedBall (z, t) r} :=
    isClosed_le (continuous_const.dist (continuous_const.prodMk continuous_id))
      continuous_const |>.measurableSet
  rw [Measure.restrict_apply hfiber]
  have hmem {t : ℝ} (ht : t ∈ {t : ℝ | w ∈ closedBall (z, t) r} ∩ uIoc a b) :
      dist w.1 z ≤ r ∧ |w.2 - t| ≤ r ∧ min a b < t ∧ t ≤ max a b := by
    have hd := ht.1
    change dist w (z, t) ≤ r at hd
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq] at hd
    exact ⟨hd.1, hd.2, ht.2.1, ht.2.2⟩
  by_cases hw : w ∈ closedBall z r ×ˢ Icc (min a b - 1) (max a b + 1)
  · rw [indicator_of_mem hw]
    calc
      _ ≤ volume (Icc (w.2 - r) (w.2 + r)) := by
        apply measure_mono
        intro t ht
        obtain ⟨_, habs, _, _⟩ := hmem ht
        rw [abs_le] at habs
        constructor <;> linarith
      _ = ENNReal.ofReal (2 * r) := by
        rw [Real.volume_Icc]
        congr 1
        ring
  · rw [indicator_of_notMem hw]
    suffices hempty :
        {t : ℝ | w ∈ closedBall (z, t) r} ∩ uIoc a b = ∅ by
      rw [hempty, measure_empty]
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨hz, habs, hlo, hhi⟩ := hmem ht
    apply hw
    refine ⟨hz, ?_, ?_⟩ <;> rw [abs_le] at habs <;> linarith

theorem lintegral_ball_measure_le (ν : Measure (V × ℝ)) [SFinite ν]
    (z : V) (a b : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫⁻ t in uIoc a b, ν (closedBall (z, t) r)) ≤
      ENNReal.ofReal (2 * r) *
        transverseMeasure ν (min a b - 1) (max a b + 1) (closedBall z r) := by
  classical
  let S : Set (ℝ × (V × ℝ)) := {p | dist p.2 (z, p.1) ≤ r}
  have hS : MeasurableSet S :=
    (isClosed_le (continuous_snd.dist (continuous_const.prodMk continuous_fst))
      continuous_const).measurableSet
  let k : ℝ → (V × ℝ) → ℝ≥0∞ := fun t w => S.indicator (fun _ => 1) (t, w)
  have hk : Measurable (Function.uncurry k) :=
    measurable_const.indicator hS
  calc
    _ = ∫⁻ t in uIoc a b, ∫⁻ w, k t w ∂ν := by
      apply lintegral_congr
      intro t
      change ν (closedBall (z, t) r) =
        ∫⁻ w, (closedBall (z, t) r).indicator 1 w ∂ν
      rw [lintegral_indicator_one measurableSet_closedBall]
    _ = ∫⁻ w, (∫⁻ t in uIoc a b, k t w) ∂ν :=
      lintegral_lintegral_swap hk.aemeasurable
    _ ≤ ∫⁻ w, (closedBall z r ×ˢ Icc (min a b - 1) (max a b + 1)).indicator
        (fun _ => ENNReal.ofReal (2 * r)) w ∂ν := by
      apply lintegral_mono
      intro w
      change (∫⁻ t in uIoc a b, {t : ℝ | w ∈ closedBall (z, t) r}.indicator 1 t) ≤ _
      have hfiber : MeasurableSet {t : ℝ | w ∈ closedBall (z, t) r} :=
        hS.preimage (show Measurable (fun t : ℝ => (t, w)) from
          measurable_id.prodMk measurable_const)
      rw [lintegral_indicator_one hfiber]
      exact vertical_ball_fiber_bound z w a b hr hr1
    _ = _ := by
      rw [lintegral_indicator_const (measurableSet_closedBall.prod measurableSet_Icc),
        transverseMeasure_apply ν _ _ measurableSet_closedBall]

open MetricDifferentiability CurveAbsoluteContinuity

theorem integral_differenceQuotient_pow_le (μ : Measure (V × ℝ)) [IsAddHaarMeasure μ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) {H : ℝ} (hH : 0 < H)
    (hf : ∀ x y w : V × ℝ, dist y x ≤ dist w x →
      dist (f y) (f x) ≤ H * dist (f w) (f x))
    (z : V) (a b : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    (∫ t in uIoc a b,
        ‖differenceQuotient (fun t => f (z, t)) h t‖ ^ Module.finrank ℝ (V × ℝ)) ≤
      (2 * (H ^ Module.finrank ℝ (V × ℝ) / (μ (ball (0 : V × ℝ) 1)).toReal) /
          h ^ Module.finrank ℝ V) *
        (transverseMeasure (imageMeasure μ f) (min a b - 1) (max a b + 1)
          (closedBall z h)).toReal := by
  let c := H ^ Module.finrank ℝ (V × ℝ) / (μ (ball (0 : V × ℝ) 1)).toReal
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let q : ℝ → ℝ := fun t =>
    ‖differenceQuotient (fun t => f (z, t)) h t‖ ^ Module.finrank ℝ (V × ℝ)
  have hq : Continuous q :=
    (continuous_differenceQuotient (f.continuous.comp
      (continuous_const.prodMk continuous_id)) h).norm.pow _
  have hqn (t : ℝ) : 0 ≤ q t := pow_nonneg (norm_nonneg _) _
  have hi : IntegrableOn q (uIoc a b) volume := (hq.intervalIntegrable a b).def'
  have hpoint (t : ℝ) : ENNReal.ofReal (q t) ≤
      ENNReal.ofReal (c / h ^ Module.finrank ℝ (V × ℝ)) *
        imageMeasure μ f (closedBall (z, t) h) := by
    have hd := displacement_pow_le_imageMeasure μ f hH hf (z, t) (z, t + h) hh (by
      simp only [Prod.dist_eq, dist_self, Real.dist_eq, add_sub_cancel_left,
        abs_of_pos hh, max_eq_right hh.le, le_refl])
    have hqeq : q t =
        dist (f (z, t + h)) (f (z, t)) ^ Module.finrank ℝ (V × ℝ) /
          h ^ Module.finrank ℝ (V × ℝ) := by
      simp only [q, differenceQuotient, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hh), mul_pow, inv_pow, dist_eq_norm]
      ring
    have hb : q t ≤ (c / h ^ Module.finrank ℝ (V × ℝ)) *
        (imageMeasure μ f (closedBall (z, t) h)).toReal := by
      rw [hqeq]
      have hp := div_le_div_of_nonneg_right hd
        (pow_nonneg hh.le (Module.finrank ℝ (V × ℝ)))
      simpa only [c, div_mul_eq_mul_div] using hp
    calc
      _ ≤ ENNReal.ofReal ((c / h ^ Module.finrank ℝ (V × ℝ)) *
          (imageMeasure μ f (closedBall (z, t) h)).toReal) :=
        ENNReal.ofReal_le_ofReal hb
      _ = _ := by
        rw [ENNReal.ofReal_mul (div_nonneg hc (pow_nonneg hh.le _)),
          ENNReal.ofReal_toReal
            ((isCompact_closedBall (z, t) h).measure_lt_top (μ := imageMeasure μ f)).ne]
  have henergy :
      ENNReal.ofReal (∫ t in uIoc a b, q t) ≤
        ENNReal.ofReal (c / h ^ Module.finrank ℝ (V × ℝ)) *
          (ENNReal.ofReal (2 * h) *
            transverseMeasure (imageMeasure μ f) (min a b - 1) (max a b + 1)
              (closedBall z h)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hqn)]
    apply (lintegral_mono hpoint).trans
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    exact lintegral_ball_measure_le (imageMeasure μ f) z a b hh hh1
  have hreal := ENNReal.toReal_mono (by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ((isCompact_closedBall z h).measure_lt_top
      (μ := transverseMeasure (imageMeasure μ f) (min a b - 1) (max a b + 1))).ne) henergy
  rw [ENNReal.toReal_ofReal (integral_nonneg hqn), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg hc (pow_nonneg hh.le _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * h)] at hreal
  change (∫ t in uIoc a b, q t) ≤ _
  convert hreal using 1
  dsimp only [c]
  simp only [Module.finrank_prod, Module.finrank_self, pow_succ]
  field_simp

theorem ae_differenceQuotient_energy_bound (μ : Measure (V × ℝ)) [IsAddHaarMeasure μ]
    (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) (hf : HasGlobalDistortion f) (a b : ℝ) :
    ∀ᵐ z ∂ρ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (∫ t in uIoc a b,
        ‖differenceQuotient (fun t => f (z, t)) h t‖ ^ Module.finrank ℝ (V × ℝ)) ≤ C := by
  obtain ⟨H, hH, hcomp⟩ := hf
  let c := H ^ Module.finrank ℝ (V × ℝ) / (μ (ball (0 : V × ℝ) 1)).toReal
  have hc : 0 < c := div_pos (pow_pos hH _)
    (ENNReal.toReal_pos (measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_lt_top.ne)
  filter_upwards [ae_ball_measure_bound ρ
    (transverseMeasure (imageMeasure μ f) (min a b - 1) (max a b + 1))] with z hz
  obtain ⟨C, hC, hz⟩ := hz
  refine ⟨2 * c * C, by positivity, ?_⟩
  filter_upwards [hz, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with h hvol hpos hsmall
  have hh : 0 < h := hpos
  have hp : 0 < h ^ Module.finrank ℝ V := pow_pos hh _
  calc
    _ ≤ (2 * c / h ^ Module.finrank ℝ V) *
        (transverseMeasure (imageMeasure μ f) (min a b - 1) (max a b + 1)
          (closedBall z h)).toReal :=
      integral_differenceQuotient_pow_le μ f hH hcomp z a b hh hsmall
    _ ≤ (2 * c / h ^ Module.finrank ℝ V) * (C * h ^ Module.finrank ℝ V) :=
      mul_le_mul_of_nonneg_left hvol (by positivity)
    _ = 2 * c * C := by field_simp

theorem sq_le_one_add_pow {q : ℝ} (hq : 0 ≤ q) {m : ℕ} (hm : 2 ≤ m) :
    q ^ 2 ≤ 1 + q ^ m := by
  by_cases hq1 : q ≤ 1
  · nlinarith [pow_nonneg hq m]
  · exact (pow_le_pow_right₀ (lt_of_not_ge hq1).le hm).trans (le_add_of_nonneg_left zero_le_one)

theorem ae_absolutelyContinuousOnInterval [Nontrivial V]
    (μ : Measure (V × ℝ)) [IsAddHaarMeasure μ] (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) (hf : HasGlobalDistortion f) (a b : ℝ) :
    ∀ᵐ z ∂ρ, AbsolutelyContinuousOnInterval (fun t => f (z, t)) a b := by
  have hdim : 2 ≤ Module.finrank ℝ (V × ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self]
    have := Module.finrank_pos (R := ℝ) (M := V)
    omega
  filter_upwards [ae_differenceQuotient_energy_bound μ ρ f hf a b] with z hz
  obtain ⟨C, hC, hbound⟩ := hz
  have hg : Continuous (fun t : ℝ => f (z, t)) :=
    f.continuous.comp (continuous_const.prodMk continuous_id)
  apply absolutelyContinuousOnInterval_of_differenceQuotient_bound hg
    (C := (volume (uIoc a b)).toReal + C) (by positivity)
  filter_upwards [hbound] with h hh
  have hd := continuous_differenceQuotient hg h
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (uIoc a b) volume :=
    integrableOn_const (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
  have hp : IntegrableOn
      (fun t => ‖differenceQuotient (fun t => f (z, t)) h t‖ ^ Module.finrank ℝ (V × ℝ))
      (uIoc a b) volume :=
    ((hd.norm.pow (Module.finrank ℝ (V × ℝ))).intervalIntegrable a b).def'
  calc
    _ ≤ ∫ t in uIoc a b, (1 + ‖differenceQuotient (fun t => f (z, t)) h t‖ ^
          Module.finrank ℝ (V × ℝ)) := by
      exact integral_mono_ae ((hd.norm.pow 2).intervalIntegrable a b).def' (hc.add hp)
        (Eventually.of_forall (fun t => sq_le_one_add_pow (norm_nonneg _) hdim))
    _ = (volume (uIoc a b)).toReal +
        ∫ t in uIoc a b, ‖differenceQuotient (fun t => f (z, t)) h t‖ ^
          Module.finrank ℝ (V × ℝ) := by
      rw [integral_add hc hp]
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
        smul_eq_mul, mul_one]
    _ ≤ _ := add_le_add le_rfl hh

theorem ae_absolutelyContinuousOn_all_intervals [Nontrivial V]
    (μ : Measure (V × ℝ)) [IsAddHaarMeasure μ] (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) (hf : HasGlobalDistortion f) :
    ∀ᵐ z ∂ρ, ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun t => f (z, t)) a b := by
  have hall : ∀ᵐ z ∂ρ, ∀ N : ℕ,
      AbsolutelyContinuousOnInterval (fun t => f (z, t)) (-(N : ℝ)) N :=
    ae_all_iff.2 fun N => ae_absolutelyContinuousOnInterval μ ρ f hf (-(N : ℝ)) N
  filter_upwards [hall] with z hz
  intro a b
  obtain ⟨N, hN⟩ := exists_nat_gt (max |a| |b|)
  apply (hz N).mono
  have ha : |a| < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hb : |b| < (N : ℝ) := (le_max_right _ _).trans_lt hN
  rw [abs_lt] at ha hb
  have hNN : -(N : ℝ) ≤ N := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  rw [uIcc_of_le hNN]
  exact uIcc_subset_Icc ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩

theorem ae_absolutelyContinuousOn_linear_coordinates [Nontrivial V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (V × ℝ)) [IsAddHaarMeasure μ] (ρ : Measure V) [IsAddHaarMeasure ρ]
    (e : (V × ℝ) ≃L[ℝ] E) (f : E ≃ₜ E) (hf : HasGlobalDistortion f) :
    ∀ᵐ z ∂ρ, ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun t => f (e (z, t))) a b := by
  let g := (e.toHomeomorph.trans f).trans e.symm.toHomeomorph
  have hg : HasGlobalDistortion g := hf.conjugate e f
  filter_upwards [ae_absolutelyContinuousOn_all_intervals μ ρ g hg] with z hz
  intro a b
  have h := absolutelyContinuousOnInterval_lipschitz_comp (hz a b)
    e.toContinuousLinearMap.lipschitzWith
  change AbsolutelyContinuousOnInterval (fun t => e (e.symm (f (e (z, t))))) a b at h
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

end DifferentialGeometry.QuasiconformalACL
