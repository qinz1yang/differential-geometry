import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakFTC
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.DenseDual
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_timeH1_dual_of_weak_deriv_on
    {a b : ℝ} (hab : a < b) {p q : ℝ → X →L[ℝ] ℝ}
    (hp : MemLp p 2 (volume.restrict (Icc a b)))
    (hq : MemLp q 2 (volume.restrict (Icc a b)))
    (hweak : ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ t in Ioo a b, deriv φ t * p t x) =
        -∫ t in Ioo a b, φ t * q t x) :
    ∃ w : timeH1 (X →L[ℝ] ℝ) (b - a),
      (fun t ↦ p (a + t)) =ᵐ[timeMeasure (b - a)] w.toFun ∧
      w.deriv =ᵐ[timeMeasure (b - a)] fun t ↦ q (a + t) := by
  apply exists_timeH1_of_weak_deriv_on hab hp hq
  intro φ hφ hφc hφs
  have hpI : Integrable p (volume.restrict (Ioo a b)) :=
    (hp.integrable (by norm_num)).mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hqI : Integrable q (volume.restrict (Ioo a b)) :=
    (hq.integrable (by norm_num)).mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hdφp : Integrable (fun t => deriv φ t • p t) (volume.restrict (Ioo a b)) :=
    hpI.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hφ.continuous_deriv (by norm_cast)) hφc.deriv
  have hφq : Integrable (fun t => φ t • q t) (volume.restrict (Ioo a b)) :=
    hqI.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  ext x
  rw [ContinuousLinearMap.integral_apply hdφp, neg_apply,
    ContinuousLinearMap.integral_apply hφq]
  exact hweak x φ hφ hφc hφs

theorem exists_timeH1_dual_of_weak_deriv
    {T : ℝ} (hT : 0 < T) {p q : ℝ → X →L[ℝ] ℝ}
    (hp : MemLp p 2 (timeMeasure T)) (hq : MemLp q 2 (timeMeasure T))
    (hweak : ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo (0 : ℝ) T →
      (∫ t in Ioo (0 : ℝ) T, deriv φ t * p t x) =
        -∫ t in Ioo (0 : ℝ) T, φ t * q t x) :
    ∃ w : timeH1 (X →L[ℝ] ℝ) T, p =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] q := by
  have h := exists_timeH1_dual_of_weak_deriv_on hT hp hq hweak
  rw [sub_zero] at h
  simpa only [zero_add] using h

private theorem scalar_weak_deriv_of_tensor_integrals_on
    {X S E J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup S] [NormedSpace ℝ S]
    [MeasurableSpace E] [Fintype J] {ν : Measure E}
    {a b : ℝ} (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (ι : S →L[ℝ] X) {p q : ℝ → X →L[ℝ] ℝ}
    {W B : ℝ × E → ℝ} {Q : J → ℝ × E → ℝ}
    {R : S → E → ℝ} {D : S → J → E → ℝ}
    (hmass : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * p t (ι x) ∂μ) =
        ∫ z, τ z.1 * W z * R x z.2 ∂μ.prod ν)
    (hdual : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * q t (ι x) ∂μ) =
        (∫ z, τ z.1 * B z * R x z.2 ∂μ.prod ν) -
          ∑ j, ∫ z, τ z.1 * Q j z * D x j z.2 ∂μ.prod ν)
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ z, deriv φ z.1 * W z * R x z.2 ∂μ.prod ν) =
        (∑ j, ∫ z, φ z.1 * Q j z * D x j z.2 ∂μ.prod ν) -
          ∫ z, φ z.1 * B z * R x z.2 ∂μ.prod ν) :
    ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ t in Ioo a b, deriv φ t * p t (ι x)) = -∫ t in Ioo a b, φ t * q t (ι x) := by
  subst μ
  intro x φ hφ hφc hφs
  let μ := volume.restrict (Icc a b)
  have hφm : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hdφm : MemLp (deriv φ) 2 μ :=
    (hφ.continuous_deriv (by simp)).memLp_of_hasCompactSupport hφc.deriv
  have hτint (τ : ℝ → ℝ) (hτ : MemLp τ 2 μ) (L : ℝ → X →L[ℝ] ℝ) :
      (∫ t in Icc a b, hτ.toLp τ t * L t (ι x)) =
        ∫ t in Ioo a b, τ t * L t (ι x) := by
    apply Eq.trans ?_ (setIntegral_congr_set Ioo_ae_eq_Icc).symm
    apply integral_congr_ae
    filter_upwards [hτ.coeFn_toLp] with t ht
    rw [ht]
  have hτprod (τ : ℝ → ℝ) (hτ : MemLp τ 2 μ) (F : ℝ × E → ℝ) (V : E → ℝ) :
      (∫ z, hτ.toLp τ z.1 * F z * V z.2 ∂μ.prod ν) =
        ∫ z, τ z.1 * F z * V z.2 ∂μ.prod ν := by
    apply integral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hτ.coeFn_toLp] with z hz
    rw [hz]
  have hM := hmass (hdφm.toLp (deriv φ)) x
  rw [hτint, hτprod] at hM
  have hQ := hdual (hφm.toLp φ) x
  rw [hτint, hτprod] at hQ
  have hsum : (∑ j, ∫ z, hφm.toLp φ z.1 * Q j z * D x j z.2 ∂(volume.restrict (Icc a b)).prod ν) =
      ∑ j, ∫ z, φ z.1 * Q j z * D x j z.2 ∂(volume.restrict (Icc a b)).prod ν := by
    apply Finset.sum_congr rfl
    intro j _
    exact hτprod φ hφm (Q j) (D x j)
  rw [hsum] at hQ
  have hW := hweak x φ hφ hφc hφs
  exact hM.trans (hW.trans (by linarith only [hQ]))

theorem exists_timeH1_dual_of_tensor_integrals_on
    {X S E J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup S] [NormedSpace ℝ S]
    [MeasurableSpace E] [Fintype J] {ν : Measure E}
    {a b : ℝ} (hab : a < b) (μ : Measure ℝ)
    (hμ : μ = volume.restrict (Icc a b))
    (ι : S →L[ℝ] X) (hdense : DenseRange ι)
    {p q : ℝ → X →L[ℝ] ℝ}
    (hp : MemLp p 2 μ) (hq : MemLp q 2 μ)
    {W B : ℝ × E → ℝ} {Q : J → ℝ × E → ℝ}
    {R : S → E → ℝ} {D : S → J → E → ℝ}
    (hmass : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * p t (ι x) ∂μ) =
        ∫ z, τ z.1 * W z * R x z.2 ∂μ.prod ν)
    (hdual : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * q t (ι x) ∂μ) =
        (∫ z, τ z.1 * B z * R x z.2 ∂μ.prod ν) -
          ∑ j, ∫ z, τ z.1 * Q j z * D x j z.2 ∂μ.prod ν)
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ z, deriv φ z.1 * W z * R x z.2 ∂μ.prod ν) =
        (∑ j, ∫ z, φ z.1 * Q j z * D x j z.2 ∂μ.prod ν) -
          ∫ z, φ z.1 * B z * R x z.2 ∂μ.prod ν) :
    ∃ w : timeH1 (X →L[ℝ] ℝ) (b - a),
      (fun t ↦ p (a + t)) =ᵐ[timeMeasure (b - a)] w.toFun ∧
      w.deriv =ᵐ[timeMeasure (b - a)] fun t ↦ q (a + t) := by
  have hp' : MemLp p 2 (volume.restrict (Icc a b)) := by rw [← hμ]; exact hp
  have hq' : MemLp q 2 (volume.restrict (Icc a b)) := by rw [← hμ]; exact hq
  have hscalar := extend_scalar_weak_deriv_of_denseRange_on ι hdense hp' hq'
    (scalar_weak_deriv_of_tensor_integrals_on μ hμ ι hmass hdual hweak)
  exact exists_timeH1_dual_of_weak_deriv_on hab hp' hq' hscalar

variable [CompleteSpace X] in
theorem timeH1.deriv_eq_of_toFun_ae_eq
    {T : ℝ} {u v : timeH1 X T}
    (huv : u.toFun =ᵐ[timeMeasure T] v.toFun) : u.deriv = v.deriv := by
  by_cases hT : 0 < T
  swap
  · apply Lp.ext
    have hbot : ae (timeMeasure T) = ⊥ :=
      MeasureTheory.ae_eq_bot.mpr (timeMeasure_eq_zero_of_nonpos (le_of_not_gt hT))
    change ∀ᶠ t in ae (timeMeasure T), _
    rw [hbot]
    exact Filter.mem_bot
  have hval : EqOn u.toFun v.toFun (Icc (0 : ℝ) T) :=
    Measure.eqOn_Icc_of_ae_eq (μ := volume) hT.ne huv
      u.continuousOn_toFun v.continuousOn_toFun
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  apply Lp.ext
  filter_upwards [u.ae_hasDerivWithinAt_toFun,
    v.ae_hasDerivWithinAt_toFun, hmem] with t hut hvt ht
  have hIcc : Icc (0 : ℝ) T ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hut' : HasDerivAt u.toFun (u.deriv t) t := hut.hasDerivAt hIcc
  have hvt' : HasDerivAt v.toFun (v.deriv t) t := hvt.hasDerivAt hIcc
  have heq : u.toFun =ᶠ[𝓝 t] v.toFun := by
    filter_upwards [hIcc] with r hr
    exact hval hr
  exact hut'.unique (hvt'.congr_of_eventuallyEq heq)

theorem timeH1.deriv_ae_eq_of_weak_dual_deriv_on
    {a b : ℝ} (hab : a < b) (w : timeH1 (X →L[ℝ] ℝ) (b - a))
    {p q : ℝ → X →L[ℝ] ℝ}
    (hp : MemLp p 2 (volume.restrict (Icc a b)))
    (hq : MemLp q 2 (volume.restrict (Icc a b)))
    (hrep : (fun t ↦ p (a + t)) =ᵐ[timeMeasure (b - a)] w.toFun)
    (hweak : ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ t in Ioo a b, _root_.deriv φ t * p t x) =
        -∫ t in Ioo a b, φ t * q t x) :
    w.deriv =ᵐ[timeMeasure (b - a)] fun t ↦ q (a + t) := by
  obtain ⟨v, hvp, hvq⟩ := exists_timeH1_dual_of_weak_deriv_on hab hp hq hweak
  have hderiv : w.deriv = v.deriv :=
    timeH1.deriv_eq_of_toFun_ae_eq (hrep.symm.trans hvp)
  exact hderiv ▸ hvq

variable {S : Type*} [SeminormedAddCommGroup S] [NormedSpace ℝ S] in
theorem timeH1.deriv_ae_eq_of_dense_weak_dual_deriv_on
    {a b : ℝ} (hab : a < b) (ι : S →L[ℝ] X) (hdense : DenseRange ι)
    (w : timeH1 (X →L[ℝ] ℝ) (b - a))
    {p q : ℝ → X →L[ℝ] ℝ}
    (hp : MemLp p 2 (volume.restrict (Icc a b)))
    (hq : MemLp q 2 (volume.restrict (Icc a b)))
    (hrep : (fun t ↦ p (a + t)) =ᵐ[timeMeasure (b - a)] w.toFun)
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ t in Ioo a b, _root_.deriv φ t * p t (ι x)) =
        -∫ t in Ioo a b, φ t * q t (ι x)) :
    w.deriv =ᵐ[timeMeasure (b - a)] fun t ↦ q (a + t) :=
  timeH1.deriv_ae_eq_of_weak_dual_deriv_on hab w hp hq hrep
    (extend_scalar_weak_deriv_of_denseRange_on ι hdense hp hq hweak)

theorem timeH1.deriv_ae_eq_of_tensor_mass_dual
    {X Y S E J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [SeminormedAddCommGroup S] [NormedSpace ℝ S]
    [MeasurableSpace E] [Fintype J] {ν : Measure E}
    {a b : ℝ} (hab : a < b) (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (ι : S →L[ℝ] X) (hdense : DenseRange ι)
    (mass : Y →L[ℝ] X →L[ℝ] ℝ) (v : Lp Y 2 μ)
    (w : timeH1 (X →L[ℝ] ℝ) (b - a)) (q : Lp (X →L[ℝ] ℝ) 2 μ)
    (hw : ∀ᵐ s ∂timeMeasure (b - a), ∀ z : X, w.toFun s z = mass (v (a + s)) z)
    {W B : ℝ × E → ℝ} {Q : J → ℝ × E → ℝ}
    {R : S → E → ℝ} {D : S → J → E → ℝ}
    (hmass : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * mass (v t) (ι x) ∂μ) = ∫ z, τ z.1 * W z * R x z.2 ∂μ.prod ν)
    (hdual : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * q t (ι x) ∂μ) = (∫ z, τ z.1 * B z * R x z.2 ∂μ.prod ν) -
        ∑ j, ∫ z, τ z.1 * Q j z * D x j z.2 ∂μ.prod ν)
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ z, _root_.deriv φ z.1 * W z * R x z.2 ∂μ.prod ν) =
        (∑ j, ∫ z, φ z.1 * Q j z * D x j z.2 ∂μ.prod ν) -
          ∫ z, φ z.1 * B z * R x z.2 ∂μ.prod ν) :
    w.deriv =ᵐ[timeMeasure (b - a)] fun s => q (a + s) := by
  have hp : MemLp (fun t => mass (v t)) 2 (volume.restrict (Icc a b)) := by
    rw [← hμ]
    exact mass.comp_memLp v
  have hq : MemLp (fun t => q t) 2 (volume.restrict (Icc a b)) := by
    rw [← hμ]
    exact Lp.memLp q
  have hrep : (fun s => mass (v (a + s))) =ᵐ[timeMeasure (b - a)] w.toFun := by
    filter_upwards [hw] with s hs
    exact ContinuousLinearMap.ext (fun z => (hs z).symm)
  exact w.deriv_ae_eq_of_dense_weak_dual_deriv_on hab ι hdense hp hq hrep
    (scalar_weak_deriv_of_tensor_integrals_on μ hμ ι hmass hdual hweak)

variable [CompleteSpace X]

theorem timeH1.integral_dual_deriv_add_deriv_dual
    {T : ℝ} (hT : 0 ≤ T) (w : timeH1 (X →L[ℝ] ℝ) T) (v : timeH1 X T) :
    (∫ t, w.toFun t (v.deriv t) ∂timeMeasure T) +
      (∫ t, w.deriv t (v.toFun t) ∂timeMeasure T) =
      w.toFun T (v.toFun T) - w.toFun 0 (v.toFun 0) := by
  obtain ⟨z, _, hz, hzd⟩ := exists_timeH1_clm_apply w v
  have h := z.toFun_sub_toFun (t₀ := 0) (t₁ := T) ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩
  rw [hz T ⟨hT, le_rfl⟩, hz 0 ⟨le_rfl, hT⟩] at h
  rw [intervalIntegral.integral_of_le hT, setIntegral_congr_set Ioc_ae_eq_Icc] at h
  have hright : Integrable (fun t => w.deriv t (v.toFun t)) (timeMeasure T) := by
    have hv := memLp_of_continuousOn v.continuousOn_toFun
    exact MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable
      (fun _ => ContinuousLinearMap.id ℝ (X →L[ℝ] ℝ))
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      (Lp.memLp w.deriv) hv
  have hleft : Integrable (fun t => w.toFun t (v.deriv t)) (timeMeasure T) := by
    have hw := memLp_of_continuousOn w.continuousOn_toFun
    exact MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable
      (fun _ => ContinuousLinearMap.id ℝ (X →L[ℝ] ℝ))
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      hw (Lp.memLp v.deriv)
  have hzint : (∫ t in Icc (0 : ℝ) T, z.deriv t) =
      ∫ t, w.deriv t (v.toFun t) + w.toFun t (v.deriv t) ∂timeMeasure T := by
    exact integral_congr_ae hzd
  rw [hzint, integral_add hright hleft] at h
  exact (add_comm _ _).trans h.symm

theorem integral_timeH1_test_of_mass_dual
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a b : ℝ} (hab : a ≤ b) (mass : Y →L[ℝ] X →L[ℝ] ℝ)
    (v : ℝ → Y) (w : timeH1 (X →L[ℝ] ℝ) (b - a))
    (ℓ : ℝ → X →L[ℝ] ℝ)
    (hw : ∀ᵐ s ∂timeMeasure (b - a), ∀ z : X,
      w.toFun s z = mass (v (a + s)) z)
    (hd : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (ζ : timeH1 X (b - a)) (hζ0 : ζ.toFun 0 = 0) (hζ1 : ζ.toFun (b - a) = 0) :
    (∫ s, mass (v (a + s)) (ζ.deriv s) ∂timeMeasure (b - a)) +
      (∫ s, ℓ (a + s) (ζ.toFun s) ∂timeMeasure (b - a)) = 0 := by
  have h := timeH1.integral_dual_deriv_add_deriv_dual (sub_nonneg.mpr hab) w ζ
  rw [hζ0, hζ1, map_zero, map_zero, sub_self] at h
  refine Eq.trans ?_ h
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply integral_congr_ae
    filter_upwards [hw] with s hs
    exact (hs (ζ.deriv s)).symm
  · apply integral_congr_ae
    filter_upwards [hd] with s hs
    exact (congrArg (fun L : X →L[ℝ] ℝ => L (ζ.toFun s)) hs).symm

theorem integral_timeH1_test_of_weak_dual_deriv_on
    {a b : ℝ} (hab : a < b) {p q : ℝ → X →L[ℝ] ℝ}
    (hp : MemLp p 2 (volume.restrict (Icc a b)))
    (hq : MemLp q 2 (volume.restrict (Icc a b)))
    (hweak : ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ t in Ioo a b, deriv φ t * p t x) =
        -∫ t in Ioo a b, φ t * q t x)
    (v : timeH1 X (b - a)) (hv0 : v.toFun 0 = 0) (hvT : v.toFun (b - a) = 0) :
    (∫ t, p (a + t) (v.deriv t) ∂timeMeasure (b - a)) +
      (∫ t, q (a + t) (v.toFun t) ∂timeMeasure (b - a)) = 0 := by
  obtain ⟨w, hwp, hwq⟩ := exists_timeH1_dual_of_weak_deriv_on hab hp hq hweak
  have h := timeH1.integral_dual_deriv_add_deriv_dual (sub_nonneg.mpr hab.le) w v
  rw [hv0, hvT, map_zero, map_zero, sub_self] at h
  refine Eq.trans ?_ h
  apply congrArg₂ (fun a b : ℝ => a + b)
  · exact integral_congr_ae (hwp.mono fun t ht => congrArg (fun L : X →L[ℝ] ℝ => L (v.deriv t)) ht)
  · exact integral_congr_ae (hwq.mono fun t ht => congrArg (fun L : X →L[ℝ] ℝ => L (v.toFun t)) ht.symm)

theorem integral_timeH1_test_of_weak_dual_deriv
    {T : ℝ} (hT : 0 < T) {p q : ℝ → X →L[ℝ] ℝ}
    (hp : MemLp p 2 (timeMeasure T)) (hq : MemLp q 2 (timeMeasure T))
    (hweak : ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo (0 : ℝ) T →
      (∫ t in Ioo (0 : ℝ) T, deriv φ t * p t x) =
        -∫ t in Ioo (0 : ℝ) T, φ t * q t x)
    (v : timeH1 X T) (hv0 : v.toFun 0 = 0) (hvT : v.toFun T = 0) :
    (∫ t, p t (v.deriv t) ∂timeMeasure T) +
      (∫ t, q t (v.toFun t) ∂timeMeasure T) = 0 := by
  have h := integral_timeH1_test_of_weak_dual_deriv_on hT hp hq hweak
  rw [sub_zero] at h
  simpa only [zero_add] using h v hv0 hvT

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
