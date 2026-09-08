import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakFTC
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_timeH1_dual_of_weak_deriv
    {T : ℝ} (hT : 0 < T) {p q : ℝ → X →L[ℝ] ℝ}
    (hp : MemLp p 2 (timeMeasure T)) (hq : MemLp q 2 (timeMeasure T))
    (hweak : ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo (0 : ℝ) T →
      (∫ t in Ioo (0 : ℝ) T, deriv φ t * p t x) =
        -∫ t in Ioo (0 : ℝ) T, φ t * q t x) :
    ∃ w : timeH1 (X →L[ℝ] ℝ) T, p =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] q := by
  apply exists_timeH1_of_weak_deriv hT hp hq
  intro φ hφ hφc hφs
  have hpI : Integrable p (volume.restrict (Ioo (0 : ℝ) T)) :=
    (hp.integrable (by norm_num)).mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hqI : Integrable q (volume.restrict (Ioo (0 : ℝ) T)) :=
    (hq.integrable (by norm_num)).mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hdφp : Integrable (fun t => deriv φ t • p t) (volume.restrict (Ioo (0 : ℝ) T)) :=
    hpI.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hφ.continuous_deriv (by norm_cast)) hφc.deriv
  have hφq : Integrable (fun t => φ t • q t) (volume.restrict (Ioo (0 : ℝ) T)) :=
    hqI.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  ext x
  rw [ContinuousLinearMap.integral_apply hdφp, neg_apply,
    ContinuousLinearMap.integral_apply hφq]
  exact hweak x φ hφ hφc hφs

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
  obtain ⟨w, hwp, hwq⟩ := exists_timeH1_dual_of_weak_deriv hT hp hq hweak
  have h := timeH1.integral_dual_deriv_add_deriv_dual hT.le w v
  rw [hv0, hvT, map_zero, map_zero, sub_self] at h
  refine Eq.trans ?_ h
  apply congrArg₂ (fun a b : ℝ => a + b)
  · exact integral_congr_ae (hwp.mono fun t ht => congrArg (fun L : X →L[ℝ] ℝ => L (v.deriv t)) ht)
  · exact integral_congr_ae (hwq.mono fun t ht => congrArg (fun L : X →L[ℝ] ℝ => L (v.toFun t)) ht.symm)

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
