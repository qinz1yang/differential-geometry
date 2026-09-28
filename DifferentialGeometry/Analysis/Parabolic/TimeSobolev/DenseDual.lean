import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.WeakDerivative.FundamentalTheorem

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X S : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup S] [NormedSpace ℝ S]

theorem extend_scalar_weak_deriv_of_denseRange_on
    {a b : ℝ} (ι : S →L[ℝ] X) (hdense : DenseRange ι)
    {p q : ℝ → X →L[ℝ] ℝ}
    (hp : MemLp p 2 (volume.restrict (Icc a b)))
    (hq : MemLp q 2 (volume.restrict (Icc a b)))
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ t in Ioo a b, deriv φ t * p t (ι x)) =
        -∫ t in Ioo a b, φ t * q t (ι x)) :
    ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ t in Ioo a b, deriv φ t * p t x) =
        -∫ t in Ioo a b, φ t * q t x := by
  intro x φ hφ hφc hφs
  let μ := volume.restrict (Ioo a b)
  have hpI : Integrable p μ := (hp.integrable (by norm_num)).mono_measure
    (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hqI : Integrable q μ := (hq.integrable (by norm_num)).mono_measure
    (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hdp : Integrable (fun t => deriv φ t • p t) μ :=
    hpI.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hφ.continuous_deriv (by norm_cast)) hφc.deriv
  have hqφ : Integrable (fun t => φ t • q t) μ :=
    hqI.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  let A : X →L[ℝ] ℝ := ∫ t, deriv φ t • p t ∂μ
  let B : X →L[ℝ] ℝ := ∫ t, φ t • q t ∂μ
  have hABfun : (A : X → ℝ) = (-B : X → ℝ) := by
    apply DenseRange.equalizer hdense A.continuous (-B).continuous
    funext s
    dsimp [A, B]
    rw [ContinuousLinearMap.integral_apply hdp]
    change (∫ x, (deriv φ x • p x) (ι s) ∂μ) = -((∫ t, φ t • q t ∂μ) (ι s))
    rw [ContinuousLinearMap.integral_apply hqφ]
    exact hweak s φ hφ hφc hφs
  have hAB : A = -B := ContinuousLinearMap.ext (fun s => congrFun hABfun s)
  have hx := congrArg (fun L : X →L[ℝ] ℝ => L x) hAB
  dsimp [A, B] at hx
  rw [ContinuousLinearMap.integral_apply hdp] at hx
  change (∫ t, (deriv φ t • p t) x ∂μ) = -((∫ t, φ t • q t ∂μ) x) at hx
  rw [ContinuousLinearMap.integral_apply hqφ] at hx
  exact hx

theorem extend_scalar_weak_deriv_of_denseRange
    {T : ℝ} (ι : S →L[ℝ] X) (hdense : DenseRange ι)
    {p q : ℝ → X →L[ℝ] ℝ} (hp : MemLp p 2 (timeMeasure T))
    (hq : MemLp q 2 (timeMeasure T))
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo (0 : ℝ) T →
      (∫ t in Ioo (0 : ℝ) T, deriv φ t * p t (ι x)) =
        -∫ t in Ioo (0 : ℝ) T, φ t * q t (ι x)) :
    ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo (0 : ℝ) T →
      (∫ t in Ioo (0 : ℝ) T, deriv φ t * p t x) =
        -∫ t in Ioo (0 : ℝ) T, φ t * q t x := by
  exact extend_scalar_weak_deriv_of_denseRange_on ι hdense hp hq hweak

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
