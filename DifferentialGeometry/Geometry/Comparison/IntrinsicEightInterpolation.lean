import DifferentialGeometry.Geometry.Comparison.IntrinsicEightMidpoint
import DifferentialGeometry.Analysis.ODE.HyperbolicMidpoint

set_option autoImplicit false


open Set Metric Real Topology
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem hyperbolicInterpolate_le_of_intrinsic_8_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    [LocallyCompactSpace (ball o (8 * R))]
    (hlocal : ∀ z : ball o (8 * R), ∃ Ω : Set (ball o (8 * R)),
      @IsOpen (ball o (8 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o (8 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)) κ Ω ∧ z ∈ Ω)
    {A : ℝ} (hA : 0 < A) (σ : Icc (0 : ℝ) A → X) (hσ : Isometry σ)
    (hσmem : ∀ s, σ s ∈ closedBall o (3 * R / 2)) {z : X} (hz : z ∈ closedBall o R)
    (hzero : dist z (σ ⟨0, ⟨le_rfl, hA.le⟩⟩) ≤ 2 * R)
    (hend : dist z (σ ⟨A, ⟨hA.le, le_rfl⟩⟩) ≤ 2 * R) :
    ∀ t ∈ Icc (0 : ℝ) A,
      hyperbolicInterpolate (sqrt κ) A
        (cosh (sqrt κ * dist z (σ ⟨0, ⟨le_rfl, hA.le⟩⟩)))
        (cosh (sqrt κ * dist z (σ ⟨A, ⟨hA.le, le_rfl⟩⟩))) t ≤
        cosh (sqrt κ * dist z (IccExtend hA.le σ t)) := by
  let f : ℝ → ℝ := fun t => cosh (sqrt κ * dist z (IccExtend hA.le σ t))
  have hk : 0 < sqrt κ := sqrt_pos.mpr hκ
  have hσc : Continuous (IccExtend hA.le σ) := (continuous_IccExtend_iff (h := hA.le)).mpr hσ.continuous
  have hf : ContinuousOn f (Icc (0 : ℝ) A) := by
    exact (continuous_cosh.comp (continuous_const.mul (continuous_const.dist hσc))).continuousOn
  have hzero' : f 0 ≤ cosh (sqrt κ * (2 * R)) := by
    dsimp only [f]
    rw [IccExtend_left]
    apply cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg hk.le dist_nonneg), abs_of_pos (mul_pos hk (by positivity))]
    exact mul_le_mul_of_nonneg_left hzero hk.le
  have hend' : f A ≤ cosh (sqrt κ * (2 * R)) := by
    dsimp only [f]
    rw [IccExtend_right]
    apply cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg hk.le dist_nonneg), abs_of_pos (mul_pos hk (by positivity))]
    exact mul_le_mul_of_nonneg_left hend hk.le
  have hall := hyperbolicInterpolate_le_of_local_midpoint hk hA hf (by
    intro t ht hbad
    change 0 < t ∧ t < A at ht
    have hbound : hyperbolicInterpolate (sqrt κ) A (f 0) (f A) t ≤
        cosh (sqrt κ * (2 * R)) :=
      (hyperbolicInterpolate_le_max hk.le hA
        ((zero_le_one.trans (one_le_cosh _)).trans (le_max_left _ _)) ⟨ht.1.le, ht.2.le⟩).trans
        (max_le hzero' hend')
    have hdt : dist z (σ ⟨t, ⟨ht.1.le, ht.2.le⟩⟩) < 2 * R := by
      have hd := cosh_lt_cosh.mp (hbad.trans_le hbound)
      rw [IccExtend_of_mem hA.le σ ⟨ht.1.le, ht.2.le⟩,
        abs_of_nonneg (mul_nonneg hk.le dist_nonneg), abs_of_pos (mul_pos hk (by positivity))] at hd
      exact (mul_lt_mul_iff_right₀ hk).mp hd
    obtain ⟨h, hh, hl, hr, hmid⟩ := exists_cosh_midpoint_of_intrinsic_8_buffer
      hcurves o hκ hR hlocal hA.le σ hσ hσmem hz ht hdt
    exact ⟨h, hh, ⟨by linarith, by linarith [ht.2]⟩,
      ⟨by linarith [ht.1], hr⟩, hmid⟩)
  intro t ht
  simpa only [f, IccExtend_left, IccExtend_right] using hall t ht

end DifferentialGeometry.Geometry.Comparison.Toponogov
