import DifferentialGeometry.Analysis.Integration.Convolution.Laplacian
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Convolution Pointwise

namespace DifferentialGeometry.Analysis

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integral_laplacian_smul_eq_of_smooth_test
    {u g : V → F} (hu : LocallyIntegrable u volume) (hg : LocallyIntegrable g volume)
    (hw : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, Laplacian.laplacian φ y • u y) = ∫ y, φ y • g y)
    {φ : V → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ y, Laplacian.laplacian φ y • u y) = ∫ y, φ y • g y := by
  let β (n : ℕ) : ContDiffBump (0 : V) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  let φn := fun n => (β n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ
  have hφnc (n : ℕ) : ContDiff ℝ ∞ (φn n) :=
    (β n).hasCompactSupport_normed.contDiff_convolution_left _ (β n).contDiff_normed
      hφ.continuous.locallyIntegrable
  have hφncs (n : ℕ) : HasCompactSupport (φn n) :=
    (β n).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hc
  have hLc : Continuous (Laplacian.laplacian φ) :=
    continuous_iff_continuousAt.mpr fun _ => hφ.contDiffAt.continuousAt_laplacian
  have hLcs : HasCompactSupport (Laplacian.laplacian φ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset _)
  have hlap (n : ℕ) : Laplacian.laplacian (φn n) =
      (β n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] Laplacian.laplacian φ := by
    funext y
    exact MeasureTheory.laplacian_convolution_right _
      ((β n).contDiff_normed (n := (⊤ : ℕ∞))).continuous.locallyIntegrable hc hφ y
  have hr : Tendsto (fun n => (β n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφlim (y : V) : Tendsto (fun n => φn n y) atTop (𝓝 (φ y)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous hr hφ.continuous y
  have hLlim (y : V) : Tendsto (fun n => Laplacian.laplacian (φn n) y) atTop
      (𝓝 (Laplacian.laplacian φ y)) := by
    simpa only [hlap] using
      ContDiffBump.convolution_tendsto_right_of_continuous hr hLc y
  have hnorm {f : V → ℝ} {C : ℝ} (hf : Continuous f) (hC : ∀ y, ‖f y‖ ≤ C)
      (n : ℕ) (y : V) :
      ‖((β n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) y‖ ≤ C := by
    have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
    simpa only [dist_zero_right] using dist_convolution_le (x₀ := y) (z₀ := (0 : ℝ)) hC0
      (β n).support_normed_eq.subset (β n).nonneg_normed (β n).integral_normed
      hf.aestronglyMeasurable (fun z _ => by simpa only [dist_zero_right] using hC z)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hφ.continuous
  obtain ⟨L, hL⟩ := hLcs.exists_bound_of_continuous hLc
  let S : Set V := Metric.closedBall 0 1 + tsupport φ
  have hS : IsCompact S := (isCompact_closedBall (0 : V) 1).add hc
  have hSφ : Function.support φ ⊆ S := by
    intro x hx
    exact Set.mem_add.mpr ⟨0, by simp, x, subset_tsupport φ hx, zero_add x⟩
  have hSL : Function.support (Laplacian.laplacian φ) ⊆ S := by
    intro x hx
    exact Set.mem_add.mpr ⟨0, by simp, x, tsupport_laplacian_subset φ
      (subset_tsupport _ hx), zero_add x⟩
  have hSn {f : V → ℝ} (hf : Function.support f ⊆ tsupport φ) (n : ℕ) :
      Function.support ((β n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) ⊆ S := by
    apply (support_convolution_subset _).trans
    apply add_subset_add _ hf
    rw [(β n).support_normed_eq]
    apply Metric.ball_subset_closedBall.trans
    apply Metric.closedBall_subset_closedBall
    change 1 / ((n : ℝ) + 1) ≤ 1
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hSφn (n : ℕ) : Function.support (φn n) ⊆ S := hSn (subset_tsupport φ) n
  have hSLn (n : ℕ) : Function.support (Laplacian.laplacian (φn n)) ⊆ S := by
    rw [hlap n]
    exact hSn ((subset_tsupport _).trans (tsupport_laplacian_subset φ)) n
  have huint : Integrable u (volume.restrict S) := hu.integrableOn_isCompact hS
  have hgint : Integrable g (volume.restrict S) := hg.integrableOn_isCompact hS
  have hrestrict {a : V → ℝ} {b : V → F} (ha : Function.support a ⊆ S) :
      (∫ y in S, a y • b y) = ∫ y, a y • b y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [show a y = 0 from not_not.mp (fun h => hy (ha h)), zero_smul]
  have hleft : Tendsto (fun n => ∫ y in S, Laplacian.laplacian (φn n) y • u y) atTop
      (𝓝 (∫ y in S, Laplacian.laplacian φ y • u y)) := by
    apply tendsto_integral_of_dominated_convergence (fun y => L * ‖u y‖)
      (fun n => ?_) (huint.norm.const_mul L) (fun n => ?_)
      (Eventually.of_forall fun y => (hLlim y).smul tendsto_const_nhds)
    · have hcont : Continuous (Laplacian.laplacian (φn n)) :=
        continuous_iff_continuousAt.mpr fun y =>
          ((hφnc n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) :
            ContDiff ℝ 2 (φn n)).contDiffAt.continuousAt_laplacian
      exact (hcont.aestronglyMeasurable.restrict).smul huint.aestronglyMeasurable
    · filter_upwards with y
      rw [norm_smul, hlap n]
      exact mul_le_mul_of_nonneg_right (hnorm hLc hL n y) (norm_nonneg _)
  have hright : Tendsto (fun n => ∫ y in S, φn n y • g y) atTop
      (𝓝 (∫ y in S, φ y • g y)) := by
    apply tendsto_integral_of_dominated_convergence (fun y => M * ‖g y‖)
      (fun n => ((hφnc n).continuous.aestronglyMeasurable.restrict).smul hgint.aestronglyMeasurable)
      (hgint.norm.const_mul M) (fun n => ?_)
      (Eventually.of_forall fun y => (hφlim y).smul tendsto_const_nhds)
    filter_upwards with y
    change ‖φn n y • g y‖ ≤ M * ‖g y‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hnorm hφ.continuous hM n y) (norm_nonneg _)
  rw [← hrestrict hSL, ← hrestrict hSφ]
  exact tendsto_nhds_unique hleft (hright.congr fun n => by
    rw [hrestrict (hSφn n), hrestrict (hSLn n)]
    exact (hw (φn n) (hφnc n) (hφncs n)).symm)

end DifferentialGeometry.Analysis

end
