import DifferentialGeometry.Analysis.Elliptic.Euclidean.GradientEstimate
import DifferentialGeometry.Analysis.Integration.Convolution.Laplacian
import DifferentialGeometry.Analysis.Schauder.Holder.DerivativeLimit
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Convolution NNReal
namespace DifferentialGeometry.Analysis
open Parabolic.Euclidean Schauder

theorem exists_holder_fderiv_of_bounded_weak_laplacian
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u g : V → F} (hu : Continuous u) (hcu : HasCompactSupport u)
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (hw : ∀ φ : V → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, Laplacian.laplacian φ y • u y) = ∫ y, φ y • g y)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ContDiff ℝ 1 u ∧ HolderWith C α (fderiv ℝ u) := by
  have hB0 : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  obtain ⟨M, hM⟩ := hcu.exists_bound_of_continuous hu
  have hM0 : 0 ≤ M := (norm_nonneg (u 0)).trans (hM 0)
  let φ (n : ℕ) : ContDiffBump (0 : V) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  let v (n : ℕ) : V → F := (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u
  have hvc (n : ℕ) : ContDiff ℝ ∞ (v n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hu.locallyIntegrable
  have hv2 (n : ℕ) : ContDiff ℝ 2 (v n) := (hvc n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hcs (n : ℕ) : HasCompactSupport (v n) :=
    (φ n).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcu
  have hconvnorm {f : V → F} {A : ℝ} (hf : AEStronglyMeasurable f volume)
      (hA : ∀ x, ‖f x‖ ≤ A) (n : ℕ) (x : V) :
      ‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ≤ A := by
    have hA0 : 0 ≤ A := (norm_nonneg (f 0)).trans (hA 0)
    simpa only [dist_zero_right] using
      dist_convolution_le (x₀ := x) (z₀ := 0) hA0 (φ n).support_normed_eq.subset (φ n).nonneg_normed
        (φ n).integral_normed hf (fun y _ => by simpa only [dist_zero_right] using hA y)
  have hvM (n : ℕ) (x : V) : ‖v n x‖ ≤ M := hconvnorm hu.aestronglyMeasurable hM n x
  have hvB (n : ℕ) (x : V) : ‖Laplacian.laplacian (v n) x‖ ≤ B := by
    change ‖Laplacian.laplacian ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u) x‖ ≤ B
    rw [laplacian_convolution_of_weak_laplacian hu.locallyIntegrable hw
      (φ n).contDiff_normed (φ n).hasCompactSupport_normed]
    exact hconvnorm hg hB n x
  have hC0 : 0 ≤ (heatC2 V + 2 * heatC1 V) * (M + 2 * B / (1 - (α : ℝ))) := by
    have h1 := heatC1_nonneg (V := V)
    have h2 := heatC2_nonneg (V := V)
    have ha : (α : ℝ) < 1 := hα1
    positivity
  let C : ℝ≥0 := ⟨(heatC2 V + 2 * heatC1 V) * (M + 2 * B / (1 - (α : ℝ))), hC0⟩
  have hvhold (n : ℕ) : HolderWith C α (fderiv ℝ (v n)) := by
    intro x y
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow]
    change dist (fderiv ℝ (v n) x) (fderiv ℝ (v n) y) ≤
      (heatC2 V + 2 * heatC1 V) * (M + 2 * B / (1 - (α : ℝ))) * dist x y ^ (α : ℝ)
    have hh := norm_fderiv_sub_le_of_laplacian_bound (hv2 n) (hcs n) hα1
      (t := 1) zero_lt_one (hvM n) (hvB n) x y
    simpa only [Real.one_rpow, mul_one, dist_eq_norm] using hh
  have hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hun : TendstoUniformly v u atTop := by
    have huc := hcu.uniformContinuous_of_continuous hu
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
    filter_upwards [hr.eventually (gt_mem_nhds hδ)] with n hn
    intro x
    have hh : dist (v n x) (u x) ≤ ε / 2 := by
      apply (φ n).dist_normed_convolution_le hu.aestronglyMeasurable
      intro y hy
      exact (hδu (lt_trans hy hn)).le
    rw [dist_comm]
    exact hh.trans_lt (half_lt_self hε)
  have hd := differentiable_of_tendstoUniformly_of_holder_fderiv hα
    (fun n => (hv2 n).differentiable (by norm_num)) hvhold hun
  have hh := holder_fderiv_of_tendstoUniformly hα
    (fun n => (hv2 n).differentiable (by norm_num)) hvhold hun
  refine ⟨C, ?_, hh⟩
  exact contDiff_one_iff_fderiv.mpr ⟨hd, hh.continuous hα⟩

end DifferentialGeometry.Analysis
