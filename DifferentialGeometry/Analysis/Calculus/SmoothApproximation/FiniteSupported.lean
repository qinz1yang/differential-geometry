import DifferentialGeometry.Analysis.Integration.Convolution.IteratedDerivative
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric ContinuousLinearMap Set
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis

theorem exists_smooth_approx_supported_in_open_of_contDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (k : ℕ) (hf : ContDiff ℝ (k : ℕ∞ω) f)
    (hfc : HasCompactSupport f) {U : Set E} (hU : IsOpen U)
    (hfs : tsupport f ⊆ U) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧ tsupport f ⊆ K ∧
      ∃ g : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (g n)) ∧
        (∀ n, tsupport (g n) ⊆ K) ∧
        ∀ j, j ≤ k → TendstoUniformly
          (fun n => iteratedFDeriv ℝ j (g n)) (iteratedFDeriv ℝ j f) atTop := by
  borelize E
  let μ : Measure E := Measure.addHaar
  obtain ⟨δ, hδ, hδU⟩ := hfc.isCompact.exists_cthickening_subset_open hU hfs
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(δ / ((n : ℝ) + 1)) / 2, δ / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    simpa only [φ, mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  have hrad (n : ℕ) : (φ n).rOut ≤ δ := by
    dsimp only [φ]
    exact div_le_self hδ.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  refine ⟨cthickening δ (tsupport f), hfc.isCompact.cthickening, hδU,
    self_subset_cthickening (tsupport f),
    fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_, ?_, ?_⟩
  · intro n
    exact (φ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ n).contDiff_normed hf.continuous.locallyIntegrable
  · intro n
    apply closure_minimal _ isClosed_cthickening
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := support_convolution_subset_swap (lsmul ℝ ℝ) hx
    apply mem_cthickening_of_dist_le (y + z) y δ (tsupport f) (subset_tsupport f hy)
    have hz' : dist z 0 < (φ n).rOut := by
      simpa only [(φ n).support_normed_eq (μ := μ), mem_ball] using hz
    simpa only [dist_eq_norm, add_sub_cancel_left, sub_zero] using hz'.le.trans (hrad n)
  · exact ContDiffBump.tendstoUniformly_iteratedFDeriv_normed_convolution hφ hfc k hf

end DifferentialGeometry.Analysis
