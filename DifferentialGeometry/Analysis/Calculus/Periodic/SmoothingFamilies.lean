import DifferentialGeometry.Analysis.Calculus.Periodic.Smoothing
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Support









noncomputable section

open MeasureTheory Filter Function ContinuousLinearMap Set
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis

variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]



theorem continuous_convolution_family {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) {f : K × ℝ → F} (hf : Continuous f) :
    Continuous (fun p : K × ℝ => (k ⋆[lsmul ℝ ℝ, volume] (fun t => f (p.1, t))) p.2) := by
  let G : (K × ℝ) → ℝ → F := fun p t => k t • f (p.1, p.2 - t)
  have hG : Continuous G.uncurry := by
    apply Continuous.smul (hk.comp continuous_snd)
    exact hf.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).sub continuous_snd))
  have hzero : ∀ p t, p ∈ (univ : Set (K × ℝ)) → t ∉ tsupport k → G p t = 0 := by
    intro p t _ ht
    have hkt : k t = 0 := by
      by_contra hn
      exact ht (subset_closure hn)
    simp only [G, hkt, zero_smul]
  have hi := continuousOn_integral_of_compact_support hks hG.continuousOn hzero (μ := volume)
  simpa only [continuousOn_univ, G, convolution_def, lsmul_apply] using hi

theorem hasCompactSupport_iteratedDeriv {k : ℝ → ℝ} (hk : HasCompactSupport k) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n k) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hk
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv


theorem iteratedDeriv_convolution_left {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hks : HasCompactSupport k) {f : ℝ → F} (hf : Continuous f) (n : ℕ) :
    iteratedDeriv n (k ⋆[lsmul ℝ ℝ, volume] f) =
      (iteratedDeriv n k ⋆[lsmul ℝ ℝ, volume] f) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    have hkn : ContDiff ℝ ∞ (iteratedDeriv n k) := by
      rw [iteratedDeriv_eq_iterate]
      exact hk.iterate_deriv n
    exact ((hasCompactSupport_iteratedDeriv hks n).hasDerivAt_convolution_left
      (lsmul ℝ ℝ) (hkn.of_le (by simp)) hf.locallyIntegrable x).deriv


theorem continuous_iteratedDeriv_smoothPeriodic (φ : ContDiffBump (0 : ℝ))
    {f : K × ℝ → F} (hf : Continuous f) (n : ℕ) :
    Continuous (fun p : K × ℝ => iteratedDeriv n
      (smoothPeriodic φ (fun t => f (p.1, t))) p.2) := by
  have heq (p : K × ℝ) : iteratedDeriv n (smoothPeriodic φ (fun t => f (p.1, t))) =
      (iteratedDeriv n (φ.normed volume) ⋆[lsmul ℝ ℝ, volume] (fun t => f (p.1, t))) :=
    iteratedDeriv_convolution_left φ.contDiff_normed φ.hasCompactSupport_normed
      (hf.comp (continuous_const.prodMk continuous_id)) n
  simp_rw [heq]
  apply continuous_convolution_family _ (hasCompactSupport_iteratedDeriv φ.hasCompactSupport_normed n) hf
  have hk : ContDiff ℝ ∞ (iteratedDeriv n (φ.normed volume)) := by
    rw [iteratedDeriv_eq_iterate]
    exact φ.contDiff_normed.iterate_deriv n
  exact hk.continuous

end DifferentialGeometry.Analysis
