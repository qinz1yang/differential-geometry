import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

theorem HasFTaylorSeriesUpToOn.closure_of_continuousOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {f : E → F} {p : E → FormalMultilinearSeries ℝ E F} {s : Set E}
    (hp : HasFTaylorSeriesUpToOn n f p s) (hs : Convex ℝ s) (ho : IsOpen s)
    (hf : ContinuousOn f (closure s))
    (hc : ∀ k : ℕ, k ≤ n → ContinuousOn (fun x => p x k) (closure s)) :
    HasFTaylorSeriesUpToOn n f p (closure s) := by
  refine ⟨?_, ?_, hc⟩
  · exact (show EqOn (fun x => (p x 0).curry0) f s from hp.zero_eq).of_subset_closure
      ((continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn
        (hc 0 (by simp))) hf subset_closure Subset.rfl
  · intro k hk x hx
    have hk1 : ((k + 1 : ℕ) : ℕ∞ω) ≤ n := ENat.add_one_natCast_le_withTop_of_lt hk
    have hd (y : E) (hy : y ∈ s) :
        HasFDerivAt (fun z => p z k) (p y (k + 1)).curryLeft y :=
      (hp.fderivWithin k hk y hy).hasFDerivAt (ho.mem_nhds hy)
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt) hs ho
      (fun y hy => (hc k hk.le y hy).mono subset_closure)
    have ht : Tendsto (fun y => (p y (k + 1)).curryLeft) (𝓝[s] x)
        (𝓝 ((p x (k + 1)).curryLeft)) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).continuous.tendsto _ |>.comp
        ((hc (k + 1) hk1 x hx).mono subset_closure)
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).fderiv.symm

namespace DifferentialGeometry.Analysis

theorem contDiffOn_closure_of_continuousOn_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {f : E → F} {p : E → FormalMultilinearSeries ℝ E F} {s : Set E}
    (hs : Convex ℝ s) (ho : IsOpen s) (hf : ContDiffOn ℝ n f s)
    (hfc : ContinuousOn f (closure s))
    (hc : ∀ k : ℕ, k ≤ n → ContinuousOn (fun x => p x k) (closure s))
    (he : ∀ k : ℕ, k ≤ n → EqOn (fun x => p x k) (iteratedFDeriv ℝ k f) s) :
    ContDiffOn ℝ n f (closure s) ∧
      ∀ k : ℕ, k ≤ n → EqOn (fun x => p x k) (iteratedFDerivWithin ℝ k f (closure s)) (closure s) := by
  have hp : HasFTaylorSeriesUpToOn n f p s := by
    apply (hf.ftaylorSeriesWithin ho.uniqueDiffOn).congr_series
    intro k hk x hx
    rw [he k (by exact_mod_cast hk) hx]
    exact iteratedFDerivWithin_of_isOpen k ho hx
  have hpc := hp.closure_of_continuousOn hs ho hfc (fun k hk => hc k (by exact_mod_cast hk))
  refine ⟨hpc.contDiffOn, ?_⟩
  have hUD : UniqueDiffOn ℝ (closure s) := by
    rcases eq_empty_or_nonempty s with rfl | hne
    · simp [UniqueDiffOn]
    · apply uniqueDiffOn_convex hs.closure
      apply hne.mono
      simpa only [ho.interior_eq] using
        (interior_mono subset_closure : interior s ⊆ interior (closure s))
  intro k hk x hx
  exact hpc.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hk) hUD hx

end DifferentialGeometry.Analysis
