import DifferentialGeometry.Analysis.Calculus.Smoothness.Closure
import DifferentialGeometry.Analysis.Schauder.Holder.Extension

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Analysis

theorem contDiffOn_succ_closure_of_holderOnWith_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : Convex ℝ s) (ho : IsOpen s) {f : E → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f s) (hfc : ContDiffOn ℝ n f (closure s))
    {K α : ℝ≥0} (hα : 0 < α) (hD : HolderOnWith K α (iteratedFDeriv ℝ (n + 1) f) s) :
    ContDiffOn ℝ (n + 1) f (closure s) ∧
      HolderOnWith K α (iteratedFDerivWithin ℝ (n + 1) f (closure s)) (closure s) := by
  have hUD : UniqueDiffOn ℝ (closure s) := by
    rcases eq_empty_or_nonempty s with rfl | hne
    · simp [UniqueDiffOn]
    · apply uniqueDiffOn_convex hs.closure
      apply hne.mono
      simpa only [ho.interior_eq] using
        (interior_mono subset_closure : interior s ⊆ interior (closure s))
  let p : E → FormalMultilinearSeries ℝ E F := fun x k =>
    extendFrom s (iteratedFDeriv ℝ k f) x
  have he (k : ℕ) (hk : k ≤ n + 1) : EqOn (fun x => p x k) (iteratedFDeriv ℝ k f) s := by
    apply extendFrom_extends
    have hc : ContinuousOn (iteratedFDerivWithin ℝ k f s) s :=
      hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) ho.uniqueDiffOn
    apply hc.congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen k ho hx).symm
  have htop : HolderOnWith K α (fun x => p x (n + 1)) (closure s) := (hD.extendFrom hα).1
  have hc (k : ℕ) (hk : k ≤ n + 1) : ContinuousOn (fun x => p x k) (closure s) := by
    by_cases hkn : k = n + 1
    · subst k
      exact htop.continuousOn hα
    have hle : k ≤ n := by omega
    have hcanon := hfc.continuousOn_iteratedFDerivWithin (m := k)
      (by exact_mod_cast hle) hUD
    apply hcanon.congr
    intro x hx
    apply extendFrom_eq hx
    apply ((hcanon x hx).mono subset_closure).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact iteratedFDerivWithin_eq_iteratedFDeriv hUD
      ((hf y hy).contDiffAt (ho.mem_nhds hy) |>.of_le (by exact_mod_cast hk)) (subset_closure hy)
  obtain ⟨hnew, heq⟩ := contDiffOn_closure_of_continuousOn_jets (n := (n + 1 : ℕ)) hs ho
    hf hfc.continuousOn (fun k hk => hc k (by exact_mod_cast hk))
    (fun k hk => he k (by exact_mod_cast hk))
  refine ⟨hnew, ?_⟩
  intro x hx y hy
  rw [← heq (n + 1) le_rfl hx, ← heq (n + 1) le_rfl hy]
  exact htop x hx y hy

end DifferentialGeometry.Analysis
