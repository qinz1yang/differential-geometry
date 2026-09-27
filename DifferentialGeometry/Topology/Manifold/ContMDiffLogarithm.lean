import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : WithTop ℕ∞} {s : Set M} {f : M → ℝ}

theorem ContMDiffOn.log (hf : ContMDiffOn I 𝓘(ℝ, ℝ) k f s)
    (hzero : ∀ x ∈ s, f x ≠ 0) :
    ContMDiffOn I 𝓘(ℝ, ℝ) k (fun x => Real.log (f x)) s := by
  intro x hx
  exact (Real.contDiffAt_log.2 (hzero x hx)).comp_contMDiffWithinAt (hf x hx)
