import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support

open Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : E → F} {s : Set E}

theorem ContDiffOn.contDiff_of_tsupport_subset (hf : ContDiffOn 𝕜 n f s)
    (hs : IsOpen s) (hfs : tsupport f ⊆ s) : ContDiff 𝕜 n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt (hs.mem_nhds (hfs hx))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hx)
