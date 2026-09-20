import Mathlib.Analysis.Calculus.ContDiff.RCLike

theorem ContDiffOn.locallyLipschitzOn_of_isOpen
    {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
    (hf : ContDiffOn 𝕜 1 f s) (hs : IsOpen s) : LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t, ht, hK⟩ := ((hf x hx).contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

