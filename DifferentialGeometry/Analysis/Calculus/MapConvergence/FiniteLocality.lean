import DifferentialGeometry.Analysis.Calculus.MapConvergence.Locality

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem MapCPConvergenceOn.of_nhds
    {K : Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (hK : IsCompact K)
    (h : ∀ x ∈ K, ∃ V ∈ 𝓝 x, MapCPConvergenceOn (K ∩ V) p Φ Φinf) :
    MapCPConvergenceOn K p Φ Φinf := by
  apply hK.induction_on (p := fun L => MapCPConvergenceOn L p Φ Φinf)
  · intro ε hε
    exact ⟨0, fun _ _ _ _ _ hx => hx.elim⟩
  · intro s t hst ht
    exact ht.mono_set hst
  · intro s t hs ht
    exact hs.union ht
  · intro x hx
    obtain ⟨V, hV, hconv⟩ := h x hx
    exact ⟨K ∩ V, inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV), hconv⟩

end DifferentialGeometry.CheegerGromovCompactness
