import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support


namespace LocallyLipschitzOn

open Filter Set
open scoped Topology

theorem locallyLipschitz_of_tsupport_subset
    {X F : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace F] [Zero F]
    {Ω : Set X} (hΩ : IsOpen Ω) {u : X → F}
    (hu : LocallyLipschitzOn Ω u) (hsupport : tsupport u ⊆ Ω) : LocallyLipschitz u := by
  intro x
  by_cases hx : x ∈ Ω
  · obtain ⟨C, V, hV, hC⟩ := hu hx
    exact ⟨C, V, by simpa only [hΩ.nhdsWithin_eq hx] using hV, hC⟩
  · refine ⟨0, (tsupport u)ᶜ,
      (isClosed_tsupport u).isOpen_compl.mem_nhds (fun h => hx (hsupport h)), ?_⟩
    intro y hy z hz
    rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hz,
      edist_self]
    exact bot_le

end LocallyLipschitzOn
