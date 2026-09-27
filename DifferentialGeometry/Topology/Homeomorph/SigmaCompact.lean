import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Compactness.SigmaCompact

section

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

theorem isSigmaCompact_of_isOpen_subset_target
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (e : OpenPartialHomeomorph X Y) {s : Set Y} (hs : IsOpen s) (hsub : s ⊆ e.target) :
    IsSigmaCompact s := by
  let U : Set X := e.source ∩ e ⁻¹' s
  have hU : IsOpen U := e.isOpen_inter_preimage hs
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hSigma : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have himage : e '' U = s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      refine ⟨e.symm y, ⟨e.map_target (hsub hy), ?_⟩, e.right_inv (hsub hy)⟩
      change e (e.symm y) ∈ s
      rwa [e.right_inv (hsub hy)]
  rw [← himage]
  exact hSigma.image_of_continuousOn (e.continuousOn.mono inter_subset_left)

end OpenPartialHomeomorph

end
