import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem le_iSup_eigenspace_of_fixed
    (V : Submodule R M) (O : Module.End R M) (s : Set R) (hs : 1 ∈ s)
    (hfix : ∀ v ∈ V, O v = v) :
    V ≤ ⨆ a ∈ s, Module.End.eigenspace O a := by
  intro v hv
  have hv1 : v ∈ Module.End.eigenspace O 1 := by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact hfix v hv
  exact (le_iSup₂_of_le (1 : R) hs le_rfl : Module.End.eigenspace O 1 ≤ _) hv1

end Submodule
