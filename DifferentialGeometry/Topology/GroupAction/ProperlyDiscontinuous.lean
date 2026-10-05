import Mathlib.Topology.Algebra.ConstMulAction

set_option autoImplicit false

open Set

variable {Γ T : Type*} [TopologicalSpace T] [SMul Γ T]

@[to_additive]
theorem ProperlyDiscontinuousSMul.finite_of_isCompact_mapsTo
    [ProperlyDiscontinuousSMul Γ T] {K : Set T}
    (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (hK_mapsTo : ∀ γ : Γ, MapsTo (γ • ·) K K) :
    Finite Γ := by
  apply Finite.of_finite_univ
  refine (finite_disjoint_inter_image hK hK).subset ?_
  intro γ _
  obtain ⟨x, hx⟩ := hK_nonempty
  exact ⟨γ • x, ⟨x, hx, rfl⟩, hK_mapsTo γ hx⟩
