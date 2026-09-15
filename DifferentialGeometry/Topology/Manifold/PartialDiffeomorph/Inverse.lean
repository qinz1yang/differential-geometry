import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u v uE uF uH uH'

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H' : Type uH'} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type v} [TopologicalSpace N] [ChartedSpace H' N]
variable {n : WithTop ℕ∞}

namespace PartialDiffeomorph

theorem invFunOn_eqOn_symm
    [Nonempty M] (Ψ : PartialDiffeomorph I J M N n)
    {U : Set M} (hU : U ⊆ Ψ.source) :
    EqOn (Function.invFunOn (Ψ : M → N) U) (Ψ.symm : N → M) ((Ψ : M → N) '' U) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ((Ψ.toPartialEquiv.injOn.mono hU).leftInvOn_invFunOn hx).trans
    (Ψ.left_inv' (hU hx)).symm

theorem invFunOn_eventuallyEq_symm_on_image
    [Nonempty M] (Ψ : PartialDiffeomorph I J M N n)
    {U : Opens M} (hU : (U : Set M) ⊆ Ψ.source) :
    ∀ y ∈ (Ψ : M → N) '' (U : Set M),
      Function.invFunOn (Ψ : M → N) (U : Set M) =ᶠ[nhds y] (Ψ.symm : N → M) := by
  intro y hy
  refine Filter.eventuallyEq_of_mem ((image_opens_isOpen Ψ hU).mem_nhds hy) ?_
  intro z hz
  exact invFunOn_eqOn_symm Ψ hU hz

end PartialDiffeomorph
end DifferentialGeometry
