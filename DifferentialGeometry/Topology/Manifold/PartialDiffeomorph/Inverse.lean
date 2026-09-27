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


theorem invFunOn_eqOn_of_eqOn
    [Nonempty M] (Φ : PartialDiffeomorph I J M N n)
    {U : Set M} (hU : U ⊆ Φ.source) {F : M → N}
    (hEq : EqOn (Φ : M → N) F U) :
    EqOn (Function.invFunOn F U) (Φ.symm : N → M) (F '' U) := by
  have hF_inj : Set.InjOn F U := by
    intro x hx y hy hxy
    apply Φ.toPartialEquiv.injOn (hU hx) (hU hy)
    calc
      Φ x = F x := hEq hx
      _ = F y := hxy
      _ = Φ y := (hEq hy).symm
  rintro _ ⟨x, hx, rfl⟩
  calc
    Function.invFunOn F U (F x) = x := hF_inj.leftInvOn_invFunOn hx
    _ = Φ.symm (Φ x) := (Φ.left_inv' (hU hx)).symm
    _ = Φ.symm (F x) := congrArg Φ.symm (hEq hx)

end PartialDiffeomorph
end DifferentialGeometry
