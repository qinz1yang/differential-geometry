import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Manifold

theorem IsImmersion.isImmersionOfComplement_of_finrank_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E V C : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [FiniteDimensional 𝕜 C]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N] {n : WithTop ℕ∞} {f : M → N}
    (h : IsImmersion I J n f)
    (hdim : Module.finrank 𝕜 C = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    IsImmersionOfComplement C I J n f := by
  intro x
  let hi := h.isImmersionOfComplement_complement x
  let : FiniteDimensional 𝕜 (E × h.complement) :=
    FiniteDimensional.of_injective hi.equiv.toLinearEquiv.toLinearMap hi.equiv.injective
  let : FiniteDimensional 𝕜 E :=
    FiniteDimensional.of_injective (LinearMap.inl 𝕜 E h.complement)
      LinearMap.inl_injective
  let : FiniteDimensional 𝕜 h.complement :=
    FiniteDimensional.of_injective (LinearMap.inr 𝕜 E h.complement)
      LinearMap.inr_injective
  have hsum : Module.finrank 𝕜 E + Module.finrank 𝕜 h.complement = Module.finrank 𝕜 V := by
    simpa only [Module.finrank_prod] using hi.equiv.toLinearEquiv.finrank_eq
  have hrank : Module.finrank 𝕜 h.complement = Module.finrank 𝕜 C := by omega
  exact hi.trans_F (ContinuousLinearEquiv.ofFinrankEq hrank)

end Manifold
