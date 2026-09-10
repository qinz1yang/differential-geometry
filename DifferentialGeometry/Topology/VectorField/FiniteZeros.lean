import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.DiscreteSubset

set_option autoImplicit false

open Bundle Filter Set Topology
open scoped Manifold

namespace Poincare.VectorBundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

include 𝕜

theorem isClosed_zeroSet {v : ∀ x, E x}
    (hv : Continuous (fun x ↦ TotalSpace.mk' F x (v x))) :
    IsClosed {x | v x = 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x hx
  let e := trivializationAt F E x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  have hc : ContinuousAt (fun y ↦ (e ⟨y, v y⟩).2) x :=
    (FiberBundle.continuousAt_section F x).mp hv.continuousAt
  have hn : (e ⟨x, v x⟩).2 ≠ 0 := by
    rw [e.apply_eq_prod_continuousLinearEquivAt 𝕜 x hxe]
    exact (e.continuousLinearEquivAt 𝕜 x hxe).map_ne_zero_iff.mpr hx
  filter_upwards [e.open_baseSet.mem_nhds hxe, hc.eventually_ne hn] with y hy hne
  change v y ≠ 0
  intro hzero
  apply hne
  rw [hzero, e.apply_eq_prod_continuousLinearEquivAt 𝕜 y hy]
  exact map_zero _

theorem finite_zeroSet [CompactSpace B] {v : ∀ x, E x}
    (hv : Continuous (fun x ↦ TotalSpace.mk' F x (v x)))
    (hzeros : IsDiscrete {x | v x = 0}) :
    {x | v x = 0}.Finite :=
  (isClosed_zeroSet 𝕜 hv).isCompact.finite hzeros

theorem finite_zeroSet_of_isolated [CompactSpace B] {v : ∀ x, E x}
    (hv : Continuous (fun x ↦ TotalSpace.mk' F x (v x)))
    (hzeros : ∀ x, v x = 0 → ∀ᶠ y in 𝓝 x, v y = 0 → y = x) :
    {x | v x = 0}.Finite := by
  apply finite_zeroSet 𝕜 hv
  apply IsDiscrete.of_nhdsWithin
  intro x hx
  rw [Filter.le_pure_iff]
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hzeros x hx),
    self_mem_nhdsWithin] with y hy hyv
  exact hy hyv

end Poincare.VectorBundle

namespace Poincare.VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem finite_zeroSet [CompactSpace M] {v : ∀ x : M, TangentSpace I x}
    (hv : Continuous (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hzeros : ∀ x, v x = 0 → ∀ᶠ y in 𝓝 x, v y = 0 → y = x) :
    {x | v x = 0}.Finite :=
  Poincare.VectorBundle.finite_zeroSet_of_isolated 𝕜 hv hzeros

end Poincare.VectorField
