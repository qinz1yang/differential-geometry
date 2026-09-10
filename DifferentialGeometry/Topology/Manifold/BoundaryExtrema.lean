import DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open scoped ContDiff Manifold Topology
open Set
open DifferentialGeometry.Geometry.Operator

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private theorem differentiable_of_regular {f : M → ℝ} {x : M}
    (hreg : mfderiv I 𝓘(ℝ) f x ≠ 0) : MDifferentiableAt I 𝓘(ℝ) f x := by
  by_contra hf
  exact hreg (mfderiv_zero_of_not_mdifferentiableAt hf)

theorem isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero
    {f : M → ℝ} {x : M} (hmin : IsLocalMin f x)
    (hreg : mfderiv I 𝓘(ℝ) f x ≠ 0) : I.IsBoundaryPoint x := by
  apply (I.isBoundaryPoint_iff_not_isInteriorPoint x).mpr
  intro hx
  exact hreg (mfderiv_eq_zero_at_spatial_min_of_isInteriorPoint hmin hx
    (differentiable_of_regular hreg))

theorem isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero
    {f : M → ℝ} {x : M} (hmax : IsLocalMax f x)
    (hreg : mfderiv I 𝓘(ℝ) f x ≠ 0) : I.IsBoundaryPoint x := by
  apply isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero (f := -f) hmax.neg
  rw [mfderiv_neg]
  exact neg_ne_zero.mpr hreg

theorem range_subset_Icc_of_boundary_values [CompactSpace M]
    {f : M → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → f x = a ∨ f x = b) :
    range f ⊆ Icc a b := by
  have hf : Continuous f := (show MDifferentiable I 𝓘(ℝ) f from
    fun x ↦ differentiable_of_regular (hreg x)).continuous
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn ⟨x, mem_univ x⟩ hf.continuousOn
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn ⟨x, mem_univ x⟩ hf.continuousOn
  have hpB := isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero
    (hp.isLocalMin Filter.univ_mem) (hreg p)
  have hqB := isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero
    (hq.isLocalMax Filter.univ_mem) (hreg q)
  have hpv : a ≤ f p := by rcases hboundary p hpB with h | h <;> simp [h, hab]
  have hqv : f q ≤ b := by rcases hboundary q hqB with h | h <;> simp [h, hab]
  exact ⟨hpv.trans (hp (mem_univ x)), (hq (mem_univ x)).trans hqv⟩

theorem boundary_eq_preimage_endpoints_of_boundary_values [CompactSpace M]
    {f : M → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → f x = a ∨ f x = b) :
    I.boundary M = f ⁻¹' ({a} : Set ℝ) ∪ f ⁻¹' ({b} : Set ℝ) := by
  have hb := fun x ↦ range_subset_Icc_of_boundary_values hab hreg hboundary (mem_range_self x)
  ext x
  change I.IsBoundaryPoint x ↔ f x = a ∨ f x = b
  refine ⟨hboundary x, ?_⟩
  rintro (hx | hx)
  · apply isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero _ (hreg x)
    exact Filter.Eventually.of_forall (fun y ↦ by simpa only [hx] using (hb y).1)
  · apply isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero _ (hreg x)
    exact Filter.Eventually.of_forall (fun y ↦ by simpa only [hx] using (hb y).2)

theorem range_eq_Icc_of_boundary_values [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → f x = a ∨ f x = b)
    (ha : a ∈ range f) (hb : b ∈ range f) : range f = Icc a b := by
  have hf : Continuous f := (show MDifferentiable I 𝓘(ℝ) f from
    fun x ↦ differentiable_of_regular (hreg x)).continuous
  exact Subset.antisymm (range_subset_Icc_of_boundary_values hab hreg hboundary)
    ((isPreconnected_range hf).Icc_subset ha hb)

end Poincare.Topology.Manifold
