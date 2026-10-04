import DifferentialGeometry.Topology.Manifold.Cutoff.Finite

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

theorem two_domain_weight_preserving_compact_core
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    {n : ℕ∞} [IsManifold I n M] [T2Space M]
    {A W T P : Set M} (hA : IsOpen A) (hT : IsOpen T)
    (hW : IsCompact (closure W)) (hcover : closure W ⊆ A ∪ T)
    (hP : IsCompact P) (hPA : P ⊆ A) :
    ∃ χ : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) n χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      tsupport χ ⊆ A ∧ W ∩ tsupport (fun x ↦ 1 - χ x) ⊆ T ∧
      χ =ᶠ[𝓝ˢ P] 1 := by
  let C := (closure W \ T) ∪ P
  have hC : IsCompact C := (hW.diff hT).union hP
  have hCA : C ⊆ A := by
    intro x hx
    rcases hx with hx | hx
    · exact (hcover hx.1).resolve_right hx.2
    · exact hPA hx
  obtain ⟨χ, hχ, hcompact, hsupp, hrange, hone⟩ :=
    exists_contMDiff_cutoff (I := I) (n := n) hC hA hCA
  refine ⟨χ, hχ, hcompact, hrange, hsupp, ?_, ?_⟩
  · intro x hx
    by_contra hxT
    have hxC : x ∈ C := Or.inl ⟨subset_closure hx.1, hxT⟩
    have hχone := eventually_nhdsSet_iff_forall.mp hone x hxC
    have hz : (fun y ↦ 1 - χ y) =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hχone] with y hy
      rw [show χ y = 1 from hy, sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx.2
  · apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    exact eventually_nhdsSet_iff_forall.mp hone x (Or.inr hx)

end DifferentialGeometry.Topology.Manifold
