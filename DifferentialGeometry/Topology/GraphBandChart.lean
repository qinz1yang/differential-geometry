import DifferentialGeometry.Topology.GraphBand
import DifferentialGeometry.Topology.Embedding.OpensChartRegion

namespace DifferentialGeometry.Topology

open Set

theorem frontier_graphBand_of_opens_product_chart
    {N M : Type*} [TopologicalSpace N] [CompactSpace N]
    [TopologicalSpace M] [T2Space M]
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (e : O ≃ₜ V) (a b : N → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ p, a p < b p)
    (hband : {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} ⊆ O) :
    frontier ((fun p : O ↦ (e p : M)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' {x | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1})) =
      range (fun p ↦ (e ⟨(p, a p), hband ⟨le_rfl, (hab p).le⟩⟩ : M)) ∪
      range (fun p ↦ (e ⟨(p, b p), hband ⟨(hab p).le, le_rfl⟩⟩ : M)) := by
  rw [Embedding.frontier_opens_chart_image O V e (isCompact_graphBand a b ha hb hab) hband,
    frontier_graphBand a b ha hb hab]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨p, hp⟩ | ⟨p, hp⟩
    · left
      refine ⟨p, ?_⟩
      have heq : (⟨(p, a p), hband ⟨le_rfl, (hab p).le⟩⟩ : O) = x :=
        Subtype.ext hp
      exact congrArg (fun q : O ↦ (e q : M)) heq
    · right
      refine ⟨p, ?_⟩
      have heq : (⟨(p, b p), hband ⟨(hab p).le, le_rfl⟩⟩ : O) = x :=
        Subtype.ext hp
      exact congrArg (fun q : O ↦ (e q : M)) heq
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨⟨(p, a p), hband ⟨le_rfl, (hab p).le⟩⟩, Or.inl ⟨p, rfl⟩, rfl⟩
    · exact ⟨⟨(p, b p), hband ⟨(hab p).le, le_rfl⟩⟩, Or.inr ⟨p, rfl⟩, rfl⟩

end DifferentialGeometry.Topology

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Topology

theorem interior_eq_empty_of_frontier_graph_in_opens_product_chart
    {X M : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace M]
    (O : TopologicalSpace.Opens (X × ℝ)) (V : TopologicalSpace.Opens M)
    (e : O ≃ₜ V) {K : Set M} (hK : IsCompact K) (hKV : K ⊆ V)
    (f : X → ℝ)
    (hfront : ∀ p : V, p.val ∈ frontier K →
      (e.symm p).val ∈ range (fun x => (x, f x))) : interior K = ∅ := by
  let A : Set (X × ℝ) := (fun p : V => (e.symm p).val) '' ((Subtype.val : V → M) ⁻¹' K)
  have hpre : IsCompact ((Subtype.val : V → M) ⁻¹' K) :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hK
      (fun x hx => ⟨⟨x, hKV hx⟩, rfl⟩)
  have hA : IsCompact A := hpre.image (continuous_subtype_val.comp e.symm.continuous)
  have hAg : frontier A ⊆ range (fun x => (x, f x)) := by
    rw [show frontier A = (fun p : V => (e.symm p).val) ''
      ((Subtype.val : V → M) ⁻¹' frontier K) from
        Embedding.frontier_opens_chart_image V O e.symm hK hKV]
    rintro _ ⟨p, hp, rfl⟩
    exact hfront p hp
  have hAi := interior_eq_empty_of_frontier_subset_graph hA f hAg
  rw [show interior A = (fun p : V => (e.symm p).val) ''
      ((Subtype.val : V → M) ⁻¹' interior K) from
        Embedding.interior_opens_chart_image V O e.symm K] at hAi
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxV : x ∈ V := hKV (interior_subset hx)
  have hm : (e.symm ⟨x, hxV⟩).val ∈
      (fun p : V => (e.symm p).val) '' ((Subtype.val : V → M) ⁻¹' interior K) :=
    ⟨⟨x, hxV⟩, hx, rfl⟩
  rw [hAi] at hm
  exact hm

end DifferentialGeometry.Topology
