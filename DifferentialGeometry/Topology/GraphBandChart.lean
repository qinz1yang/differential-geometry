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
