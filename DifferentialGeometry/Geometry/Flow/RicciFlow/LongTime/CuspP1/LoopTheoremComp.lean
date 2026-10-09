import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTheoremCore
set_option autoImplicit false
open Set Topology
namespace GC.LongTime.CuspP1
open GC.Topology

theorem connectedComponentIn_range_family_LTP4 {E : Type*} [TopologicalSpace E] [T2Space E]
    {ι : Type} [Finite ι] [TopologicalSpace ι] [DiscreteTopology ι]
    (g : ι × Torus → E) (hg : Continuous g) (hinj : Function.Injective g) (j : ι) (z₀ : Torus) :
    connectedComponentIn (range g) (g (j, z₀)) = range (fun z : Torus => g (j, z)) := by
  have hcj : Continuous fun z : Torus => g (j, z) := hg.comp (continuous_const.prodMk continuous_id)
  have hT : IsConnected (range fun z : Torus => g (j, z)) := isConnected_range hcj
  have hAc : IsCompact {p : ι × Torus | p.1 = j} :=
    (isClosed_discrete {j}).preimage continuous_fst |>.isCompact
  have hBc : IsCompact {p : ι × Torus | p.1 ≠ j} :=
    (isClosed_discrete {j}ᶜ).preimage continuous_fst |>.isCompact
  have hTeq : range (fun z : Torus => g (j, z)) = g '' {p | p.1 = j} := by
    ext y; constructor
    · rintro ⟨z, rfl⟩; exact ⟨(j, z), rfl, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, by rw [← hp]⟩
  have hTcl : IsClosed (range fun z : Torus => g (j, z)) := by
    rw [hTeq]; exact (hAc.image hg).isClosed
  have hUcl : IsClosed (g '' {p | p.1 ≠ j}) := (hBc.image hg).isClosed
  have hdisj : Disjoint (range fun z : Torus => g (j, z)) (g '' {p | p.1 ≠ j}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨p, hp, hpe⟩
    exact hp (by simpa using (congrArg Prod.fst (hinj hpe)))
  have hrange : range g = (range fun z : Torus => g (j, z)) ∪ g '' {p | p.1 ≠ j} := by
    ext y; constructor
    · rintro ⟨⟨i, z⟩, rfl⟩
      by_cases hi : i = j
      · subst hi; exact Or.inl ⟨z, rfl⟩
      · exact Or.inr ⟨(i, z), hi, rfl⟩
    · rintro (⟨z, rfl⟩ | ⟨p, -, rfl⟩) <;> exact mem_range_self _
  have hxT : g (j, z₀) ∈ range fun z : Torus => g (j, z) := ⟨z₀, rfl⟩
  apply Subset.antisymm
  · set C := connectedComponentIn (range g) (g (j, z₀))
    have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCsub : C ⊆ range g := connectedComponentIn_subset _ _
    have hx : g (j, z₀) ∈ C := mem_connectedComponentIn (mem_range_self _)
    intro y hy
    by_contra hyT
    have hyU : y ∈ g '' {p | p.1 ≠ j} := by
      rcases hrange ▸ hCsub hy with h | h
      · exact absurd h hyT
      · exact h
    obtain ⟨w, hw⟩ := isPreconnected_closed_iff.mp hCpre _ _ hTcl hUcl
      (hCsub.trans hrange.subset) ⟨_, hx, hxT⟩ ⟨y, hy, hyU⟩
    exact Set.disjoint_left.mp hdisj hw.2.1 hw.2.2
  · exact hT.isPreconnected.subset_connectedComponentIn hxT (hrange ▸ subset_union_left)
end GC.LongTime.CuspP1
