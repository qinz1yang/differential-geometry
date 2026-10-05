import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.Defs

noncomputable section

open Metric Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def emptyTubeSystem (M : Type*) [TopologicalSpace M] : TubeSystem M where
  Index := PEmpty
  finiteIndex := ⟨∅, fun x => PEmpty.elim x⟩
  tube := fun a => PEmpty.elim a
  embedding := fun a => PEmpty.elim a
  disjoint := fun a => PEmpty.elim a

theorem emptyTubeSystem_core (M : Type*) [TopologicalSpace M] :
    (emptyTubeSystem M).core = univ := by
  apply Set.eq_univ_of_forall
  intro x
  simp only [TubeSystem.core, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  intro a
  exact PEmpty.elim a

def emptyTubeCapping (N : Type*) [TopologicalSpace N] :
    Capping (emptyTubeSystem N) N where
  coreInclusion := ⟨Subtype.val, continuous_subtype_val⟩
  coreEmbedding := Topology.IsEmbedding.subtypeVal
  cap := fun b => PEmpty.elim b.1
  capEmbedding := fun b => PEmpty.elim b.1
  attaching := fun b => PEmpty.elim b.1
  boundary_eq := fun b => PEmpty.elim b.1
  exhaustive := by
    have hcap : (⋃ b : (emptyTubeSystem N).Boundary,
        Set.range (PEmpty.elim b.1 : C(ThreeBall, N))) = ∅ := by
      apply Set.iUnion_eq_empty.mpr
      intro b
      exact PEmpty.elim b.1
    rw [hcap, Set.union_empty]
    apply Set.range_eq_univ.mpr
    intro x
    exact ⟨⟨x, by rw [emptyTubeSystem_core]; exact Set.mem_univ x⟩, rfl⟩
  core_cap_intersection := fun b => PEmpty.elim b.1
  cap_disjoint := fun b => PEmpty.elim b.1

def discardedComponentCutCap (Q D : Type*) [TopologicalSpace Q] [TopologicalSpace D]
    (d : D) : CutCapTopology (Q ⊕ D) Q D (Q ⊕ D) where
  tubes := emptyTubeSystem (Q ⊕ D)
  capping := emptyTubeCapping (Q ⊕ D)
  presentation := Homeomorph.refl _
  nontrivial := Or.inr ⟨d⟩

theorem discardedComponentCutCap_retained (Q D : Type*) [TopologicalSpace Q]
    [TopologicalSpace D] (d : D) (q : Q) :
    (discardedComponentCutCap Q D d).presentation (Sum.inl q) = Sum.inl q ∧
      (discardedComponentCutCap Q D d).presentation (Sum.inr d) = Sum.inr d :=
  ⟨rfl, rfl⟩

theorem nonempty_retainedCore_of_discardedComponentCutCap (Q D : Type*)
    [TopologicalSpace Q] [TopologicalSpace D] (d : D) (q : Q) :
    Nonempty ((discardedComponentCutCap Q D d).retainedCore) := by
  refine ⟨⟨⟨Sum.inl q, ?_⟩, q, ?_⟩⟩
  · change Sum.inl q ∈ (emptyTubeSystem (Q ⊕ D)).core
    rw [emptyTubeSystem_core]
    exact Set.mem_univ _
  · rfl

theorem not_isEmpty_index_and_isEmpty_discarded {M Q D N : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace D] [TopologicalSpace N]
    (E : CutCapTopology M Q D N) (h₁ : IsEmpty E.tubes.Index) (h₂ : IsEmpty D) : False := by
  rcases E.nontrivial with h | h
  · exact h₁.false h.some
  · exact h₂.false h.some

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
