import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
Connected maps into a compact carrier land in a unique member of its actual finite component
cover. In particular every supplied boundary torus has a unique component owner.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

universe u v

namespace GC.Endpoint.CompactCarrier.Components

variable {C : CompactCarrier.{u}} (D : C.Components)

theorem exists_unique_owner {M : Type v} [TopologicalSpace M] [ConnectedSpace M]
    (f : M → C.Carrier) (hf : Continuous f) :
    ∃! i : Fin D.count, range f ⊆ D.piece i := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have hx : f x ∈ ⋃ i, (D.piece i : Set C.Carrier) := by
    rw [D.covers]
    exact mem_univ _
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have howner : range f ⊆ D.piece i :=
    (isPreconnected_range hf).subset_isClopen ⟨D.closed i, (D.piece i).isOpen⟩
      ⟨f x, ⟨x, rfl⟩, hi⟩
  refine ⟨i, howner, ?_⟩
  intro j hj
  by_contra hne
  exact (disjoint_left.mp (D.disjoint hne)) (hj ⟨x, rfl⟩) hi

theorem exists_owner {M : Type v} [TopologicalSpace M] [ConnectedSpace M]
    (f : M → C.Carrier) (hf : Continuous f) :
    ∃ i : Fin D.count, range f ⊆ D.piece i :=
  (D.exists_unique_owner f hf).exists

end GC.Endpoint.CompactCarrier.Components

namespace GC.GraphManifold.BoundaryTori

variable {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n)

theorem exists_unique_owner (D : C.Components) (j : Fin n) :
    ∃! i : Fin D.count, range (T.torusMap j) ⊆ D.piece i :=
  D.exists_unique_owner (T.torusMap j) (T.torusMap_smooth j).continuous

theorem exists_owner (D : C.Components) (j : Fin n) :
    ∃ i : Fin D.count, range (T.torusMap j) ⊆ D.piece i :=
  (T.exists_unique_owner D j).exists

end GC.GraphManifold.BoundaryTori
