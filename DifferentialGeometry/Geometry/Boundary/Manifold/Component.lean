import DifferentialGeometry.Geometry.Boundary.Manifold.Basic

open Set Function Topology
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

abbrev BoundaryComponent (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  ConnectedComponents (BoundaryManifold I M)

namespace BoundaryComponent

def carrier (C : BoundaryComponent I M) : Set M :=
  Subtype.val '' {x : BoundaryManifold I M | ConnectedComponents.mk x = C}

theorem mem_carrier {C : BoundaryComponent I M} {x : M} :
    x ∈ carrier C ↔
      ∃ y : BoundaryManifold I M, ConnectedComponents.mk y = C ∧ (y : M) = x :=
  Iff.rfl

theorem carrier_mk (x : BoundaryManifold I M) :
    carrier (ConnectedComponents.mk x) = Subtype.val '' connectedComponent x := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, ConnectedComponents.coe_eq_coe'.mp hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, ConnectedComponents.coe_eq_coe'.mpr hz, rfl⟩

theorem mk_mem_carrier (x : BoundaryManifold I M) :
    (x : M) ∈ carrier (ConnectedComponents.mk x) :=
  ⟨x, rfl, rfl⟩

theorem carrier_nonempty (C : BoundaryComponent I M) : (carrier C).Nonempty := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  exact ⟨(x : M), mk_mem_carrier x⟩

theorem carrier_subset_boundary (C : BoundaryComponent I M) : carrier C ⊆ I.boundary M := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem eq_of_mem_carrier {C D : BoundaryComponent I M} {x : M} (hx : x ∈ carrier C)
    (hy : x ∈ carrier D) : C = D := by
  obtain ⟨y, hyC, hyx⟩ := hx
  obtain ⟨z, hzD, hzx⟩ := hy
  have hyz : y = z := Subtype.ext (by rw [hyx, hzx])
  rw [← hyC, ← hzD, hyz]

theorem disjoint_carrier {C D : BoundaryComponent I M} (h : C ≠ D) :
    Disjoint (carrier C) (carrier D) := by
  rw [Set.disjoint_left]
  exact fun _ hx hy => h (eq_of_mem_carrier hx hy)

theorem carrier_injective {C D : BoundaryComponent I M} (h : carrier C = carrier D) : C = D := by
  obtain ⟨x, hx⟩ := carrier_nonempty C
  exact eq_of_mem_carrier hx (h ▸ hx)

theorem isClosed_carrier [IsManifold I 1 M] (C : BoundaryComponent I M) :
    IsClosed (carrier C) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [carrier_mk]
  exact (isClosedEmbedding_boundaryInclusion (I := I) (M := M)).isClosedMap _
    isClosed_connectedComponent

theorem isCompact_carrier [IsManifold I 1 M] [CompactSpace M] (C : BoundaryComponent I M) :
    IsCompact (carrier C) :=
  (isClosed_carrier C).isCompact

theorem isPreconnected_carrier (C : BoundaryComponent I M) : IsPreconnected (carrier C) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [carrier_mk]
  exact isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn

theorem iUnion_carrier : ⋃ C : BoundaryComponent I M, carrier C = I.boundary M := by
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC⟩ := mem_iUnion.mp hx
    exact carrier_subset_boundary C hC
  · intro hx
    exact mem_iUnion.mpr
      ⟨ConnectedComponents.mk ⟨x, hx⟩, mk_mem_carrier (I := I) ⟨x, hx⟩⟩

end BoundaryComponent

end DifferentialGeometry.Geometry.Boundary
