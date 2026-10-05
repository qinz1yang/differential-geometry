import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleUnionSet

/-!
# Consumers of the rounded union as a set (FC42 packet H3a, parts 1–2)

* `vertex_image_union_handles_subset_roundedComplement`: all vertices and all handles lie in the
  closed complement of the open rounded circle region (the ball–handle side of the common rounding);
* `CyclePartition.unionSet_spec`: the rounded union of a cycle is a compact connected subset of
  `W.interior ∩ roundedComplement`, equal to the `ψ_std ≤ 0` side in each of its rim charts.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- Every vertex and every handle lies on the closed side `ρ ≥ 0` of the common rounding. -/
theorem vertex_image_union_handles_subset_roundedComplement :
    (⋃ k, (D.vertex k).image) ∪ (⋃ h, range (D.handle h).map) ⊆ D.roundedComplement := by
  rintro x (hx | hx)
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_cases hxd : x ∈ D.circ.domain
    · exact Or.inr (D.nonneg_roundedFunction_of_mem_vertex_image k hk hxd)
    · exact Or.inl hxd
  · obtain ⟨h, hh⟩ := mem_iUnion.mp hx
    by_cases hxd : x ∈ D.circ.domain
    · exact Or.inr (D.nonneg_roundedFunction_of_mem_handle h hh hxd)
    · exact Or.inl hxd

namespace CyclePartition

variable {D} (P : D.CyclePartition)

/-- **The rounded union of a cycle, as a set.** -/
theorem unionSet_spec (j : Fin P.cnt) :
    IsCompact (P.unionSet j) ∧ IsConnected (P.unionSet j) ∧
      P.unionSet j ⊆ (W.interior : Set W.Carrier) ∩ D.roundedComplement ∧
      ∀ k b {p}, p ∈ (P.cycleRimChart j k b).source →
        (P.cycleRimChart j k b p ∈ P.unionSet j ↔ standardRimRounding p.2 ≤ 0) :=
  ⟨(P.isClosed_unionSet j).isCompact, P.isConnected_unionSet j,
    subset_inter (P.unionSet_subset_interior j) (P.unionSet_subset_roundedComplement j),
    fun k b _ hp => P.mem_unionSet_rim_iff j k b hp⟩

end CyclePartition

end DecompositionCertificate

end GC.GraphManifold.Assembly
