import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleUnionCycle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleSeamSidesApplications

/-!
# Consumers of packet H3 (the cycles of FC42 step 6)

* `CyclePartition.toBallHandleCycle_spec`: the L1 inputs of one cycle (union = rounded union,
  balls in `W.interior`, rim product under the certificate clause);
* `exists_ballHandleCycles_of_badVertexCount_eq_zero`: without sphere seams and bad vertices, the
  certificate yields finitely many `BallHandleCycle`s whose unions are pairwise disjoint, contain
  every ball vertex and every handle, and are pieces whose boundary is the zero level of the common
  defining function `ρ` (the input shape of packet T4a).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsUA_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothUA_ASMCYC3 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskChartsUA_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothUA_ASMCYC3 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

namespace DecompositionCertificate

namespace CyclePartition

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {D : DecompositionCertificate W E}
  (P : D.CyclePartition)

/-- **The L1 inputs of one cycle**: the `BallHandleCycle`, its union is the rounded union, its
balls lie in `W.interior`, and under the certificate rim-product clause it is a rim product. -/
theorem toBallHandleCycle_spec (hprodD : D.RimProduct) (j : Fin P.cnt) :
    range (P.toBallHandleCycle j).union.map = P.unionSet j ∧
      (∀ k, range ((P.toBallHandleCycle j).ball k).map ⊆ (W.interior : Set W.Carrier)) ∧
      (P.toBallHandleCycle j).RimProduct :=
  ⟨P.range_toBallHandleCycle_union j, P.toBallHandleCycle_ball_subset_interior j,
    P.rimProduct_toBallHandleCycle hprodD j⟩

end CyclePartition

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **The cycles of FC42 step 6.** -/
theorem exists_ballHandleCycles_of_badVertexCount_eq_zero (hsph : D.sphereSeamCount = 0)
    (hbad : D.badVertexCount = 0) :
    ∃ (cnt : ℕ) (C : Fin cnt → BallHandleCycle W),
      Pairwise (fun j j' => Disjoint (range (C j).union.map) (range (C j').union.map)) ∧
      (∀ k, (D.vertex k).IsBall → ∃ j, (D.vertex k).image ⊆ range (C j).union.map) ∧
      (∀ h, ∃ j, range (D.handle h).map ⊆ range (C j).union.map) ∧
      (∀ j, range (C j).union.map ⊆ (W.interior : Set W.Carrier)) ∧
      ∀ j, (C j).union.map '' (𝓡∂ 3).boundary (C j).union.Piece =
        range (C j).union.map ∩ {x | x ∈ D.circ.domain ∧ D.circ.roundedFunction x = 0} := by
  obtain ⟨P⟩ := D.nonempty_cyclePartition_of_badVertexCount_eq_zero hsph hbad
  refine ⟨P.cnt, P.toBallHandleCycle, ?_, ?_, ?_, ?_, ?_⟩
  · intro j j' hjj
    rw [P.range_toBallHandleCycle_union, P.range_toBallHandleCycle_union]
    exact P.pairwise_disjoint_unionSet hjj
  · intro k hk
    refine ⟨(P.ballIdx.symm ⟨k, hk⟩).1, ?_⟩
    rw [P.range_toBallHandleCycle_union]
    exact P.vertex_image_subset_unionSet k hk
  · intro h
    refine ⟨(P.handleIdx.symm h).1, ?_⟩
    rw [P.range_toBallHandleCycle_union]
    exact P.handle_range_subset_unionSet h
  · intro j
    exact P.range_roundedUnion_subset_interior j
  · intro j
    rw [P.range_toBallHandleCycle_union]
    exact P.image_boundary_roundedUnion j

end DecompositionCertificate

end GC.GraphManifold.Assembly
