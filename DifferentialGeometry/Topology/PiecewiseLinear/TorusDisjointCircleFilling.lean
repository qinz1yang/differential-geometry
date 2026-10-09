/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TorusTraceCircles

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_disk_of_nullhomotopic_circle_disjoint_carrier
    {ι : Type*} [Finite ι] {T J : Set E3} {F : ι → Set E3}
    (hT : IsCombinatorialSolidTorus T) (hF : ∀ i, IsPLSphere 1 (F i))
    (hFT : ∀ i, F i ⊆ frontier T) (hdis : Pairwise fun i j => Disjoint (F i) (F j))
    (hcarry : CarriesFirstHomologyOnto (⋃ i, F i) T)
    (hJ : IsPLSphere 1 J) (hJΘ : J ⊆ frontier T) (hJF : ∀ i, Disjoint J (F i))
    (hnull : (⟨inclusion (hJΘ.trans hT.isPolyhedron.isClosed.frontier_subset),
      continuous_inclusion _⟩ : C(J, T)).Nullhomotopic) :
    ∃ (D : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ frontier T ∧
        J = q '' stdSimplexBoundary 2 := by
  let G : Option ι → Set E3 := fun i => i.elim J F
  have hG : ∀ i, IsPLSphere 1 (G i) := by
    intro i
    cases i with
    | none => exact hJ
    | some i => exact hF i
  have hGT : ∀ i, G i ⊆ frontier T := by
    intro i
    cases i with
    | none => exact hJΘ
    | some i => exact hFT i
  have hGdis : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hJF j
    | some i =>
      cases j with
      | none => exact (hJF i).symm
      | some j => exact hdis (fun h => hij (congrArg Option.some h))
  have hFG : (⋃ i, F i) ⊆ ⋃ i, G i := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨some i, hxi⟩
  have hGsub : (⋃ i, G i) ⊆ T := iUnion_subset fun i =>
    (hGT i).trans hT.isPolyhedron.isClosed.frontier_subset
  have hzero := integralSingularHomologyMap_nullhomotopic 1 one_ne_zero hnull
  exact exists_disk_of_zero_trace_homology_image hT hG hGT hGdis
    (hcarry.mono hFG hGsub) none (hJΘ.trans hT.isPolyhedron.isClosed.frontier_subset) hzero

end DifferentialGeometry.Topology.PiecewiseLinear
