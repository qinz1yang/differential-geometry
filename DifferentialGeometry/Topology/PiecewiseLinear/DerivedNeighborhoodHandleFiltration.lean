/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodFiltration
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodHandleAttachment

/-! Finite PL handle filtrations produced from closed combinatorial three-manifolds. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.SimplicialComplex (geometricFacePrefix geometricFacePrefix_le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_pl_three_handle_filtration
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) :
    ∃ m : ℕ, ∃ e : Fin m ≃ K.faces, ∃ he : Monotone (fun i => (e i).val.card),
      ∃ k : Fin m → Fin 4, (∀ i, (k i).val + 1 = (e i).val.card) ∧ Monotone k ∧
      let L := geometricFacePrefix K e he
      let N := fun i => derivedNeighborhood K (L i)
      (N 0).space = ∅ ∧ (N m).space = K.space ∧ Monotone (fun i => (N i).space) ∧
        (∀ i, IsCombinatorialManifoldWithBoundary 3 (N i)) ∧
        ∀ i : Fin m, IsPLThreeHandleAttachment (k i) (N i.val)
          (derivedNeighborhoodCell K (e i).val).space (N (i.val + 1)).space := by
  classical
  obtain ⟨m, e, he, hzero, hlast, hmono, hman, hstep⟩ :=
    exists_derivedNeighborhood_filtration K hK.isCombinatorialManifoldWithBoundary
  have hbound (i : Fin m) : (e i).val.card - 1 < 4 := by
    have hcard := hK.card_le K (e i).property
    omega
  let k : Fin m → Fin 4 := fun i => ⟨(e i).val.card - 1, hbound i⟩
  have hk (i : Fin m) : (k i).val + 1 = (e i).val.card := by
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces (e i).property)
    dsimp only [k]
    omega
  refine ⟨m, e, he, k, hk, ?_, hzero, hlast, hmono, hman, ?_⟩
  · intro i j hij
    change (e i).val.card - 1 ≤ (e j).val.card - 1
    exact Nat.sub_le_sub_right (he hij) 1
  · intro i
    have hi := hstep i
    dsimp only at hi ⊢
    rw [hi.2.2.2.1]
    exact isPLThreeHandleAttachment_derivedNeighborhoodCell K _ hK
      (geometricFacePrefix_le K e he i.val) (e i).property hi.1 hi.2.2.1 hi.2.1 (k i)
      (hk i).symm

end DifferentialGeometry.Topology.PiecewiseLinear
