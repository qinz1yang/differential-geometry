/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TubeSplitDiskComponents

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_isHandleDecompositionOfTube :
    ∃ (K : Geometry.SimplicialComplex ℝ E3) (N : Set E3)
      (C : E3 → Set E3) (D Dbd : Finset E3 → Set E3)
      (h : E3 → E3) (N' : Set E3)
      (Ec Eint Ebd : Finset E3 → Set E3) (Cpp : E3 → Set E3),
      IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp ∧
      ∃ e ∈ K.faces, e.card = 2 := by
  obtain ⟨K, N, C, D, Dbd, ht, hedge, hpseudo⟩ :=
    exists_isTube_id_with_pseudoCell_splitDisks
  refine ⟨K, N, C, D, Dbd, id, N, D, (fun e => D e \ Dbd e),
    Dbd, C, ?_, hedge⟩
  refine
    { tube := ht
      pseudoCell := hpseudo
      rimEq := ?_
      rimFrontier := ?_
      meetsGraph := ?_
      pseudoCellDisjoint := ?_
      oneVertex := ?_
      coversTube := ht.unionEq
      componentClosure := ?_
      handleEdge := ?_
      handleNonEdge := ?_ }
  · intro e he hc
    simp
  · intro e he hc
    exact ht.splitProper e he hc
  · intro e he hc
    simpa [id] using ht.splitMidpoint he hc
  · intro e he hc f hf hfc hef
    exact ht.splitDisjoint he hc hf hfc hef
  · intro v hv
    simpa [id] using ht.dualVertex hv
  · intro v hv
    exact (ht.connectedComponentIn_splitDisk_complement hv).2.symm
  · intro u hu v hv huv he
    exact ht.interEdge hu hv huv he
  · intro u hu v hv huv he
    exact ht.interNonEdge hu hv huv he

end DifferentialGeometry.Topology.PiecewiseLinear
