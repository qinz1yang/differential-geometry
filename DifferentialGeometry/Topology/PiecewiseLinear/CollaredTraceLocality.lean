/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteCollaredTrace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem traceCircles_eq_of_inter_eq {L L' T : Set E3} (heq : L' ∩ T = L ∩ T) :
    traceCircles L' T = traceCircles L T := by
  simp only [traceCircles, heq]

theorem nullTraceCount_eq_of_inter_eq {L L' T : Set E3} (heq : L' ∩ T = L ∩ T) :
    nullTraceCount L' T = nullTraceCount L T := by
  simp only [nullTraceCount, traceCircles_eq_of_inter_eq heq]

theorem HasFiniteCollaredTrace.of_locally_eq {L L' T U : Set E3}
    (h : HasFiniteCollaredTrace L T) (hL' : IsPolyhedron L')
    (hU : IsOpen U) (hTU : T ⊆ U) (heq : L' ∩ U = L ∩ U) :
    HasFiniteCollaredTrace L' T := by
  have hmeet : L' ∩ T = L ∩ T := by
    ext x
    exact ⟨fun hx => ⟨(heq.subset ⟨hx.1, hTU hx.2⟩).1, hx.2⟩,
      fun hx => ⟨(heq.symm.subset ⟨hx.1, hTU hx.2⟩).1, hx.2⟩⟩
  have htrace := traceCircles_eq_of_inter_eq hmeet
  refine ⟨hL', htrace.symm ▸ h.finiteTrace, ?_, ?_⟩
  · rw [hmeet, htrace]
    exact h.traceCover
  · intro G hG
    rw [htrace] at hG
    exact (h.circleCollar G hG).of_locally_eq hU
      ((traceCircles_subset hG).trans (inter_subset_right.trans hTU)) heq

end DifferentialGeometry.Topology.PiecewiseLinear
