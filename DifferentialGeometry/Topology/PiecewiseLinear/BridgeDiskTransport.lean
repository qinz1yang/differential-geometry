/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskArc
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsBridgeDisk.image {C A B : Set E} {D : Set F} {a b : E}
    (h : IsBridgeDisk C A B a b) {f : E → F} (hf : IsPLHomeomorphOn f C D)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hC : IsClosed C) (hD : IsClosed D) :
    IsBridgeDisk D (f '' A) (f '' B) (f a) (f b) := by
  obtain ⟨q, hq, hBC, hbase, htrace, hq0, hq1⟩ := h
  have hB : IsPLBall 2 B := ⟨q, hq⟩
  have hfB := hf.restrict hB.isPolyhedron hBC
  refine ⟨f ∘ q, hq.trans hfB, (image_mono hBC).trans hf.image_eq.subset, ?_, ?_, ?_, ?_⟩
  · rw [image_comp, hbase]
  · rw [← hf.image_frontier hdim hC hD,
      ← hf.bijOn.injOn.image_inter hBC hC.frontier_subset, htrace, image_comp]
  · exact congrArg f hq0
  · exact congrArg f hq1

end DifferentialGeometry.Topology.PiecewiseLinear
