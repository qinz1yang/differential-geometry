/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.BasedCircle

open Set

namespace DifferentialGeometry.Topology

theorem not_injective_path_loop {X : Type*} [TopologicalSpace X] {x : X}
    (γ : Path x x) : ¬ Function.Injective γ := by
  intro h
  have hzero : γ (0 : Set.Icc (0 : ℝ) 1) = γ (1 : Set.Icc (0 : ℝ) 1) :=
    γ.source.trans γ.target.symm
  have h01 : (0 : Set.Icc (0 : ℝ) 1) = 1 := h hzero
  norm_num at h01

end DifferentialGeometry.Topology
