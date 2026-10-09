/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.EmbeddingParity
import Mathlib.Topology.Instances.RealVectorSpace

open Set Filter
open scoped Topology

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem euclideanLocalDegree_sub_eq_one_of_eqOn_compl_isCompact
    {f : E → E} (hf : Continuous f) (hinj : Function.Injective f)
    {K : Set E} (hK : IsCompact K) (hfix : EqOn f id Kᶜ) (x : E) :
    euclideanLocalDegree (fun z => f z - f x) x
      (isolatedZero_sub_of_injOn isOpen_univ hf.continuousOn hinj.injOn (mem_univ x)) = 1 := by
  obtain ⟨y, hy⟩ := Set.nonempty_compl.mpr hK.ne_univ
  have heq : f =ᶠ[𝓝 y] id :=
    Filter.mem_of_superset (hK.isClosed.isOpen_compl.mem_nhds hy) (fun z hz => hfix hz)
  have hzero := embeddingOrientationParity_congr isOpen_univ isOpen_univ
    hf.continuousOn hinj.injOn continuousOn_id (injOn_id univ)
    (mem_univ y) (mem_univ y) heq
  rw [embeddingOrientationParity_id] at hzero
  apply (embeddingOrientationParity_eq_zero_iff isOpen_univ hf.continuousOn
    hinj.injOn ⟨x, mem_univ x⟩).mp
  exact (embeddingOrientationParity_eq_of_isPreconnected isOpen_univ hf.continuousOn
    hinj.injOn isPreconnected_univ Subset.rfl (mem_univ x) (mem_univ y)).trans hzero

end DifferentialGeometry.LocalDegree
