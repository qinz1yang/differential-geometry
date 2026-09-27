/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_eqOn_circle_of_isPLSphere_two
    {S J : Set E} {S' J' : Set F} (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ S) {g : E → F}
    (hg : IsPLHomeomorphOn g J J') (hJ'S' : J' ⊆ S') :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧ EqOn G g J := by
  obtain ⟨D, _, hcover, hmeet, p, _, hp, _, hpJ, _⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hS hJ hJS
  obtain ⟨D', _, hcover', _, q, _, hq, _, hqJ', _⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hS' (hJ.of_isPLHomeomorphOn hg) hJ'S'
  have hg' : IsPLHomeomorphOn g (p '' stdSimplexBoundary 2) (q '' stdSimplexBoundary 2) := by
    rwa [hpJ, hqJ']
  obtain ⟨f, hf, hfg⟩ := exists_isPLHomeomorphOn_of_stdSimplexBoundary hp hq hg'
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two hS hS'
    ⟨p, hp⟩ (subset_union_left.trans hcover.subset) hf (subset_union_left.trans hcover'.subset)
  refine ⟨G, hG, fun x hx => ?_⟩
  exact (hGf (inter_subset_left (hmeet.symm.subset hx))).trans (hfg (hpJ.symm.subset hx))

end DifferentialGeometry.Topology.PiecewiseLinear
