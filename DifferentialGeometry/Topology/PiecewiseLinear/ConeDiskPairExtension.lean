/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereDiskMarked
import DifferentialGeometry.Topology.PiecewiseLinear.BallPair

/-!
# Relative extensions of marked cone pairs
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked
    {p : E} {Lc : Geometry.SimplicialComplex ℝ E} [Finite Lc.faces] (hLc : IsConeBase p Lc)
    {X : Set E} (hXLc : X ⊆ Lc.space) (hSph : IsPLSphere 2 Lc.space)
    {q : F} {Lc' : Geometry.SimplicialComplex ℝ F} [Finite Lc'.faces] (hLc' : IsConeBase q Lc')
    {X' : Set F} (hSph' : IsPLSphere 2 Lc'.space)
    {D : Set E} {D' : Set F} (hD : IsPLBall 2 D) (hDS : D ⊆ Lc.space) (hD'S' : D' ⊆ Lc'.space)
    {g : E → F} (hg : IsPLHomeomorphOn g D D')
    {y : E} (hy : y ∈ closure (Lc.space \ D) \ D)
    {y' : F} (hy' : y' ∈ closure (Lc'.space \ D') \ D')
    (hJsplit : X = X ∩ D ∪ {y}) (hJ'split : X' = X' ∩ D' ∪ {y'})
    (hgJ : g '' (X ∩ D) = X' ∩ D') :
    ∃ G : E → F, IsPLHomeomorphOn G (coneSet p Lc.space) (coneSet q Lc'.space) ∧
      EqOn G g D ∧ G p = q ∧ G '' coneSet p X = coneSet q X' ∧ G '' Lc.space = Lc'.space := by
  classical
  obtain ⟨Gs, hGs, hGseq, hGsy⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two_marked hSph hSph' hD hDS hg hD'S' hy hy'
  have hGsJ : Gs '' X = X' := by
    rw [hJsplit, image_union, image_singleton, hGsy,
      (hGseq.mono inter_subset_right).image_eq, hgJ, ← hJ'split]
  obtain ⟨G, hG, hGeq, hGp, hGJ⟩ :=
    exists_isPLHomeomorphOn_coneSet_pair hLc hXLc hLc' hGs hGsJ
  exact ⟨G, hG, (hGeq.mono hDS).trans hGseq, hGp, hGJ, hGeq.image_eq.trans hGs.image_eq⟩

end DifferentialGeometry.Topology.PiecewiseLinear
