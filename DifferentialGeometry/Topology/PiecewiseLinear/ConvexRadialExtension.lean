/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexCone
import DifferentialGeometry.Topology.PiecewiseLinear.ConeExtension

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_of_convex_frontier
    {C : Set E} {D : Set F} (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCc : IsCompact C) (hDc : IsCompact D)
    (hCf : IsPolyhedron (frontier C)) (hDf : IsPolyhedron (frontier D))
    {p : E} {q : F} (hp : p ∈ interior C) (hq : q ∈ interior D)
    {f : E → F} (hf : IsPLHomeomorphOn f (frontier C) (frontier D)) :
    ∃ g : E → F, IsPLHomeomorphOn g C D ∧ EqOn g f (frontier C) ∧ g p = q ∧
      ∀ z ∈ frontier C, ∀ s ∈ Icc (0 : ℝ) 1,
        g (p + s • (z - p)) = q + s • (f z - q) := by
  classical
  obtain ⟨K, hKfin, hKspace⟩ := hCf.exists_simplicialComplex
  obtain ⟨L, hLfin, hLspace⟩ := hDf.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let hK := isConeBase_of_space_subset_frontier_convex hC hCc.isClosed hp K hKspace.le
  let hL := isConeBase_of_space_subset_frontier_convex hD hDc.isClosed hq L hLspace.le
  have hKC : (coneComplex hK).space = C :=
    coneComplex_space_eq_of_convex hC hCc (interior_subset hp) hK hKspace
  have hLD : (coneComplex hL).space = D :=
    coneComplex_space_eq_of_convex hD hDc (interior_subset hq) hL hLspace
  have hf' : IsPLHomeomorphOn f K.space L.space := by
    rw [hKspace, hLspace]
    exact hf
  obtain ⟨g, hg, hgf, hgp, hgr⟩ := exists_isPLHomeomorphOn_coneComplex hK hL hf'
  rw [hKC, hLD] at hg
  rw [hKspace] at hgf hgr
  exact ⟨g, hg, hgf, hgp, fun z hz s hs => hgr z hz s hs.1 hs.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
