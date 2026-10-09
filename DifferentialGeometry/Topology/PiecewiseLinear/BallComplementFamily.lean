/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPolyhedron.sdiff_iUnion_interior_of_isPLBall
    {n : ℕ} {ι : Type*} [Finite ι]
    {D : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {H : ι → Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hD : IsPolyhedron D) (hH : ∀ i, IsPLBall (n + 1) (H i)) :
    IsPolyhedron (D \ ⋃ i, interior (H i)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hind : ∀ d : Finset ι, IsPolyhedron (D \ ⋃ i ∈ d, interior (H i)) := by
    intro d
    induction d using Finset.induction_on with
    | empty => simpa using hD
    | @insert i d _ ih =>
      rw [Finset.set_biUnion_insert]
      convert ih.sdiff_interior_of_isPLBall (hH i) using 1
      ext x
      simp only [mem_sdiff, mem_union]
      tauto
  simpa only [Finset.mem_univ, iUnion_true] using hind Finset.univ

end DifferentialGeometry.Topology.PiecewiseLinear
