/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.interior_eq_empty_of_lt_three {d : ℕ} {C B : Set M}
    (hC : IsPLCellOn d C B) (hd : d < 3) : interior C = ∅ := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hC
  rw [← hu.image_interior]
  have hP : IsPLBall d P := ⟨r, hr⟩
  rw [hP.interior_eq_empty_of_lt_finrank (by simpa using hd), image_empty]

private theorem cell_subset_closure_interior {C B : Set M} (hC : IsPLCellOn 3 C B) :
    C ⊆ closure (interior C) := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hC
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  rw [← hu.image_interior]
  have hcont : ContinuousOn u (closure (interior P)) := by
    rw [hP.closure_interior]
    exact hu.continuousOn
  have h := hcont.image_closure
  rwa [hP.closure_interior] at h

theorem IsPLCellOn.inter_subset_boundary_of_isPLCellOn
    {C CB D DB I : Set M} (hC : IsPLCellOn 3 C CB) (hD : IsPLCellOn 3 D DB)
    (hI : IsPLCellOn 2 (C ∩ D) I) : C ∩ D ⊆ CB := by
  have hdis : interior C ∩ interior D = ∅ := by
    rw [← interior_inter]
    exact hI.interior_eq_empty_of_lt_three (by decide)
  intro x hx
  by_contra hxB
  have hxint : x ∈ interior C := hC.sdiff_boundary_eq_interior.subset ⟨hx.1, hxB⟩
  have hxcl : x ∈ closure (interior C ∩ interior D) :=
    isOpen_interior.inter_closure ⟨hxint, cell_subset_closure_interior hD hx.2⟩
  simp only [hdis, closure_empty, mem_empty_iff_false] at hxcl

end DifferentialGeometry.Topology.PiecewiseLinear
