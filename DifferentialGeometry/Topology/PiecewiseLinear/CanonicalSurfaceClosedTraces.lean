/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.inter_even_subset_boundary
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i k : ℤ) :
    (X i).space ∩ T'' (2 * k) ⊆ (boundaryComplex 2 (X i)).space := by
  rintro x ⟨hx, hxT⟩
  rw [hX.boundary i]
  refine ⟨hx, ?_⟩
  by_cases hki : k = i
  · exact Or.inl (hki ▸ hxT)
  · by_cases hki' : k = i + 1
    · exact Or.inr (hki' ▸ hxT)
    · rcases hX.carrier i hx with (hxLo | hxMid) | hxHi
      · exact (disjoint_left.mp (htw.apart (2 * i) (2 * k) (by rw [le_abs]; omega))
          hxLo (htw.boundary_subset_outer _ hxT)).elim
      · exact (disjoint_left.mp (htw.apart (2 * i + 1) (2 * k) (by rw [le_abs]; omega))
          hxMid (htw.boundary_subset_outer _ hxT)).elim
      · exact (disjoint_left.mp (htw.apart (2 * (i + 1)) (2 * k) (by rw [le_abs]; omega))
          hxHi (htw.boundary_subset_outer _ hxT)).elim

theorem IsCanonicalSurface.closed_component_disjoint_even
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i : ℤ) (c : ConnectedComponents (X i).space)
    (hclosed : (boundaryComplex 2 (connectedComponentComplex (X i) c)).space = ∅) (k : ℤ) :
    Disjoint (connectedComponentComplex (X i) c).space (T'' (2 * k)) := by
  have hsub : (connectedComponentComplex (X i) c).space ⊆ (X i).space :=
    (subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  apply disjoint_left.mpr
  intro x hxC hxT
  have hxB := hX.inter_even_subset_boundary htw i k ⟨hsub hxC, hxT⟩
  have hxBC := (boundaryComplex_space_connectedComponentComplex 2 (X i) c).symm.subset
    ⟨hxB, hxC⟩
  exact notMem_empty x (hclosed ▸ hxBC)

end DifferentialGeometry.Topology.PiecewiseLinear
