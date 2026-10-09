/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerOddSurface
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldDisjointUnion
import DifferentialGeometry.Topology.PiecewiseLinear.OrientableSurfaceEulerParity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.exists_adjacentOdd_surface [d : DecidableEq E3]
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ (X : Geometry.SimplicialComplex ℝ E3) (hXfin : X.faces.Finite),
      letI := hXfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 X ∧ IsOrientable 2 X ∧
      X.space = canonicalOddPiece S'' T'' (i - 1) ∪ canonicalOddPiece S'' T'' i ∧
      (boundaryComplex 2 X).space =
        (canonicalOddPiece S'' T'' (i - 1) ∩ (T'' (2 * i - 2) ∪ T'' (2 * i))) ∪
          (canonicalOddPiece S'' T'' i ∩ (T'' (2 * i) ∪ T'' (2 * i + 2))) ∧
      (boundaryComplex 2 X).space ∩ interior (φ '' S (2 * i)) ⊆ T'' (2 * i) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨X₀, hX₀fin, hX₀, hX₀o, hX₀space, hX₀b⟩ := htw.exists_oddPiece_surface (i - 1)
  obtain ⟨X₁, hX₁fin, hX₁, hX₁o, hX₁space, hX₁b⟩ := htw.exists_oddPiece_surface i
  let _ : Finite X₀.faces := hX₀fin.to_subtype
  let _ : Finite X₁.faces := hX₁fin.to_subtype
  have hdis : Disjoint X₀.space X₁.space := by
    rw [hX₀space, hX₁space]
    exact (htw.apart (2 * (i - 1) + 1) (2 * i + 1) (by rw [le_abs]; omega)).mono
      (fun x hx => htw.boundary_subset_outer _ hx.1)
      (fun x hx => htw.boundary_subset_outer _ hx.1)
  obtain ⟨X, hXfin, hX, hXspace, hXb⟩ :=
    hX₀.exists_space_disjoint_union X₀ X₁ hX₁ hdis
  let _ : Finite X.faces := hXfin.to_subtype
  have hXo : IsOrientable 2 X := IsOrientable.of_space_eq_union hX hX₀ hX₁ hXspace
    (hdis.inter_eq.symm ▸ isPreconnected_empty) hX₀o hX₁o
  have hXb' : (boundaryComplex 2 X).space =
      (canonicalOddPiece S'' T'' (i - 1) ∩ (T'' (2 * i - 2) ∪ T'' (2 * i))) ∪
        (canonicalOddPiece S'' T'' i ∩ (T'' (2 * i) ∪ T'' (2 * i + 2))) := by
    rw [hXb, hX₀b, hX₁b]
    rw [show 2 * (i - 1) = 2 * i - 2 by omega,
      show 2 * i - 2 + 2 = 2 * i by omega]
  refine ⟨X, hXfin, hX, hXo, by rw [hXspace, hX₀space, hX₁space], hXb', ?_⟩
  rintro x ⟨hxB, hxO⟩
  rcases hXb'.subset hxB with ⟨-, hxLo | hxT⟩ | ⟨-, hxT | hxHi⟩
  · exact (disjoint_left.mp (htw.apart (2 * i) (2 * i - 2) (by rw [le_abs]; omega))
      (interior_subset hxO) (htw.boundary_subset_outer _ hxLo)).elim
  · exact hxT
  · exact hxT
  · exact (disjoint_left.mp (htw.apart (2 * i) (2 * i + 2) (by rw [le_abs]; omega))
      (interior_subset hxO) (htw.boundary_subset_outer _ hxHi)).elim

end DifferentialGeometry.Topology.PiecewiseLinear
