/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDisk
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem EmbeddedDisk.exists_isSubdivision_simplicialMap {S : NormalSystem E}
    (D : EmbeddedDisk S) :
    ∃ (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (M : Geometry.SimplicialComplex ℝ E),
      P.faces.Finite ∧ M.faces.Finite ∧ P.space = D.domain ∧
      IsSubdivision M S.manifoldComplex ∧
      (∀ s ∈ P.faces, s.image D.map ∈ M.faces) ∧
      EqOn (simplicialMap P D.map) D.map D.domain := by
  obtain ⟨P₀, hP₀fin, hP₀space⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  let _ : Finite P₀.faces := hP₀fin.to_subtype
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  have hpa : IsPiecewiseAffineOn D.map P₀.space := by
    rw [hP₀space]; exact D.isPLHomeomorphOn.isPiecewiseAffineOn
  have hmap : MapsTo D.map P₀.space S.manifoldComplex.space := by
    rw [hP₀space]; exact D.mapsTo
  obtain ⟨P, M, hPfin, hMfin, hPsub, hMsub, hfaces, heq⟩ :=
    hpa.exists_isSubdivision_simplicialMap P₀ S.manifoldComplex hmap
  exact ⟨P, M, hPfin, hMfin, hPsub.space_eq.trans hP₀space, hMsub, hfaces,
    hP₀space ▸ heq⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
