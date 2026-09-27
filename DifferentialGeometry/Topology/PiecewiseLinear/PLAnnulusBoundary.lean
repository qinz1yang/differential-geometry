/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusEnds

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.boundaryComplex_space [d : DecidableEq E3]
    (K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] {J₀ J₁ : Set E3}
    (h : IsPLAnnulusWithEnds K.space J₀ J₁) :
    (boundaryComplex 2 K).space = J₀ ∪ J₁ := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨L, hLfin, hL, -, hLK, hLb⟩ := h.exists_complex
  let _ : Finite L.faces := hLfin.to_subtype
  have hid : IsPLHomeomorphOn (id : E3 → E3) L.space K.space := by
    rw [hLK]
    exact (isPolyhedron_space K).isPLHomeomorphOn_id
  simpa only [image_id, hLb] using
    boundaryComplex_space_of_isPLHomeomorphOn L K hL hid

end DifferentialGeometry.Topology.PiecewiseLinear
