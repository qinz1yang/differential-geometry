/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentSubsurfaceEmbedding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasEssentialBoundaryPLEmbeddings.of_component_space_eq [d : DecidableEq E3]
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {T : Set E3}
    (h : HasEssentialBoundaryPLEmbeddings K T)
    (e : ConnectedComponents Q.space → ConnectedComponents K.space)
    (he : ∀ c, (connectedComponentComplex Q c).space =
      (connectedComponentComplex K (e c)).space) : HasEssentialBoundaryPLEmbeddings Q T := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let _ (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  let _ (c : ConnectedComponents Q.space) : Finite (connectedComponentComplex Q c).faces :=
    (connectedComponentComplex_faces_finite Q c).to_subtype
  intro c H hH hHQ hess
  have hf : IsPLHomeomorphOn (id : E3 → E3) (connectedComponentComplex K (e c)).space
      (connectedComponentComplex Q c).space := by
    rw [he c]
    exact (isPolyhedron_space (connectedComponentComplex K (e c))).isPLHomeomorphOn_id
  have hbd : (boundaryComplex 2 (connectedComponentComplex Q c)).space =
      (boundaryComplex 2 (connectedComponentComplex K (e c))).space := by
    simpa only [image_id] using boundaryComplex_space_of_isPLHomeomorphOn
      (connectedComponentComplex K (e c)) (connectedComponentComplex Q c)
      (hK.connectedComponentComplex (e c)) hf
  exact (h (e c) H hH (hHQ.trans hbd.subset) hess).of_isPLHomeomorphOn hf hbd (fun _ _ => rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
