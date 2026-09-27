/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitEuler
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceHomology
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSphereRecognition

namespace DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitAndCap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {source split result : Geometry.SimplicialComplex ℝ E}
  [Finite source.faces] [Finite split.faces] [Finite result.faces]

theorem bettiOne_add_two_eq_of_isConnected (h : SurfaceSplitAndCap source split result)
    (hsource : IsCombinatorialManifold 2 source) (hsourceConn : IsConnected source.space)
    (hsourceOr : IsOrientable 2 source) (hresult : IsCombinatorialManifold 2 result)
    (hresultConn : IsConnected result.space) (hresultOr : IsOrientable 2 result) :
    Homology.bettiOne result.space + 2 = Homology.bettiOne source.space := by
  have hEuler := h.eulerChar_eq_add_two
  have hsourceEuler := hsource.eulerChar_eq_two_sub_bettiOne_of_isOrientable
    source hsourceConn hsourceOr
  have hresultEuler := hresult.eulerChar_eq_two_sub_bettiOne_of_isOrientable
    result hresultConn hresultOr
  omega

theorem bettiOne_lt_of_isConnected (h : SurfaceSplitAndCap source split result)
    (hsource : IsCombinatorialManifold 2 source) (hsourceConn : IsConnected source.space)
    (hsourceOr : IsOrientable 2 source) (hresult : IsCombinatorialManifold 2 result)
    (hresultConn : IsConnected result.space) (hresultOr : IsOrientable 2 result) :
    Homology.bettiOne result.space < Homology.bettiOne source.space := by
  have hsum := h.bettiOne_add_two_eq_of_isConnected hsource hsourceConn hsourceOr
    hresult hresultConn hresultOr
  omega

theorem bettiOne_add_eq_of_disjoint_union (h : SurfaceSplitAndCap source split result)
    (hsource : IsCombinatorialManifold 2 source) (hsourceConn : IsConnected source.space)
    (hsourceOr : IsOrientable 2 source)
    (A B : Geometry.SimplicialComplex ℝ E) [Finite A.faces] [Finite B.faces]
    (hA : IsCombinatorialManifold 2 A) (hAConn : IsConnected A.space) (hAOr : IsOrientable 2 A)
    (hB : IsCombinatorialManifold 2 B) (hBConn : IsConnected B.space) (hBOr : IsOrientable 2 B)
    (hfaces : result.faces = A.faces ∪ B.faces) (hdis : Disjoint A.faces B.faces) :
    Homology.bettiOne A.space + Homology.bettiOne B.space = Homology.bettiOne source.space := by
  have hEuler := h.eulerChar_eq_add_two
  have hsourceEuler := hsource.eulerChar_eq_two_sub_bettiOne_of_isOrientable
    source hsourceConn hsourceOr
  have hresultEuler := eulerChar_eq_add_of_faces_disjoint_union result A B hfaces hdis
  have hAEuler := hA.eulerChar_eq_two_sub_bettiOne_of_isOrientable A hAConn hAOr
  have hBEuler := hB.eulerChar_eq_two_sub_bettiOne_of_isOrientable B hBConn hBOr
  omega

theorem bettiOne_lt_of_disjoint_union_of_not_isPLSphere
    (h : SurfaceSplitAndCap source split result)
    (hsource : IsCombinatorialManifold 2 source) (hsourceConn : IsConnected source.space)
    (hsourceOr : IsOrientable 2 source)
    (A B : Geometry.SimplicialComplex ℝ E) [Finite A.faces] [Finite B.faces]
    (hA : IsCombinatorialManifold 2 A) (hAConn : IsConnected A.space) (hAOr : IsOrientable 2 A)
    (hB : IsCombinatorialManifold 2 B) (hBConn : IsConnected B.space) (hBOr : IsOrientable 2 B)
    (hfaces : result.faces = A.faces ∪ B.faces) (hdis : Disjoint A.faces B.faces)
    (hASphere : ¬ IsPLSphere 2 A.space) (hBSphere : ¬ IsPLSphere 2 B.space) :
    Homology.bettiOne A.space < Homology.bettiOne source.space ∧
      Homology.bettiOne B.space < Homology.bettiOne source.space := by
  have hsum := h.bettiOne_add_eq_of_disjoint_union hsource hsourceConn hsourceOr
    A B hA hAConn hAOr hB hBConn hBOr hfaces hdis
  have hAPos := hA.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two A hAConn hAOr
    (fun hχ => hASphere (hA.isPLSphere_two_of_faceEulerChar_eq_two A hAConn hχ))
  have hBPos := hB.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two B hBConn hBOr
    (fun hχ => hBSphere (hB.isPLSphere_two_of_faceEulerChar_eq_two B hBConn hχ))
  omega

end DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitAndCap
