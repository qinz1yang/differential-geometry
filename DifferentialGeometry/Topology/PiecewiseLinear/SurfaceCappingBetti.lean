/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCapping
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCapping
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanSurfaceOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceHomology
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSphereRecognition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.exists_capped_pair_of_separating_essential_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected K.space) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ K.space = r '' stdSimplexBoundary 2)
    (hsep : ¬ IsPreconnected (K.space \ r '' stdSimplexBoundary 2))
    (hnon : ¬ (⟨Set.inclusion (hmeet.symm.subset.trans inter_subset_right),
      continuous_inclusion _⟩ : C(r '' stdSimplexBoundary 2, K.space)).Nullhomotopic) :
    ∃ (P Q : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite) (hQfin : Q.faces.Finite),
      letI := hPfin.to_subtype
      letI := hQfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsCombinatorialManifold 2 Q ∧
      IsConnected P.space ∧ IsConnected Q.space ∧ IsOrientable 2 P ∧ IsOrientable 2 Q ∧
      ¬ IsPLSphere 2 P.space ∧ ¬ IsPLSphere 2 Q.space ∧
      Homology.bettiOne P.space + Homology.bettiOne Q.space = Homology.bettiOne K.space ∧
      Homology.bettiOne P.space < Homology.bettiOne K.space ∧
      Homology.bettiOne Q.space < Homology.bettiOne K.space ∧
      P.space ∪ Q.space = K.space ∪ D ∧ P.space ∩ Q.space = D ∧
      ∃ a ∈ K.space \ r '' stdSimplexBoundary 2, ∃ b ∈ K.space \ r '' stdSimplexBoundary 2,
        P.space = closure (connectedComponentIn (K.space \ r '' stdSimplexBoundary 2) a) ∪ D ∧
        Q.space = closure (connectedComponentIn (K.space \ r '' stdSimplexBoundary 2) b) ∪ D := by
  have hor := hK.isOrientable_of_finrank_eq_three K hdim hconn
  obtain ⟨P, Q, hPfin, hQfin, hP, hQ, hPc, hQc, hEuler, hcover, hPQ,
      a, ha, b, hb, hPspace, hQspace, hAD, hBD⟩ :=
    hK.exists_capped_pair_of_separating_circle K hor hconn.isPreconnected hr hmeet hsep
  let _ : Finite P.faces := hPfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  have hPo := hP.isOrientable_of_finrank_eq_three P hdim hPc
  have hQo := hQ.isOrientable_of_finrank_eq_three Q hdim hQc
  have hsubset (x : E) : closure (connectedComponentIn
      (K.space \ r '' stdSimplexBoundary 2) x) ⊆ K.space :=
    closure_minimal ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (isPolyhedron_space K).isClosed
  have hPsphere : ¬ IsPLSphere 2 P.space := by
    intro hSphere
    rw [hPspace] at hSphere
    exact hnon (hSphere.nullhomotopic_inclusion_of_union_disk hr hAD (hsubset a))
  have hQsphere : ¬ IsPLSphere 2 Q.space := by
    intro hSphere
    rw [hQspace] at hSphere
    exact hnon (hSphere.nullhomotopic_inclusion_of_union_disk hr hBD (hsubset b))
  have hEulerK := hK.eulerChar_eq_two_sub_bettiOne_of_isOrientable K hconn hor
  have hEulerP := hP.eulerChar_eq_two_sub_bettiOne_of_isOrientable P hPc hPo
  have hEulerQ := hQ.eulerChar_eq_two_sub_bettiOne_of_isOrientable Q hQc hQo
  have hsum : Homology.bettiOne P.space + Homology.bettiOne Q.space =
      Homology.bettiOne K.space := by omega
  have hPpos := hP.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two P hPc hPo
    (fun hχ => hPsphere (hP.isPLSphere_two_of_faceEulerChar_eq_two P hPc hχ))
  have hQpos := hQ.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two Q hQc hQo
    (fun hχ => hQsphere (hQ.isPLSphere_two_of_faceEulerChar_eq_two Q hQc hχ))
  exact ⟨P, Q, hPfin, hQfin, hP, hQ, hPc, hQc, hPo, hQo, hPsphere, hQsphere,
    hsum, by omega, by omega, hcover, hPQ, a, ha, b, hb, hPspace, hQspace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
