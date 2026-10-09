/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleComponentClosure
import DifferentialGeometry.Topology.PiecewiseLinear.EulerUnion
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldCapping
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.exists_capped_pair_of_separating_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ K.space = r '' stdSimplexBoundary 2)
    (hsep : ¬ IsPreconnected (K.space \ r '' stdSimplexBoundary 2)) :
    ∃ (P Q : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite) (hQfin : Q.faces.Finite),
      letI := hPfin.to_subtype
      letI := hQfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsCombinatorialManifold 2 Q ∧
      IsConnected P.space ∧ IsConnected Q.space ∧
      eulerChar P + eulerChar Q = eulerChar K + 2 ∧
      P.space ∪ Q.space = K.space ∪ D ∧ P.space ∩ Q.space = D ∧
      ∃ a ∈ K.space \ r '' stdSimplexBoundary 2, ∃ b ∈ K.space \ r '' stdSimplexBoundary 2,
        P.space = closure (connectedComponentIn (K.space \ r '' stdSimplexBoundary 2) a) ∪ D ∧
        Q.space = closure (connectedComponentIn (K.space \ r '' stdSimplexBoundary 2) b) ∪ D ∧
        closure (connectedComponentIn (K.space \ r '' stdSimplexBoundary 2) a) ∩ D =
          r '' stdSimplexBoundary 2 ∧
        closure (connectedComponentIn (K.space \ r '' stdSimplexBoundary 2) b) ∩ D =
          r '' stdSimplexBoundary 2 := by
  classical
  let J := r '' stdSimplexBoundary 2
  have hJ : IsPLSphere 1 J := hr.isPLSphere_image_stdSimplexBoundary
  have hJK : J ⊆ K.space := hmeet.symm.subset.trans inter_subset_right
  have hJD : J ⊆ D := hmeet.symm.subset.trans inter_subset_left
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨A, B, hAfin, hBfin, hA, hB, -, -, hAc, hBc, hcover, hAB, hAbd, hBbd,
      a, ha, b, hb, hAcomp, hBcomp⟩ :=
    hK.exists_manifold_pair_of_separating_circle K hor hconn hJ hJK hsep
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hinter {X : Set E} (hXK : X ⊆ K.space) (hJX : J ⊆ X) : X ∩ D = J :=
    Subset.antisymm (fun _ hx => hmeet.subset ⟨hx.2, hXK hx.1⟩)
      (fun _ hx => ⟨hJX hx, hJD hx⟩)
  have hAD : A.space ∩ D = J := hinter (subset_union_left.trans hcover.subset)
    (hAB.symm.subset.trans inter_subset_left)
  have hBD : B.space ∩ D = J := hinter (subset_union_right.trans hcover.subset)
    (hAB.symm.subset.trans inter_subset_right)
  obtain ⟨P, hPfin, hP, hPspace⟩ :=
    hA.exists_isCombinatorialManifold_union_ball A hr hAD hAbd
  obtain ⟨Q, hQfin, hQ, hQspace⟩ :=
    hB.exists_isCombinatorialManifold_union_ball B hr hBD hBbd
  let _ : Finite P.faces := hPfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  have hPc : IsConnected P.space := by
    rw [hPspace]
    exact IsConnected.union (hAD.symm ▸ hJ.isConnected.nonempty) hAc hD.isConnected
  have hQc : IsConnected Q.space := by
    rw [hQspace]
    exact IsConnected.union (hBD.symm ▸ hJ.isConnected.nonempty) hBc hD.isConnected
  obtain ⟨C, hCfin, hCspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite C.faces := hCfin.to_subtype
  have hC : eulerChar C = 1 := eulerChar_of_isPLBall C (hCspace.symm ▸ hD)
  have hEulerP : eulerChar P = eulerChar A + eulerChar C :=
    eulerChar_eq_add_of_space_union_of_isPLSphere_one P A C
      (by rw [hCspace]; exact hPspace) (by rw [hCspace, hAD]; exact hJ)
  have hEulerQ : eulerChar Q = eulerChar B + eulerChar C :=
    eulerChar_eq_add_of_space_union_of_isPLSphere_one Q B C
      (by rw [hCspace]; exact hQspace) (by rw [hCspace, hBD]; exact hJ)
  have hEulerK := eulerChar_eq_add_of_space_union_of_isPLSphere_one K A B hcover.symm
    (hAB.symm ▸ hJ)
  refine ⟨P, Q, hPfin, hQfin, hP, hQ, hPc, hQc, by omega, ?_, ?_, a, ha, b, hb,
    hPspace.trans (congrArg (· ∪ D) hAcomp), hQspace.trans (congrArg (· ∪ D) hBcomp),
    by rwa [← hAcomp], by rwa [← hBcomp]⟩
  · rw [hPspace, hQspace, ← hcover]
    ext x
    simp only [mem_union]
    tauto
  · rw [hPspace, hQspace]
    apply Subset.antisymm
    · rintro x ⟨hxA | hxD, hxB | hxD⟩
      · exact hJD (hAB.subset ⟨hxA, hxB⟩)
      · exact hxD
      · exact hxD
      · exact hxD
    · exact fun _ hx => ⟨Or.inr hx, Or.inr hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
