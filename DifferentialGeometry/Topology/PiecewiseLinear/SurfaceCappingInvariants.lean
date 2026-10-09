/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfacePartialCapping
import DifferentialGeometry.Topology.PiecewiseLinear.EulerUnion
import DifferentialGeometry.Topology.PiecewiseLinear.OrientableSurfaceEulerParity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_surface_of_isPLHomeomorphOn_union_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hKo : IsOrientable 2 K)
    {Δ : Set E} {L : Set F} {r : (Fin 3 → ℝ) → E} {f : E → F}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hmeet : K.space ∩ Δ = r '' stdSimplexBoundary 2)
    (hcollar : HasPLCircleCollar K.space (r '' stdSimplexBoundary 2))
    (hf : IsPLHomeomorphOn f (K.space ∪ Δ) L) :
    ∃ (Q : Geometry.SimplicialComplex ℝ F) (hQfin : Q.faces.Finite),
      letI := hQfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 Q ∧ IsOrientable 2 Q ∧ Q.space = L ∧
      (boundaryComplex 2 Q).space = f '' ((boundaryComplex 2 K).space \
        r '' stdSimplexBoundary 2) ∧ eulerChar Q = eulerChar K + 1 := by
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  let _ : DecidableEq F := fun a b => Classical.propDecidable (a = b)
  have hΔ : IsPLBall 2 Δ := ⟨r, hr⟩
  have hJ : IsPLSphere 1 (r '' stdSimplexBoundary 2) :=
    hr.isPLSphere_image_stdSimplexBoundary
  have hL : IsPolyhedron L := hf.image_eq ▸
    ((isPolyhedron_space K).union hΔ.isPolyhedron).image_of_isPiecewiseAffineOn
      hf.isPiecewiseAffineOn hf.bijOn.injOn
  obtain ⟨C, hCfin, hC, hCspace, hCb⟩ :=
    hK.exists_surface_union_disk_of_circle_collar K hr hmeet hcollar
  obtain ⟨D, hDfin, hDspace⟩ := hΔ.isPolyhedron.exists_simplicialComplex
  obtain ⟨Q, hQfin, hQspace⟩ := hL.exists_simplicialComplex
  let _ : Finite C.faces := hCfin.to_subtype
  let _ : Finite D.faces := hDfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  have hD : IsPLBall 2 D.space := hDspace.symm ▸ hΔ
  have hCD : C.space = K.space ∪ D.space := by rw [hDspace, hCspace]
  have hmeetD : K.space ∩ D.space = r '' stdSimplexBoundary 2 := by rw [hDspace, hmeet]
  have hCo : IsOrientable 2 C := IsOrientable.of_space_eq_union hC hK
    hD.isCombinatorialManifoldWithBoundary hCD
    (hmeetD.symm ▸ hJ.isConnected.isPreconnected) hKo (isOrientable_of_isPLBall hD)
  have hfCQ : IsPLHomeomorphOn f C.space Q.space := by rw [hCspace, hQspace]; exact hf
  have hQ := hC.of_isPLHomeomorphOn hfCQ
  have hQo := (isOrientable_iff_of_isPLHomeomorphOn hC hfCQ).mp hCo
  have hχ := eulerChar_eq_add_of_space_union_of_isPLSphere_one C K D hCD (hmeetD.symm ▸ hJ)
  have hDχ := eulerChar_of_isPLBall D hD
  have hCQχ := eulerChar_eq_of_isPLHomeomorphOn C Q hfCQ
  refine ⟨Q, hQfin, hQ, hQo, hQspace, ?_, by omega⟩
  rw [boundaryComplex_space_of_isPLHomeomorphOn C Q hC hfCQ, hCb]

end DifferentialGeometry.Topology.PiecewiseLinear
