/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldCapping
import DifferentialGeometry.Topology.PiecewiseLinear.EulerUnion
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

/-!
# Capping two boundary circles of a connected surface
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_closed_of_disk_pair
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (stdSimplex ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hmeet₀ : K.space ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : K.space ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hboundary : (boundaryComplex 2 K).space =
      r₀ '' stdSimplexBoundary 2 ∪ r₁ '' stdSimplexBoundary 2) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hRfin : R.faces.Finite),
      letI := hRfin.to_subtype
      IsCombinatorialManifold 2 R ∧ IsConnected R.space ∧
      eulerChar R = eulerChar K + 2 ∧ R.space = K.space ∪ D₀ ∪ D₁ := by
  have hD₀ : IsPLBall 2 D₀ := ⟨r₀, hr₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨r₁, hr₁⟩
  have hJ₀ : IsPLSphere 1 (r₀ '' stdSimplexBoundary 2) := hr₀.isPLSphere_image_stdSimplexBoundary
  have hJ₁ : IsPLSphere 1 (r₁ '' stdSimplexBoundary 2) := hr₁.isPLSphere_image_stdSimplexBoundary
  obtain ⟨R, hRfin, hR, hRspace⟩ :=
    hK.exists_isCombinatorialManifold_union_ball_pair K hr₀ hr₁ hdis hmeet₀ hmeet₁ hboundary
  let _ : Finite R.faces := hRfin.to_subtype
  have hinter : (K.space ∪ D₀) ∩ D₁ = r₁ '' stdSimplexBoundary 2 := by
    rw [union_inter_distrib_right, hmeet₁, hdis.inter_eq, union_empty]
  have hRc : IsConnected R.space := by
    rw [hRspace]
    exact IsConnected.union (hinter.symm ▸ hJ₁.nonempty)
      (IsConnected.union (hmeet₀.symm ▸ hJ₀.nonempty) hconn hD₀.isConnected) hD₁.isConnected
  obtain ⟨A, hAfin, hAspace⟩ := hD₀.isPolyhedron.exists_simplicialComplex
  obtain ⟨B, hBfin, hBspace⟩ := hD₁.isPolyhedron.exists_simplicialComplex
  obtain ⟨P, hPfin, hPspace⟩ :=
    ((isPolyhedron_space K).union hD₀.isPolyhedron).exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  let _ : Finite P.faces := hPfin.to_subtype
  have hAχ := eulerChar_of_isPLBall A (hAspace.symm ▸ hD₀)
  have hBχ := eulerChar_of_isPLBall B (hBspace.symm ▸ hD₁)
  have hPχ := eulerChar_eq_add_of_space_union_of_isPLSphere_one P K A
    (by rw [hPspace, hAspace]) (by rw [hAspace, hmeet₀]; exact hJ₀)
  have hRχ := eulerChar_eq_add_of_space_union_of_isPLSphere_one R P B
    (by rw [hRspace, hPspace, hBspace]) (by rw [hPspace, hBspace, hinter]; exact hJ₁)
  exact ⟨R, hRfin, hR, hRc, by omega, hRspace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
