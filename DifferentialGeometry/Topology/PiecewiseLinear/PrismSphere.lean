/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.isPLSphere_prism_boundary {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) {a b : ℝ} (hab : a < b) :
    IsPLSphere 2 (D ×ˢ {a, b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b) := by
  classical
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨K, hKfin, hKspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKspace.symm ▸ hD
  have hrK : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) K.space := hKspace.symm ▸ hr
  have hboundary : (boundaryComplex 2 K).space = r '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hrK,
      simplexBoundary_stdVertices_space]
  have hprism := isPLBall_three_prod hK (isPLBall_Icc hab)
  obtain ⟨R, hRfin, hRspace⟩ := hprism.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have h := isPLSphere_boundaryComplex_space_of_isPLBall R (hRspace.symm ▸ hprism)
  rwa [boundaryComplex_space_prism K hK hab R hRspace, hKspace, hboundary] at h

end DifferentialGeometry.Topology.PiecewiseLinear
