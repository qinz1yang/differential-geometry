/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleSolidTorus

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsParametrizedSolidTorusTransport (g : E → F) (N : Set E) : Prop :=
  ∃ (P : Geometry.SimplicialComplex ℝ E) (P' : Geometry.SimplicialComplex ℝ F)
      (f : (Fin 3 → ℝ) × ℝ → E) (f' : (Fin 3 → ℝ) × ℝ → F),
    P.faces.Finite ∧ P'.faces.Finite ∧
    IsCombinatorialManifoldWithBoundary 3 P ∧
    IsCombinatorialManifoldWithBoundary 3 P' ∧
    P.space = N ∧ P'.space = g '' N ∧
    IsTopologicalSolidTorus N ∧ IsTopologicalSolidTorus (g '' N) ∧
    IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N ∧
    IsCylindricalDiagram f' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g '' N) ∧
    (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = f (x, 1)) ∧
    ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f' (x, 0) = f' (x, 1)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
open Classical in
theorem IsCommonAnnularDerivedNeighborhood.circle_subset_ambient
    {K : Geometry.SimplicialComplex ℝ E} {N J S₀ S₁ : Set E}
    (h : IsCommonAnnularDerivedNeighborhood K N J S₀ S₁) : J ⊆ K.space := by
  obtain ⟨R, L, P₀, -, -, -, -, -, hRK, hLspace, -, -, hP₀R, -, hLP₀, -⟩ := h
  rw [← hLspace, ← hRK.space_eq]
  exact space_mono_of_faces_subset (hLP₀.trans hP₀R)

open Classical in
theorem IsCommonAnnularDerivedNeighborhood.isParametrizedSolidTorusTransport
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {K : Geometry.SimplicialComplex ℝ E} {K' : Geometry.SimplicialComplex ℝ F}
    [Finite K.faces] [Finite K'.faces] {g : E → F}
    {N J S₀ S₁ : Set E} {J' S₀' S₁' : Set F}
    (h : IsCommonAnnularDerivedNeighborhood K N J S₀ S₁)
    (h' : IsCommonAnnularDerivedNeighborhood K' (g '' N) J' S₀' S₁')
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (horK : IsOrientable 3 K)
    (hK' : IsCombinatorialManifoldWithBoundary 3 K') (horK' : IsOrientable 3 K')
    (hJ : IsPLSphere 1 J) (hJ' : IsPLSphere 1 J') :
    IsParametrizedSolidTorusTransport g N := by
  obtain ⟨P, f, hPfin, hP, hPN, hsolid, hf, hends⟩ :=
    h.exists_solid_torus hK horK hJ
  obtain ⟨P', f', hP'fin, hP', hP'N, hsolid', hf', hends'⟩ :=
    h'.exists_solid_torus hK' horK' hJ'
  exact ⟨P, P', f, f', hPfin, hP'fin, hP, hP', hPN, hP'N,
    hsolid, hsolid', hf, hf', hends, hends'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
