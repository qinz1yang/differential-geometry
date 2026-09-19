/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceBoundaryCapping
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusEuler
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanSurfaceOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceHomology

/-!
# Betti descent by capping a connected annulus complement
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsCombinatorialManifold.exists_capped_annulus_complement
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifold 2 K) (hKc : IsConnected K.space)
    (hdim : Module.finrank ℝ E = 3)
    (hR : IsCombinatorialManifoldWithBoundary 2 R) (hRc : IsConnected R.space)
    {J : Set F} (hJ : IsPLSphere 1 J) {a b : ℝ} (hab : a < b)
    {W : Set E} {ρ : F × ℝ → E} (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc a b) W)
    (hcover : W ∪ R.space = K.space) (htrace : W ∩ R.space = ρ '' (J ×ˢ {a, b}))
    (hboundary : (boundaryComplex 2 R).space = ρ '' (J ×ˢ {a, b}))
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (stdSimplex ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hmeet₀ : R.space ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : R.space ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hbd₀ : r₀ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {a}))
    (hbd₁ : r₁ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {b})) :
    ∃ (P : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite),
      letI := hPfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
      eulerChar P = eulerChar K + 2 ∧
      Homology.bettiOne P.space + 2 = Homology.bettiOne K.space ∧
      Homology.bettiOne P.space < Homology.bettiOne K.space ∧
      P.space = R.space ∪ D₀ ∪ D₁ := by
  have hW : IsPolyhedron W := hρ.image_eq ▸
    (hJ.isPolyhedron.prod (isPLBall_Icc hab).isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  obtain ⟨A, hAfin, hAspace⟩ := hW.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hRχ : eulerChar R = eulerChar K :=
    eulerChar_eq_of_annulus_complement K A R hJ hab (hAspace.symm ▸ hρ)
      (by rwa [hAspace]) (by rwa [hAspace])
  have hRbd : (boundaryComplex 2 R).space =
      r₀ '' stdSimplexBoundary 2 ∪ r₁ '' stdSimplexBoundary 2 := by
    rw [hboundary, hbd₀, hbd₁, ← image_union, ← prod_union, singleton_union]
  obtain ⟨P, hPfin, hP, hPc, hPχ, hPspace⟩ :=
    hR.exists_closed_of_disk_pair R hRc hr₀ hr₁ hdis hmeet₀ hmeet₁ hRbd
  let _ : Finite P.faces := hPfin.to_subtype
  have hPo := hP.isOrientable_of_finrank_eq_three P hdim hPc
  have hKo := hK.isOrientable_of_finrank_eq_three K hdim hKc
  have hχK := hK.eulerChar_eq_two_sub_bettiOne_of_isOrientable K hKc hKo
  have hχP := hP.eulerChar_eq_two_sub_bettiOne_of_isOrientable P hPc hPo
  exact ⟨P, hPfin, hP, hPc, hPo, by omega, by omega, by omega, hPspace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
