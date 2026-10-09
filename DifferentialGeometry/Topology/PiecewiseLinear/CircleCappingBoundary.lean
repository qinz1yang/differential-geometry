/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceSplit
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SurfacePartialCapping

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCircleCollar.subset_boundaryComplex [d : DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {G : Set E}
    (h : HasPLCircleCollar K.space G) : G ⊆ (boundaryComplex 2 K).space := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  obtain ⟨W, ρ, hρ, hρ0, hWK, hnear⟩ := h.2 univ isOpen_univ (subset_univ _)
  obtain ⟨A, hAfin, hA, -, hAspace, hAb⟩ := hρ.exists_annulus_complex h.1 zero_lt_one
  let _ : Finite A.faces := hAfin.to_subtype
  have hAK : A.space ⊆ K.space := hAspace.subset.trans (hWK.trans inter_subset_left)
  intro x hx
  have hxAb : x ∈ (boundaryComplex 2 A).space := by
    rw [hAb]
    exact ⟨(x, 0), ⟨hx, Or.inl rfl⟩, hρ0 x hx⟩
  have hAnear : A.space ∈ 𝓝[K.space] x := by
    rw [hAspace]
    obtain ⟨O, hO, hGO, hOW⟩ := mem_nhdsSetWithin.mp hnear
    exact mem_nhdsWithin.mpr ⟨O, hO, hGO hx, hOW⟩
  exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K A hK hA hAK
    (boundaryComplex_space_subset 2 A hxAb) hAnear).mp hxAb

end General

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCircleCapping.exists_boundary_preserving_map [d : DecidableEq E3]
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {T : Set E3}
    (hcap : IsCircleCapping K.space Q.space T (boundaryComplex 2 K).space) :
    ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3) (f : E3 → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T ∧
      K.space ∩ Δ = r '' stdSimplexBoundary 2 ∧
      r '' stdSimplexBoundary 2 ∈ traceCircles K.space T ∧
      r '' stdSimplexBoundary 2 ⊆ (boundaryComplex 2 K).space ∧
      IsPLHomeomorphOn f (K.space ∪ Δ) Q.space ∧
      EqOn f id ((boundaryComplex 2 K).space \ r '' stdSimplexBoundary 2) ∧
      (boundaryComplex 2 Q).space = (boundaryComplex 2 K).space \ r '' stdSimplexBoundary 2 := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨Δ, r, f, hr, hΔT, hmeet, hG, hcollar, hf, hfix⟩ := hcap
  obtain ⟨A, hAfin, hA, hAspace, hAb⟩ :=
    hK.exists_surface_union_disk_of_circle_collar K hr hmeet hcollar
  let _ : Finite A.faces := hAfin.to_subtype
  have hfA : IsPLHomeomorphOn f A.space Q.space := by rw [hAspace]; exact hf
  refine ⟨Δ, r, f, hr, hΔT, hmeet, hG, hcollar.subset_boundaryComplex K hK, hf, hfix, ?_⟩
  rw [boundaryComplex_space_of_isPLHomeomorphOn A Q hA hfA, hAb]
  simpa only [image_id] using hfix.image_eq

end DifferentialGeometry.Topology.PiecewiseLinear
