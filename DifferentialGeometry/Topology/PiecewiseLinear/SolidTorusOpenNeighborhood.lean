/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.VertexCrossingLevel

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem IsCylindricalDiagram.affineEquiv_comp
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (h : IsCylindricalDiagram f P S) (A : F ≃ᵃ[ℝ] G) :
    IsCylindricalDiagram (A ∘ f) P (A '' S) where
  isPiecewiseAffineOn := by
    have hcomp := h.isPiecewiseAffineOn.affine_comp A.toAffineMap
    rw [A.coe_toAffineMap] at hcomp
    exact hcomp
  image_eq := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨f x, h.image_eq ▸ ⟨x, hx, rfl⟩, rfl⟩
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := h.image_eq.symm.subset hz
      exact ⟨x, hx, rfl⟩
  image_top_eq_bottom := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨z, hz, hzx⟩ := h.image_top_eq_bottom.subset ⟨x, hx, rfl⟩
      exact ⟨z, hz, congrArg A hzx⟩
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨z, hz, hzx⟩ := h.image_top_eq_bottom.symm.subset ⟨x, hx, rfl⟩
      exact ⟨z, hz, congrArg A hzx⟩
  eq_or_endpoints x hx y hy hxy :=
    h.eq_or_endpoints x hx y hy (A.injective hxy)

theorem IsTopologicalSolidTorus.affineEquiv_image [FiniteDimensional ℝ F]
    {S : Set F} (h : IsTopologicalSolidTorus S) (A : F ≃ᵃ[ℝ] G) :
    IsTopologicalSolidTorus (A '' S) := by
  obtain ⟨e⟩ := h
  exact ⟨((A.toContinuousAffineEquiv.toHomeomorph.image S).symm.trans e)⟩

open Classical in
theorem exists_parametrized_solid_torus_complex_subset_open
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    {U : Set E} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (N : Geometry.SimplicialComplex ℝ E) (f : (Fin 3 → ℝ) × ℝ → E),
      N.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 N ∧
      N.space ⊆ U ∧ (interior N.space).Nonempty ∧
      IsTopologicalSolidTorus N.space ∧
      IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N.space ∧
      ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = f (x, 1) := by
  obtain ⟨T, hT, hTcard, -⟩ :=
    exists_affineIndependent_openSimplex_superset 3 hdim
      (isCompact_singleton.isBounded : Bornology.IsBounded ({0} : Set E))
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  let Q := T.erase a
  have hQ : AffineIndependent ℝ ((↑) : Q → E) :=
    affineIndependent_of_subset hT (Finset.erase_subset a T)
  have hQcard : Q.card = 3 := by
    dsimp [Q]
    rw [Finset.card_erase_of_mem ha, hTcard]
  let J := (simplexBoundary Q hQ).space
  have hJ : IsPLSphere 1 J := by
    dsimp [J]
    rw [simplexBoundary_space Q hQ (by omega)]
    exact isPLSphere_biUnion_erase Q hQ (by omega)
  obtain ⟨N, f, hNfin, hNman, hJint, hNsolid, hf, hends⟩ :=
    hJ.exists_solid_torus_neighborhood hdim
  let _ : Finite N.faces := hNfin.to_subtype
  obtain ⟨j, hj⟩ := hJ.nonempty
  have hNne : N.space.Nonempty := ⟨j, interior_subset (hJint hj)⟩
  obtain ⟨p, hpU⟩ := hUne
  obtain ⟨ε, hε, hballU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  obtain ⟨R, hNR⟩ := (isPolyhedron_space N).isCompact.isBounded.subset_ball (0 : E)
  have hR : 0 < R := by
    obtain ⟨z, hz⟩ := hNne
    have hzR := hNR hz
    rw [mem_ball] at hzR
    exact lt_of_le_of_lt dist_nonneg hzR
  let r : ℝ := ε / (2 * R)
  have hr : 0 < r := div_pos hε (mul_pos (by norm_num) hR)
  let A : E ≃ᵃ[ℝ] E :=
    (LinearEquiv.smulOfNeZero ℝ E r hr.ne').toAffineEquiv.trans
      (AffineEquiv.constVAdd ℝ E p)
  have hA (x : E) : A x = p + r • x := by
    simp only [A, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv,
      LinearEquiv.smulOfNeZero_apply, AffineEquiv.constVAdd_apply, vadd_eq_add]
  let N' := affineImage N A
  let f' : (Fin 3 → ℝ) × ℝ → E := A ∘ f
  have hN'fin : N'.faces.Finite := affineImage_faces_finite N A
  let _ : Finite N'.faces := hN'fin.to_subtype
  have hN'space : N'.space = A '' N.space := affineImage_space N A
  have hN'U : N'.space ⊆ U := by
    rw [hN'space]
    rintro _ ⟨x, hxN, rfl⟩
    apply hballU
    have hxR := hNR hxN
    rw [mem_ball, dist_zero_right] at hxR
    have hrR : r * R = ε / 2 := by
      dsimp [r]
      field_simp
    have hnorm : r * ‖x‖ < ε := by
      calc
        r * ‖x‖ < r * R := mul_lt_mul_of_pos_left hxR hr
        _ = ε / 2 := hrR
        _ < ε := by linarith
    simpa only [mem_ball, hA, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le] using hnorm
  have hN'int : (interior N'.space).Nonempty := by
    refine ⟨A j, ?_⟩
    rw [hN'space]
    have himage : A '' interior N.space = interior (A '' N.space) := by
      have h := A.toContinuousAffineEquiv.toHomeomorph.image_interior N.space
      have hcoe : (A.toContinuousAffineEquiv.toHomeomorph : E → E) = A :=
        A.coe_toContinuousAffineEquiv
      rw [hcoe] at h
      exact h
    rw [← himage]
    exact mem_image_of_mem A (hJint hj)
  have hN'man : IsCombinatorialManifoldWithBoundary 3 N' :=
    hNman.of_isPLHomeomorphOn (isPLHomeomorphOn_affineImage N A)
  have hN'solid : IsTopologicalSolidTorus N'.space := by
    rw [hN'space]
    exact hNsolid.affineEquiv_image A
  have hf' : IsCylindricalDiagram f' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N'.space := by
    rw [hN'space]
    exact hf.affineEquiv_comp A
  have hends' : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f' (x, 0) = f' (x, 1) := by
    intro x hx
    exact congrArg A (hends x hx)
  exact ⟨N', f', hN'fin, hN'man, hN'U, hN'int, hN'solid, hf', hends'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
