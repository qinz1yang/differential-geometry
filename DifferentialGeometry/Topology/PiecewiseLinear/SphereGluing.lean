/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLSphere_union_of_isPLBall {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall n K.space) (hL : IsPLBall n L.space)
    (hboundaryK : K.space ∩ L.space = (boundaryComplex n K).space)
    (hboundaryL : K.space ∩ L.space = (boundaryComplex n L).space) :
    IsPLSphere n (K.space ∪ L.space) := by
  classical
  cases n with
  | zero =>
    obtain ⟨a, hKa⟩ := isPLBall_zero_iff.mp hK
    obtain ⟨b, hLb⟩ := isPLBall_zero_iff.mp hL
    refine isPLSphere_zero_iff.mpr ⟨a, b, ?_, ?_⟩
    · intro hab
      have ha : a ∈ (boundaryComplex 0 K).space := hboundaryK.subset
        ⟨by rw [hKa]; rfl, by rw [hLb, hab]; rfl⟩
      obtain ⟨s, ⟨-, t, ht, -, hcard, -⟩, -⟩ :=
        (boundaryComplex 0 K).mem_space_iff.mp ha
      have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht)
      omega
    · rw [hKa, hLb, singleton_union]
  | succ n =>
    have hboundary : IsPLHomeomorphOn (id : E → E)
        (boundaryComplex (n + 1) K).space (boundaryComplex (n + 1) L).space := by
      rw [← hboundaryK, ← hboundaryL]
      exact (hK.isPolyhedron.inter hL.isPolyhedron).isPLHomeomorphOn_id
    obtain ⟨f, hf, hfBoundary⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K L hK hL hboundary
    let R := boundaryRelSubdivision (n + 1) K
    let A := boundaryComplex (n + 1) K
    let _ : Finite R.faces := (boundaryRelSubdivision_faces_finite (n + 1) K).to_subtype
    let _ : Finite A.faces := (boundaryComplex_faces_finite (n + 1) K).to_subtype
    have hR : IsSubdivision R K := boundaryRelSubdivision_isSubdivision (n + 1) K
    have hAR : A.faces ⊆ R.faces := boundaryComplex_faces_subset_boundaryRelSubdivision (n + 1) K
    have hAK : A.faces ⊆ K.faces := boundaryComplex_faces_subset (n + 1) K
    have hfull : ∀ s ∈ R.faces, (∀ v ∈ s, {v} ∈ A.faces) → s ∈ A.faces :=
      boundaryComplex_full_boundaryRelSubdivision (n + 1) K
    have hid : IsPLHomeomorphOn (id : E → E) R.space K.space := by
      rw [hR.space_eq]
      exact hK.isPolyhedron.isPLHomeomorphOn_id
    have hcompat : ∀ x ∈ A.space, f (simplicialMap A id x) = id x := by
      intro x hx
      rw [simplicialMap_id_eq_of_mem A hx]
      exact hfBoundary hx
    have hoverlap : K.space ∩ L.space = id '' A.space := by
      rw [image_id]
      exact hboundaryK
    have hmap := isPLHomeomorphOn_gluedMap_of_full R K A A id id (isGlueIso_id A)
      hAR hAK hfull id f K.space L.space hid hf hcompat hoverlap
    exact (isPLSphere_double_of_isPLBall K hK).of_isPLHomeomorphOn hmap

end DifferentialGeometry.Topology.PiecewiseLinear
