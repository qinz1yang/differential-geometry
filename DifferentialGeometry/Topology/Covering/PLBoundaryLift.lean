/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.PLBoundary
import DifferentialGeometry.Topology.Covering.PLMapLift
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialImageIn

open Set Topology

private noncomputable local instance euclideanDecidableEq (N : ℕ) :
    DecidableEq (EuclideanSpace ℝ (Fin N)) := Classical.decEq _

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {X : Type*} [TopologicalSpace X]
  (K : Geometry.SimplicialComplex ℝ E) (p : X → K.space)
  [Finite K.faces] [Finite (coveringVertex K p)]

open Classical in
theorem exists_simplicialMap_lift_with_boundary
    {n m : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (D : Geometry.SimplicialComplex ℝ F) [Finite D.faces] (hD : IsPLBall (m + 1) D.space)
    (φ : F → E) (hφ : ∀ s ∈ D.faces, s.image φ ∈ K.faces)
    (hboundary : D.space ∩ simplicialMap D φ ⁻¹' (boundaryComplex (n + 1) K).space =
      (boundaryComplex (m + 1) D).space)
    (hp : IsCoveringMap p) (x₀ : D.space) (e₀ : X)
    (h₀ : p e₀ = ⟨simplicialMap D φ x₀, simplicialMap_mapsTo D K φ hφ x₀.2⟩) :
    ∃ (ψ : F → EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))
      (hψ : ∀ s ∈ D.faces, s.image ψ ∈ (coveringComplex K p).faces),
      EqOn (coveringBaseMap K p ∘ simplicialMap D ψ) (simplicialMap D φ) D.space ∧
      D.space ∩ simplicialMap D ψ ⁻¹' (boundaryComplex (n + 1) (coveringComplex K p)).space =
        (boundaryComplex (m + 1) D).space ∧
      coveringSpaceHomeomorph K p hp
        ⟨simplicialMap D ψ x₀, simplicialMap_mapsTo D (coveringComplex K p) ψ hψ x₀.2⟩ = e₀ := by
  obtain ⟨ψ, hψ₀, -, hproj, hanchor⟩ :=
    exists_simplicialMap_lift_of_isPLBall K p D hD φ hφ hp x₀ e₀ h₀
  have hψ : ∀ s ∈ D.faces, s.image ψ ∈ (coveringComplex K p).faces := by
    intro s hs
    convert hψ₀ s hs using 1
    exact congrArg (fun d : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) =>
      @Finset.image _ _ d ψ s) (Subsingleton.elim _ _)
  let L := coveringComplex K p
  let _ : Finite L.faces := (coveringComplex_faces_finite K p).to_subtype
  have hL := isCombinatorialManifoldWithBoundary_coveringComplex K p hp hK
  have hbd (x : F) (hx : x ∈ D.space) :
      simplicialMap D ψ x ∈ (boundaryComplex (n + 1) L).space ↔
        simplicialMap D φ x ∈ (boundaryComplex (n + 1) K).space := by
    have h := (isPiecewiseAffineOn_coveringBaseMap K p).mem_boundaryComplex_iff_of_isCoveringMap
      L K hL hK (coveringBaseMap_mapsTo K p) (isCoveringMap_coveringBaseMap_restrict K p hp)
      (simplicialMap_mapsTo D L ψ hψ hx)
    change coveringBaseMap K p (simplicialMap D ψ x) ∈ _ ↔ _ at h
    rw [show coveringBaseMap K p (simplicialMap D ψ x) = simplicialMap D φ x from hproj hx] at h
    exact h.symm
  refine ⟨ψ, hψ, hproj, ?_, hanchor⟩
  apply Subset.antisymm
  · rintro x ⟨hx, hxB⟩
    exact hboundary.subset ⟨hx, (hbd x hx).mp hxB⟩
  · intro x hx
    have hxD := boundaryComplex_space_subset (m + 1) D hx
    exact ⟨hxD, (hbd x hxD).mpr (hboundary.superset hx).2⟩

open Classical in
theorem exists_simplicialMap_lift_image_subcomplexes
    {n m : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (D : Geometry.SimplicialComplex ℝ F) [Finite D.faces] (hD : IsPLBall (m + 1) D.space)
    (φ : F → E) (hφ : ∀ s ∈ D.faces, s.image φ ∈ K.faces)
    (hboundary : D.space ∩ simplicialMap D φ ⁻¹' (boundaryComplex (n + 1) K).space =
      (boundaryComplex (m + 1) D).space)
    (hp : IsCoveringMap p) (x₀ : D.space) (e₀ : X)
    (h₀ : p e₀ = ⟨simplicialMap D φ x₀, simplicialMap_mapsTo D K φ hφ x₀.2⟩) :
    ∃ (ψ : F → EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))
      (hψ : ∀ s ∈ D.faces, s.image ψ ∈ (coveringComplex K p).faces)
      (A C : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))),
      A.faces.Finite ∧ C.faces.Finite ∧ A.faces ⊆ (coveringComplex K p).faces ∧
      C.faces ⊆ A.faces ∧ C.faces ⊆ (boundaryComplex (n + 1) (coveringComplex K p)).faces ∧
      (∀ s ∈ D.faces, s.image ψ ∈ A.faces) ∧
      A.space = simplicialMap D ψ '' D.space ∧
      C.space = simplicialMap D ψ '' (boundaryComplex (m + 1) D).space ∧
      A.space ∩ (boundaryComplex (n + 1) (coveringComplex K p)).space = C.space ∧
      D.space ∩ simplicialMap D ψ ⁻¹' (boundaryComplex (n + 1) (coveringComplex K p)).space =
        (boundaryComplex (m + 1) D).space ∧
      EqOn (coveringBaseMap K p ∘ simplicialMap D ψ) (simplicialMap D φ) D.space ∧
      coveringSpaceHomeomorph K p hp
        ⟨simplicialMap D ψ x₀, simplicialMap_mapsTo D (coveringComplex K p) ψ hψ x₀.2⟩ = e₀ := by
  obtain ⟨ψ, hψ, hproj, hproper, hanchor⟩ :=
    exists_simplicialMap_lift_with_boundary K p hK D hD φ hφ hboundary hp x₀ e₀ h₀
  let L := coveringComplex K p
  let B := boundaryComplex (m + 1) D
  let _ : Finite B.faces := (boundaryComplex_faces_finite (m + 1) D).to_subtype
  obtain ⟨A, hAfinite, hAL, hAfaces, hAspace⟩ :=
    exists_finite_subcomplex_space_eq_image_simplicialMap D L ψ hψ
  obtain ⟨C, hCfinite, hCL, hCfaces, hCspace⟩ :=
    exists_finite_subcomplex_space_eq_image_simplicialMap B L ψ
      (fun s hs => hψ s (boundaryComplex_faces_subset (m + 1) D hs))
  have hCA : C.faces ⊆ A.faces := by
    rw [hCfaces, hAfaces]
    rintro t ⟨s, hs, rfl⟩
    exact ⟨s, boundaryComplex_faces_subset (m + 1) D hs, rfl⟩
  have hCspace' : C.space = simplicialMap D ψ '' B.space :=
    hCspace.trans (simplicialMap_eqOn_of_faces_subset D B
      (boundaryComplex_faces_subset (m + 1) D) ψ).image_eq.symm
  have htrace : A.space ∩ (boundaryComplex (n + 1) L).space = C.space := by
    rw [hAspace, hCspace']
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, rfl⟩, hxB⟩
      exact ⟨x, hproper.subset ⟨hx, hxB⟩, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨⟨x, boundaryComplex_space_subset (m + 1) D hx, rfl⟩, (hproper.superset hx).2⟩
  have hCbd : C.faces ⊆ (boundaryComplex (n + 1) L).faces := by
    intro s hs
    have hcent := centroid_mem_openSimplex_of_mem_faces C s hs
    have hxC := C.convexHull_subset_space hs (openSimplex_subset_convexHull s hcent)
    exact mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset (n + 1) L)
      (hCL hs) hcent (htrace.superset hxC).2
  refine ⟨ψ, hψ, A, C, hAfinite, hCfinite, hAL, hCA, hCbd, ?_,
    hAspace, hCspace', htrace, hproper, hproj, hanchor⟩
  intro s hs
  rw [hAfaces]
  exact ⟨s, hs, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
