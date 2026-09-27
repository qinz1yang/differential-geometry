/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.PLBoundaryLift
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSimplexBoundaryNeighborhood

open Set Topology

private noncomputable local instance euclideanDecidableEq (N : ℕ) :
    DecidableEq (EuclideanSpace ℝ (Fin N)) := Classical.decEq _

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {X : Type*} [TopologicalSpace X]

open Classical in
theorem exists_simplicialMap_lift_derivedNeighborhood
    (K : Geometry.SimplicialComplex ℝ E) (p : X → K.space)
    [Finite K.faces] [Finite (coveringVertex K p)]
    {n m : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (D : Geometry.SimplicialComplex ℝ F) [Finite D.faces] (hD : IsPLBall (m + 1) D.space)
    (φ : F → E) (hφ : ∀ s ∈ D.faces, s.image φ ∈ K.faces)
    (hboundary : D.space ∩ simplicialMap D φ ⁻¹' (boundaryComplex (n + 1) K).space =
      (boundaryComplex (m + 1) D).space)
    (hp : IsCoveringMap p) (x₀ : D.space) (e₀ : X)
    (h₀ : p e₀ = ⟨simplicialMap D φ x₀, simplicialMap_mapsTo D K φ hφ x₀.2⟩)
    {V : Set E} (hV : V ∈ 𝓝ˢ[(boundaryComplex (n + 1) K).space]
      (simplicialMap D φ '' (boundaryComplex (m + 1) D).space)) :
    ∃ (ψ : F → EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))
      (hψ : ∀ s ∈ D.faces, s.image ψ ∈ (coveringComplex K p).faces)
      (A C : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))))
      (T : DerivedNeighborhoodTriangulation (coveringComplex K p) A),
      A.faces ⊆ (coveringComplex K p).faces ∧ C.faces ⊆ A.faces ∧
      (∀ s ∈ D.faces, s.image ψ ∈ A.faces) ∧
      A.space = simplicialMap D ψ '' D.space ∧
      C.space = simplicialMap D ψ '' (boundaryComplex (m + 1) D).space ∧
      IsCombinatorialManifoldWithBoundary (n + 1) T.complex ∧
      C.faces ⊆ (boundaryComplex (n + 1) T.complex).faces ∧
      A.space ∩ (boundaryComplex (n + 1) T.complex).space = C.space ∧
      D.space ∩ simplicialMap D ψ ⁻¹' (boundaryComplex (n + 1) T.complex).space =
        (boundaryComplex (m + 1) D).space ∧
      MapsTo (coveringBaseMap K p)
        (derivedNeighborhood (boundaryComplex (n + 1) T.complex) C).space V ∧
      EqOn (coveringBaseMap K p ∘ simplicialMap D ψ) (simplicialMap D φ) D.space ∧
      coveringSpaceHomeomorph K p hp
        ⟨simplicialMap D ψ x₀, simplicialMap_mapsTo D (coveringComplex K p) ψ hψ x₀.2⟩ = e₀ := by
  obtain ⟨ψ, hψ, A, C, -, -, hAL, hCA, -, hfaces, hAspace, hCspace,
    htrace, hproper, hproj, hanchor⟩ :=
    exists_simplicialMap_lift_image_subcomplexes K p hK D hD φ hφ hboundary hp x₀ e₀ h₀
  let L := coveringComplex K p
  let q := coveringBaseMap K p
  let _ : Finite L.faces := (coveringComplex_faces_finite K p).to_subtype
  have hL := isCombinatorialManifoldWithBoundary_coveringComplex K p hp hK
  have hq := isPiecewiseAffineOn_coveringBaseMap K p
  have hpre := hq.preimage_boundaryComplex_eq_of_isCoveringMap L K hL hK
    (coveringBaseMap_mapsTo K p) (isCoveringMap_coveringBaseMap_restrict K p hp)
  have hVlift := hq.continuousOn.preimage_mem_nhdsSetWithin hV
  rw [hpre] at hVlift
  have hCsub : C.space ⊆ L.space ∩ q ⁻¹'
      (simplicialMap D φ '' (boundaryComplex (m + 1) D).space) := by
    rw [hCspace]
    rintro y ⟨x, hx, rfl⟩
    have hxD := boundaryComplex_space_subset (m + 1) D hx
    exact ⟨simplicialMap_mapsTo D L ψ hψ hxD, x, hx, (hproj hxD).symm⟩
  have hVC : q ⁻¹' V ∈ 𝓝ˢ[(boundaryComplex (n + 1) L).space] C.space :=
    nhdsSetWithin_mono_left hCsub hVlift
  obtain ⟨T, hCT, hsmall⟩ := hL.exists_derivedNeighborhoodTriangulation_boundary_mem
    L A C hAL hCA htrace hVC
  have htraceT : A.space ∩ (boundaryComplex (n + 1) T.complex).space = C.space :=
    (T.inter_boundaryComplex_space hL hAL).trans htrace
  have hproperT : D.space ∩ simplicialMap D ψ ⁻¹' (boundaryComplex (n + 1) T.complex).space =
      (boundaryComplex (m + 1) D).space := by
    rw [← hproper]
    ext x
    apply and_congr_right
    intro hx
    exact T.mem_boundaryComplex_iff hL hAL (hAspace.symm ▸ mem_image_of_mem _ hx)
  exact ⟨ψ, hψ, A, C, T, hAL, hCA, hfaces, hAspace, hCspace,
    T.isCombinatorialManifoldWithBoundary hL, hCT, htraceT, hproperT,
    fun _ hx => (hsmall hx).2, hproj, hanchor⟩

end DifferentialGeometry.Topology.PiecewiseLinear
