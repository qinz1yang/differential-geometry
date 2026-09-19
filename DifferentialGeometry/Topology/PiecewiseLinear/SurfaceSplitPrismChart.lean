/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitBallPair
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitBoundaryTrace
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitCenteredPrism

/-! Centered prism charts produced by the derived-neighborhood splitting disk. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsPLBall.exists_complex_pair_with_centered_prism_and_boundary_of_boundary_trace
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {D : Set E} {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (htrace : D ∩ (boundaryComplex 3 K).space = g '' stdSimplexBoundary 2) :
    ∃ (K₀ K₁ : Geometry.SimplicialComplex ℝ E) (ρ : (Fin 3 → ℝ) × ℝ → E),
      K₀.faces.Finite ∧ K₁.faces.Finite ∧ IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
      K₀.space ∪ K₁.space = K.space ∧ K₀.space ∩ K₁.space = D ∧
      D ⊆ (boundaryComplex 3 K₀).space ∧ D ⊆ (boundaryComplex 3 K₁).space ∧
      IsPLHomeomorphOn ρ
        (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) K.space ∧
      (∀ x ∈ stdSimplex ℝ (Fin 3), ρ (x, 0) = g x) ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
       ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = K₁.space ∧
       K₀.space ∩ (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 K₀).space ∧
       K₁.space ∩ (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 K₁).space ∧
       (boundaryComplex 3 K₀).space =
         D ∪ (K₀.space ∩ (boundaryComplex 3 K).space) ∧
       (boundaryComplex 3 K₁).space =
         D ∪ (K₁.space ∩ (boundaryComplex 3 K).space) := by
  obtain ⟨K₀, K₁, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁,
      houter₀, houter₁, hboundary₀, hboundary₁⟩ :=
    hK.exists_complex_pair_union_eq_inter_eq_with_boundary_of_boundary_trace
      K hg hDK htrace
  let _ : Finite K₀.faces := hK₀fin.to_subtype
  let _ : Finite K₁.faces := hK₁fin.to_subtype
  obtain ⟨ρ, hρ, hρmid, hρ₀, hρ₁⟩ :=
    exists_isPLHomeomorphOn_centered_prism_of_boundary_disk_pair
      (isPLBall_stdSimplex 2) K₀ K₁ hK₀ hK₁ hD₀ hD₁ hinter hg
  rw [hcover] at hρ
  exact ⟨K₀, K₁, ρ, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁,
    hρ, hρmid, hρ₀, hρ₁, houter₀, houter₁, hboundary₀, hboundary₁⟩

open Classical in
theorem IsPLBall.exists_complex_pair_with_centered_prism_and_outer_boundary_of_boundary_trace
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {D : Set E} {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (htrace : D ∩ (boundaryComplex 3 K).space = g '' stdSimplexBoundary 2) :
    ∃ (K₀ K₁ : Geometry.SimplicialComplex ℝ E) (ρ : (Fin 3 → ℝ) × ℝ → E),
      K₀.faces.Finite ∧ K₁.faces.Finite ∧ IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
      K₀.space ∪ K₁.space = K.space ∧ K₀.space ∩ K₁.space = D ∧
      D ⊆ (boundaryComplex 3 K₀).space ∧ D ⊆ (boundaryComplex 3 K₁).space ∧
      IsPLHomeomorphOn ρ
        (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) K.space ∧
      (∀ x ∈ stdSimplex ℝ (Fin 3), ρ (x, 0) = g x) ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = K₁.space ∧
      K₀.space ∩ (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 K₀).space ∧
      K₁.space ∩ (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 K₁).space := by
  obtain ⟨K₀, K₁, ρ, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁,
      hρ, hρmid, hρ₀, hρ₁, houter₀, houter₁, -, -⟩ :=
    hK.exists_complex_pair_with_centered_prism_and_boundary_of_boundary_trace
      K hg hDK htrace
  exact ⟨K₀, K₁, ρ, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁,
    hρ, hρmid, hρ₀, hρ₁, houter₀, houter₁⟩

open Classical in
theorem IsPLBall.exists_complex_pair_with_centered_prism_of_boundary_trace
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {D : Set E} {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (htrace : D ∩ (boundaryComplex 3 K).space = g '' stdSimplexBoundary 2) :
    ∃ (K₀ K₁ : Geometry.SimplicialComplex ℝ E) (ρ : (Fin 3 → ℝ) × ℝ → E),
      K₀.faces.Finite ∧ K₁.faces.Finite ∧ IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
      K₀.space ∪ K₁.space = K.space ∧ K₀.space ∩ K₁.space = D ∧
      D ⊆ (boundaryComplex 3 K₀).space ∧ D ⊆ (boundaryComplex 3 K₁).space ∧
      IsPLHomeomorphOn ρ
        (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) K.space ∧
      (∀ x ∈ stdSimplex ℝ (Fin 3), ρ (x, 0) = g x) ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = K₁.space := by
  obtain ⟨K₀, K₁, ρ, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁,
      hρ, hρmid, hρ₀, hρ₁, -, -⟩ :=
    hK.exists_complex_pair_with_centered_prism_and_outer_boundary_of_boundary_trace
      K hg hDK htrace
  exact ⟨K₀, K₁, ρ, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁,
    hρ, hρmid, hρ₀, hρ₁⟩

namespace IsCombinatorialManifoldWithBoundary

open Classical in
theorem exists_isSubdivision_disk_pair_with_centered_prism_and_boundary
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {Δ D₁ D₂ U : Set E}
    (hΔ : IsPLBall 2 Δ) (hD₁ : IsPLBall 2 D₁)
    {r₂ : (Fin 3 → ℝ) → E}
    (hr₂ : IsPLHomeomorphOn r₂ (stdSimplex ℝ (Fin 3)) D₂)
    (hΔintD₂ : Δ ⊆ r₂ '' openSimplex (stdVertices 1))
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] Δ)
    (hUdis : Disjoint U (boundaryComplex 3 K).space) :
    ∃ (R A A₁ A₂ K₀ K₁ : Geometry.SimplicialComplex ℝ E)
      (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (φ : E → EuclideanSpace ℝ (Fin 2)) (ψ : EuclideanSpace ℝ (Fin 2) → E)
      (g : (Fin 3 → ℝ) → E) (ρ : (Fin 3 → ℝ) × ℝ → E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ A.faces.Finite ∧ A.space = Δ ∧
      A₁.faces ⊆ R.faces ∧ A₁.faces.Finite ∧ A₁.space = D₁ ∧
      A₂.faces ⊆ R.faces ∧ A₂.faces.Finite ∧ A₂.space = D₂ ∧
      A.faces ⊆ A₁.faces ∧ A.faces ⊆ A₂.faces ∧ A₁.space ∩ A₂.space = A.space ∧
      L.faces.Finite ∧ IsPLBall 2 L.space ∧ IsGlueIso A L φ ψ ∧
      IsPLBall 3 (PiecewiseLinear.derivedNeighborhood R A).space ∧
      Δ ⊆ (PiecewiseLinear.derivedNeighborhood R A).space ∧
      (PiecewiseLinear.derivedNeighborhood R A).space ⊆ K.space ∧
      (PiecewiseLinear.derivedNeighborhood R A).space ⊆ U ∧
      (∀ x ∈ Δ, (PiecewiseLinear.derivedNeighborhood R A).space ∈ 𝓝[K.space] x) ∧
      IsPLBall 2 (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∧
      (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∩
          (boundaryComplex 3 (PiecewiseLinear.derivedNeighborhood R A)).space =
        (boundaryComplex 2 (PiecewiseLinear.derivedNeighborhood A₂ A)).space ∧
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3))
        (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∧
      g '' stdSimplexBoundary 2 =
        (boundaryComplex 2 (PiecewiseLinear.derivedNeighborhood A₂ A)).space ∧
      K₀.faces.Finite ∧ K₁.faces.Finite ∧
      IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
      K₀.space ∪ K₁.space = (PiecewiseLinear.derivedNeighborhood R A).space ∧
      K₀.space ∩ K₁.space = D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space ∧
      D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space ⊆
        (boundaryComplex 3 K₀).space ∧
      D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space ⊆
        (boundaryComplex 3 K₁).space ∧
      IsPLHomeomorphOn ρ
        (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1)
          (PiecewiseLinear.derivedNeighborhood R A).space ∧
      (∀ x ∈ stdSimplex ℝ (Fin 3), ρ (x, 0) = g x) ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = K₁.space ∧
      K₀.space ∩
          (boundaryComplex 3 (PiecewiseLinear.derivedNeighborhood R A)).space ⊆
        (boundaryComplex 3 K₀).space ∧
      K₁.space ∩
          (boundaryComplex 3 (PiecewiseLinear.derivedNeighborhood R A)).space ⊆
        (boundaryComplex 3 K₁).space ∧
      (boundaryComplex 3 K₀).space =
        (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∪
          (K₀.space ∩
            (boundaryComplex 3 (PiecewiseLinear.derivedNeighborhood R A)).space) ∧
      (boundaryComplex 3 K₁).space =
        (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∪
          (K₁.space ∩
            (boundaryComplex 3 (PiecewiseLinear.derivedNeighborhood R A)).space) := by
  obtain ⟨R, A, A₁, A₂, L, φ, ψ, hR, hRfin, hAR, hAfin, hAΔ,
      hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
      hLfin, hL, hIso, hN, hΔN, hNK, hNU, hnhds, hB, htrace⟩ :=
    hK.exists_isSubdivision_disk_pair_with_derivedNeighborhood_boundary_trace
      hΔ hD₁ hr₂ hΔintD₂ hΔD₁ hΔD₂ hD₁D₂ hD₁K hD₂K hU hUdis
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite A₂.faces := hA₂fin.to_subtype
  let N := PiecewiseLinear.derivedNeighborhood R A
  let Q := PiecewiseLinear.derivedNeighborhood A₂ A
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite R A).to_subtype
  let _ : Finite Q.faces := (derivedNeighborhood_faces_finite A₂ A).to_subtype
  have hmiddle : D₂ ∩ N.space = Q.space := by
    rw [← hA₂D₂, inter_comm]
    exact derivedNeighborhood_space_inter_subcomplex R A₂ A hA₂R
  obtain ⟨g, hg⟩ := id hB
  have hgboundary : g '' stdSimplexBoundary 2 = (boundaryComplex 2 Q).space :=
    hg.image_stdSimplexBoundary_eq_boundaryComplex Q hmiddle.symm
  have htraceg : (D₂ ∩ N.space) ∩ (boundaryComplex 3 N).space =
      g '' stdSimplexBoundary 2 := htrace.trans hgboundary.symm
  obtain ⟨K₀, K₁, ρ, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter,
      hmiddleK₀, hmiddleK₁,
      hρ, hρmid, hρ₀, hρ₁, houterK₀, houterK₁, hboundaryK₀, hboundaryK₁⟩ :=
    hN.exists_complex_pair_with_centered_prism_and_boundary_of_boundary_trace
      N hg inter_subset_right htraceg
  exact ⟨R, A, A₁, A₂, K₀, K₁, L, φ, ψ, g, ρ, hR, hRfin, hAR, hAfin, hAΔ,
    hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
    hLfin, hL, hIso, hN, hΔN, hNK, hNU, hnhds, hB, htrace, hg, hgboundary,
    hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hmiddleK₀, hmiddleK₁,
    hρ, hρmid, hρ₀, hρ₁, houterK₀, houterK₁, hboundaryK₀, hboundaryK₁⟩

open Classical in
theorem exists_isSubdivision_disk_pair_with_centered_prism_and_outer_boundary
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {Δ D₁ D₂ U : Set E}
    (hΔ : IsPLBall 2 Δ) (hD₁ : IsPLBall 2 D₁)
    {r₂ : (Fin 3 → ℝ) → E}
    (hr₂ : IsPLHomeomorphOn r₂ (stdSimplex ℝ (Fin 3)) D₂)
    (hΔintD₂ : Δ ⊆ r₂ '' openSimplex (stdVertices 1))
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] Δ)
    (hUdis : Disjoint U (boundaryComplex 3 K).space) :
    ∃ (R A A₁ A₂ K₀ K₁ : Geometry.SimplicialComplex ℝ E)
      (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (φ : E → EuclideanSpace ℝ (Fin 2)) (ψ : EuclideanSpace ℝ (Fin 2) → E)
      (g : (Fin 3 → ℝ) → E) (ρ : (Fin 3 → ℝ) × ℝ → E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ A.faces.Finite ∧ A.space = Δ ∧
      A₁.faces ⊆ R.faces ∧ A₁.faces.Finite ∧ A₁.space = D₁ ∧
      A₂.faces ⊆ R.faces ∧ A₂.faces.Finite ∧ A₂.space = D₂ ∧
      A.faces ⊆ A₁.faces ∧ A.faces ⊆ A₂.faces ∧ A₁.space ∩ A₂.space = A.space ∧
      L.faces.Finite ∧ IsPLBall 2 L.space ∧ IsGlueIso A L φ ψ ∧
      IsPLBall 3 (PiecewiseLinear.derivedNeighborhood R A).space ∧
      Δ ⊆ (PiecewiseLinear.derivedNeighborhood R A).space ∧
      (PiecewiseLinear.derivedNeighborhood R A).space ⊆ K.space ∧
      (PiecewiseLinear.derivedNeighborhood R A).space ⊆ U ∧
      (∀ x ∈ Δ, (PiecewiseLinear.derivedNeighborhood R A).space ∈ 𝓝[K.space] x) ∧
      IsPLBall 2 (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∧
      (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∩
          (boundaryComplex 3 (PiecewiseLinear.derivedNeighborhood R A)).space =
        (boundaryComplex 2 (PiecewiseLinear.derivedNeighborhood A₂ A)).space ∧
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3))
        (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∧
      g '' stdSimplexBoundary 2 =
        (boundaryComplex 2 (PiecewiseLinear.derivedNeighborhood A₂ A)).space ∧
      K₀.faces.Finite ∧ K₁.faces.Finite ∧
      IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
      K₀.space ∪ K₁.space = (PiecewiseLinear.derivedNeighborhood R A).space ∧
      K₀.space ∩ K₁.space = D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space ∧
      D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space ⊆
        (boundaryComplex 3 K₀).space ∧
      D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space ⊆
        (boundaryComplex 3 K₁).space ∧
      IsPLHomeomorphOn ρ
        (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1)
          (PiecewiseLinear.derivedNeighborhood R A).space ∧
      (∀ x ∈ stdSimplex ℝ (Fin 3), ρ (x, 0) = g x) ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = K₁.space ∧
      K₀.space ∩
          (boundaryComplex 3 (PiecewiseLinear.derivedNeighborhood R A)).space ⊆
        (boundaryComplex 3 K₀).space ∧
      K₁.space ∩
          (boundaryComplex 3 (PiecewiseLinear.derivedNeighborhood R A)).space ⊆
        (boundaryComplex 3 K₁).space := by
  obtain ⟨R, A, A₁, A₂, K₀, K₁, L, φ, ψ, g, ρ, hR, hRfin, hAR, hAfin, hAΔ,
      hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
      hLfin, hL, hIso, hN, hΔN, hNK, hNU, hnhds, hB, htrace, hg, hgboundary,
      hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hmiddleK₀, hmiddleK₁,
      hρ, hρmid, hρ₀, hρ₁, houterK₀, houterK₁, -, -⟩ :=
    hK.exists_isSubdivision_disk_pair_with_centered_prism_and_boundary
      hΔ hD₁ hr₂ hΔintD₂ hΔD₁ hΔD₂ hD₁D₂ hD₁K hD₂K hU hUdis
  exact ⟨R, A, A₁, A₂, K₀, K₁, L, φ, ψ, g, ρ, hR, hRfin, hAR, hAfin, hAΔ,
    hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
    hLfin, hL, hIso, hN, hΔN, hNK, hNU, hnhds, hB, htrace, hg, hgboundary,
    hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hmiddleK₀, hmiddleK₁,
    hρ, hρmid, hρ₀, hρ₁, houterK₀, houterK₁⟩

end IsCombinatorialManifoldWithBoundary

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isSubdivision_disk_pair_with_centered_prism
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {Δ D₁ D₂ U : Set E}
    (hΔ : IsPLBall 2 Δ) (hD₁ : IsPLBall 2 D₁)
    {r₂ : (Fin 3 → ℝ) → E}
    (hr₂ : IsPLHomeomorphOn r₂ (stdSimplex ℝ (Fin 3)) D₂)
    (hΔintD₂ : Δ ⊆ r₂ '' openSimplex (stdVertices 1))
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] Δ)
    (hUdis : Disjoint U (boundaryComplex 3 K).space) :
    ∃ (R A A₁ A₂ K₀ K₁ : Geometry.SimplicialComplex ℝ E)
      (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (φ : E → EuclideanSpace ℝ (Fin 2)) (ψ : EuclideanSpace ℝ (Fin 2) → E)
      (g : (Fin 3 → ℝ) → E) (ρ : (Fin 3 → ℝ) × ℝ → E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ A.faces.Finite ∧ A.space = Δ ∧
      A₁.faces ⊆ R.faces ∧ A₁.faces.Finite ∧ A₁.space = D₁ ∧
      A₂.faces ⊆ R.faces ∧ A₂.faces.Finite ∧ A₂.space = D₂ ∧
      A.faces ⊆ A₁.faces ∧ A.faces ⊆ A₂.faces ∧ A₁.space ∩ A₂.space = A.space ∧
      L.faces.Finite ∧ IsPLBall 2 L.space ∧ IsGlueIso A L φ ψ ∧
      IsPLBall 3 (PiecewiseLinear.derivedNeighborhood R A).space ∧
      Δ ⊆ (PiecewiseLinear.derivedNeighborhood R A).space ∧
      (PiecewiseLinear.derivedNeighborhood R A).space ⊆ K.space ∧
      (PiecewiseLinear.derivedNeighborhood R A).space ⊆ U ∧
      (∀ x ∈ Δ, (PiecewiseLinear.derivedNeighborhood R A).space ∈ 𝓝[K.space] x) ∧
      IsPLBall 2 (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∧
      (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∩
          (boundaryComplex 3 (PiecewiseLinear.derivedNeighborhood R A)).space =
        (boundaryComplex 2 (PiecewiseLinear.derivedNeighborhood A₂ A)).space ∧
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3))
        (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) ∧
      g '' stdSimplexBoundary 2 =
        (boundaryComplex 2 (PiecewiseLinear.derivedNeighborhood A₂ A)).space ∧
      K₀.faces.Finite ∧ K₁.faces.Finite ∧
      IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
      K₀.space ∪ K₁.space = (PiecewiseLinear.derivedNeighborhood R A).space ∧
      K₀.space ∩ K₁.space = D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space ∧
      D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space ⊆
        (boundaryComplex 3 K₀).space ∧
      D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space ⊆
        (boundaryComplex 3 K₁).space ∧
      IsPLHomeomorphOn ρ
        (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1)
          (PiecewiseLinear.derivedNeighborhood R A).space ∧
      (∀ x ∈ stdSimplex ℝ (Fin 3), ρ (x, 0) = g x) ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = K₁.space := by
  obtain ⟨R, A, A₁, A₂, K₀, K₁, L, φ, ψ, g, ρ, hR, hRfin, hAR, hAfin, hAΔ,
      hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
      hLfin, hL, hIso, hN, hΔN, hNK, hNU, hnhds, hB, htrace, hg, hgboundary,
      hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hmiddleK₀, hmiddleK₁,
      hρ, hρmid, hρ₀, hρ₁, -, -⟩ :=
    hK.exists_isSubdivision_disk_pair_with_centered_prism_and_outer_boundary
      hΔ hD₁ hr₂ hΔintD₂ hΔD₁ hΔD₂ hD₁D₂ hD₁K hD₂K hU hUdis
  exact ⟨R, A, A₁, A₂, K₀, K₁, L, φ, ψ, g, ρ, hR, hRfin, hAR, hAfin, hAΔ,
    hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
    hLfin, hL, hIso, hN, hΔN, hNK, hNU, hnhds, hB, htrace, hg, hgboundary,
    hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hmiddleK₀, hmiddleK₁,
    hρ, hρmid, hρ₀, hρ₁⟩

open Classical in
theorem IsCombinatorialManifold.exists_isSubdivision_disk_pair_with_centered_prism
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {Δ D₁ D₂ U : Set E}
    (hΔ : IsPLBall 2 Δ) (hD₁ : IsPLBall 2 D₁)
    {r₂ : (Fin 3 → ℝ) → E}
    (hr₂ : IsPLHomeomorphOn r₂ (stdSimplex ℝ (Fin 3)) D₂)
    (hΔintD₂ : Δ ⊆ r₂ '' openSimplex (stdVertices 1))
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] Δ) :
    ∃ (R A A₁ A₂ K₀ K₁ : Geometry.SimplicialComplex ℝ E)
      (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (φ : E → EuclideanSpace ℝ (Fin 2)) (ψ : EuclideanSpace ℝ (Fin 2) → E)
      (g : (Fin 3 → ℝ) → E) (ρ : (Fin 3 → ℝ) × ℝ → E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ A.faces.Finite ∧ A.space = Δ ∧
      A₁.faces ⊆ R.faces ∧ A₁.faces.Finite ∧ A₁.space = D₁ ∧
      A₂.faces ⊆ R.faces ∧ A₂.faces.Finite ∧ A₂.space = D₂ ∧
      A.faces ⊆ A₁.faces ∧ A.faces ⊆ A₂.faces ∧ A₁.space ∩ A₂.space = A.space ∧
      L.faces.Finite ∧ IsPLBall 2 L.space ∧ IsGlueIso A L φ ψ ∧
      IsPLBall 3 (derivedNeighborhood R A).space ∧
      Δ ⊆ (derivedNeighborhood R A).space ∧
      (derivedNeighborhood R A).space ⊆ K.space ∧
      (derivedNeighborhood R A).space ⊆ U ∧
      (∀ x ∈ Δ, (derivedNeighborhood R A).space ∈ 𝓝[K.space] x) ∧
      IsPLBall 2 (D₂ ∩ (derivedNeighborhood R A).space) ∧
      (D₂ ∩ (derivedNeighborhood R A).space) ∩
          (boundaryComplex 3 (derivedNeighborhood R A)).space =
        (boundaryComplex 2 (derivedNeighborhood A₂ A)).space ∧
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3))
        (D₂ ∩ (derivedNeighborhood R A).space) ∧
      g '' stdSimplexBoundary 2 =
        (boundaryComplex 2 (derivedNeighborhood A₂ A)).space ∧
      K₀.faces.Finite ∧ K₁.faces.Finite ∧
      IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
      K₀.space ∪ K₁.space = (derivedNeighborhood R A).space ∧
      K₀.space ∩ K₁.space = D₂ ∩ (derivedNeighborhood R A).space ∧
      D₂ ∩ (derivedNeighborhood R A).space ⊆ (boundaryComplex 3 K₀).space ∧
      D₂ ∩ (derivedNeighborhood R A).space ⊆ (boundaryComplex 3 K₁).space ∧
      IsPLHomeomorphOn ρ
        (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) (derivedNeighborhood R A).space ∧
      (∀ x ∈ stdSimplex ℝ (Fin 3), ρ (x, 0) = g x) ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
      ρ '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = K₁.space := by
  classical
  have hboundary : (boundaryComplex 3 K).space = ∅ := by
    change (⋃ t ∈ (boundaryComplex 3 K).faces, convexHull ℝ (t : Set E)) = ∅
    rw [hK.boundaryComplex_faces_eq_empty]
    simp
  have hUdis : Disjoint U (boundaryComplex 3 K).space := by
    rw [hboundary]
    exact disjoint_empty U
  have hKb : IsCombinatorialManifoldWithBoundary 3 K :=
    hK.isCombinatorialManifoldWithBoundary
  exact hKb.exists_isSubdivision_disk_pair_with_centered_prism hΔ hD₁ hr₂ hΔintD₂ hΔD₁
    hΔD₂ hD₁D₂ hD₁K hD₂K hU hUdis

end DifferentialGeometry.Topology.PiecewiseLinear
