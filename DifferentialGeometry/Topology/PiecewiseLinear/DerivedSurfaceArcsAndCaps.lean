/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedSurfaceBoundaryFaces
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCapTrace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_derived_surface_arcs_and_caps
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : IsCombinatorialManifold 3 R) (hΓR : Γ.faces ⊆ R.faces)
    {s : Finset E} (hs : s ∈ Γ.faces)
    {ψ : (ℝ × ℝ) × ℝ → E} {V : Set ((ℝ × ℝ) × ℝ)} {Ω W : Set E}
    (hψ : IsPLHomeomorphOn ψ V (R.space ∩ Ω)) (hWΩ : W ⊆ Ω)
    (hΓ : ∀ p ∈ V, ψ p ∈ Γ.space ↔ p.1 = 0)
    {P : Fin 4 → Set E} {q : Fin 4 → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P i))
    (hPR : ∀ i, (PiecewiseLinear.restrict R (P i)).space = P i)
    (hread : ∀ x ∈ R.space ∩ W, ∀ i,
      x ∈ P i ↔ Function.invFunOn ψ V x ∈ crossHalfPlane i)
    (hbd : ∀ x ∈ R.space ∩ W, ∀ i, x ∈ q i '' stdSimplexBoundary 2 ↔ x ∈ Γ.space)
    (hstar : (⋃ v ∈ s, closedStar R v) ⊆ W)
    (hcell : (derivedNeighborhoodCell R s).space ⊆ W) {y₀ y₁ : E}
    (hpoles : Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y₀, y₁}) :
    ∃ γ : Fin 4 → ℝ → E,
      (∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1)
        ((derivedNeighborhoodCellBase R s).space ∩ P i)) ∧
      (∀ i, γ i 0 = y₀) ∧ (∀ i, γ i 1 = y₁) ∧
      (∀ i j, i ≠ j →
        ((derivedNeighborhoodCellBase R s).space ∩ P i) ∩
          ((derivedNeighborhoodCellBase R s).space ∩ P j) = {y₀, y₁}) ∧
      (∀ i : Fin 4,
        ∀ U ⊆ (derivedNeighborhoodCellBase R s).space \
          (((derivedNeighborhoodCellBase R s).space ∩ P i) ∪
            ((derivedNeighborhoodCellBase R s).space ∩ P (i + 2))),
          IsPreconnected U →
          (U ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 1))).Nonempty →
          (U ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 3))).Nonempty → False) ∧
      ∀ t ∈ Γ.faces, s ≠ t → (s ⊆ t ∨ t ⊆ s) →
        ∀ r : (Fin 3 → ℝ) → E,
          IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
            ((derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space) →
          ∀ i : Fin 4, ∃ x : E,
            r '' stdSimplexBoundary 2 ∩
              ((derivedNeighborhoodCellBase R s).space ∩ P i) = {x} ∧
            ((derivedNeighborhoodCellBase R s).space ∩ P i) ∩
              ((derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space) =
                segment ℝ (({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id) x ∧
            ({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id ≠ x := by
  obtain ⟨γ, hγ, hγ0, hγ1, hTT, hsep⟩ := exists_fourArcTrace_of_crossHalfPlane_disks R Γ
    hΓR hs hψ hWΩ hΓ hq hPR hread hbd hcell hpoles
  refine ⟨γ, hγ, hγ0, hγ1, hTT, hsep, ?_⟩
  intro t ht hne hcomp r hr i
  let A := PiecewiseLinear.restrict R (P i)
  let _ : Finite A.faces := (restrict_faces_finite R _).to_subtype
  have hA : IsCombinatorialManifoldWithBoundary 2 A :=
    (show IsPLBall 2 A.space from (hPR i).symm ▸ ⟨q i, hq i⟩).isCombinatorialManifoldWithBoundary
  have hsA : s ∈ (boundaryComplex 2 A).faces :=
    mem_boundaryComplex_of_comparable_face_of_local_reading R Γ hΓR hs hs (Or.inl subset_rfl)
      (hq i) (hPR i) (fun x hx => hbd x hx i) hstar
  have htA : t ∈ (boundaryComplex 2 A).faces :=
    mem_boundaryComplex_of_comparable_face_of_local_reading R Γ hΓR hs ht hcomp
      (hq i) (hPR i) (fun x hx => hbd x hx i) hstar
  obtain ⟨x, hx⟩ := exists_derived_cap_surface_segment R A hR hA (restrict_faces_subset R _)
    hsA htA hne hcomp hr
  rw [show A.space = P i from hPR i] at hx
  exact ⟨x, hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
