/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDiskNeighborhood

/-! Compatible subdivisions and controlled derived neighborhoods for disk pairs. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isSubdivision_disk_pair_with_derivedNeighborhood
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {Δ D₁ D₂ U : Set E}
    (hΔ : IsPLBall 2 Δ) (hD₁ : IsPLBall 2 D₁) (hD₂ : IsPLBall 2 D₂)
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] Δ) :
    ∃ (R A A₁ A₂ : Geometry.SimplicialComplex ℝ E)
      (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (φ : E → EuclideanSpace ℝ (Fin 2)) (ψ : EuclideanSpace ℝ (Fin 2) → E),
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
      ∀ x ∈ Δ, (PiecewiseLinear.derivedNeighborhood R A).space ∈ 𝓝[K.space] x := by
  classical
  have hΔK : Δ ⊆ K.space := hΔD₁.trans hD₁K
  obtain ⟨O, hO, hΔO, hOU⟩ := mem_nhdsSetWithin.mp hU
  let Q : Option Bool → Set E
    | none => Δ
    | some false => D₁
    | some true => D₂
  have hQ : ∀ j, IsPolyhedron (Q j) := by
    intro j
    cases j with
    | none => exact hΔ.isPolyhedron
    | some j =>
      cases j with
      | false => simpa only [Q] using hD₁.isPolyhedron
      | true => simpa only [Q] using hD₂.isPolyhedron
  have hQK : ∀ j, Q j ⊆ K.space := by
    intro j
    cases j with
    | none => exact hΔK
    | some j => cases j <;> simp only [Q] <;> assumption
  let V : Bool → Set E
    | false => O
    | true => Δᶜ
  have hVo : ∀ i, IsOpen (((↑) : K.space → E) ⁻¹' V i) := by
    intro i
    cases i
    · exact hO.preimage continuous_subtype_val
    · exact hΔ.isPolyhedron.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hcover : K.space ⊆ ⋃ i, V i := by
    intro x _
    by_cases hx : x ∈ Δ
    · exact mem_iUnion.mpr ⟨false, hΔO hx⟩
    · exact mem_iUnion.mpr ⟨true, hx⟩
  obtain ⟨R₀, hR₀, hR₀fin, hQR₀, hstars₀⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_cover K Q hQ hQK V hVo hcover
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  have hΔR₀ : Δ ⊆ R₀.space := hΔK.trans hR₀.space_eq.symm.subset
  obtain ⟨R, A, L, φ, ψ, hR, hRfin, hAR, hAfin, hAΔ, hLfin, hL, hIso, -⟩ :=
    exists_isSubdivision_subcomplex_isGlueIso_planar R₀ hΔ hΔR₀
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let A₁ := restrict R D₁
  let A₂ := restrict R D₂
  have hD₁R₀ : (restrict R₀ D₁).space = D₁ := by
    simpa only [Q] using hQR₀ (some false)
  have hD₂R₀ : (restrict R₀ D₂).space = D₂ := by
    simpa only [Q] using hQR₀ (some true)
  have hsub₁ := hR.restrict (restrict R₀ D₁) (restrict_faces_subset R₀ D₁)
  have hsub₂ := hR.restrict (restrict R₀ D₂) (restrict_faces_subset R₀ D₂)
  rw [hD₁R₀] at hsub₁
  rw [hD₂R₀] at hsub₂
  have hA₁D₁ : A₁.space = D₁ := hsub₁.space_eq.trans hD₁R₀
  have hA₂D₂ : A₂.space = D₂ := hsub₂.space_eq.trans hD₂R₀
  have hA₁R : A₁.faces ⊆ R.faces := restrict_faces_subset R D₁
  have hA₂R : A₂.faces ⊆ R.faces := restrict_faces_subset R D₂
  have hA₁fin : A₁.faces.Finite := restrict_faces_finite R D₁
  have hA₂fin : A₂.faces.Finite := restrict_faces_finite R D₂
  have hAA₁ : A.faces ⊆ A₁.faces := by
    intro s hs
    exact ⟨hAR hs, fun x hx => hΔD₁ (hAΔ ▸ A.convexHull_subset_space hs hx)⟩
  have hAA₂ : A.faces ⊆ A₂.faces := by
    intro s hs
    exact ⟨hAR hs, fun x hx => hΔD₂ (hAΔ ▸ A.convexHull_subset_space hs hx)⟩
  have hmeet : A₁.space ∩ A₂.space = A.space := by
    rw [hA₁D₁, hA₂D₂, hD₁D₂, hAΔ]
  have hstarsR : ∀ s ∈ R.faces, ∃ i, (⋃ v ∈ s, closedStar R v) ⊆ V i :=
    hR.closedStars_subset_cover hstars₀
  have hstars₂ : ∀ s ∈ (PiecewiseLinear.secondDerived R).faces,
      ∃ i, (⋃ v ∈ s, closedStar (PiecewiseLinear.secondDerived R) v) ⊆ V i :=
    (secondDerived_isSubdivision R).closedStars_subset_cover hstarsR
  have hcellO (s : Finset E) (hs : s ∈ A.faces) :
      (derivedNeighborhoodCell R s).space ⊆ O := by
    have hsR := hAR hs
    have hc : {s.centroid ℝ id} ∈ (PiecewiseLinear.secondDerived R).faces :=
      (barycentricSubdivision_isSubdivision
        (PiecewiseLinear.barycentricSubdivision R)).singleton_mem
          (singleton_centroid_mem_barycentricSubdivision R hsR)
    obtain ⟨i, hi⟩ := hstars₂ _ hc
    have hi' : closedStar (PiecewiseLinear.secondDerived R) (s.centroid ℝ id) ⊆ V i := by
      simpa only [Finset.set_biUnion_singleton] using hi
    cases i
    · rwa [derivedNeighborhoodCell_space_eq_closedStar R hsR]
    · have hcentroidA : s.centroid ℝ id ∈ A.space :=
        A.convexHull_subset_space hs
          (s.centroid_mem_convexHull (A.nonempty_of_mem_faces hs))
      have hcentroidΔ : s.centroid ℝ id ∈ Δ := hAΔ ▸ hcentroidA
      have hcentroidNot : s.centroid ℝ id ∉ Δ := by
        simpa only [V, mem_compl_iff] using hi' (mem_closedStar_self _ hc)
      exact (hcentroidNot hcentroidΔ).elim
  have hNO : (PiecewiseLinear.derivedNeighborhood R A).space ⊆ O := by
    rw [← iUnion_derivedNeighborhoodCell_space R A hAR]
    exact iUnion₂_subset hcellO
  have hRK : IsSubdivision R K := hR.trans hR₀
  have hNK : (PiecewiseLinear.derivedNeighborhood R A).space ⊆ K.space :=
    (derivedNeighborhood_space_subset R A).trans hRK.space_eq.subset
  have hNU : (PiecewiseLinear.derivedNeighborhood R A).space ⊆ U := by
    intro x hx
    exact hOU ⟨hNO hx, hNK hx⟩
  have hball :=
    (hK.of_isSubdivision hRK).isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex
      hAR hL hIso
  have hcontains : A.space ⊆ (PiecewiseLinear.derivedNeighborhood R A).space := by
    rw [← iUnion_derivedNeighborhoodCell_space R A hAR]
    exact space_subset_iUnion_derivedNeighborhoodCell_space R A hAR
  refine ⟨R, A, A₁, A₂, L, φ, ψ, hRK, hRfin, hAR, hAfin, hAΔ,
    hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
    hLfin, hL, hIso, hball, hAΔ ▸ hcontains, hNK, hNU, ?_⟩
  intro x hxΔ
  have hxA : x ∈ A.space := hAΔ.symm ▸ hxΔ
  have hx := derivedNeighborhood_mem_nhdsWithin hAR hxA
  rwa [hRK.space_eq] at hx

end DifferentialGeometry.Topology.PiecewiseLinear
