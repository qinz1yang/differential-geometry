/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcChainCells
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCone
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall

/-!
# An interior simplicial edge in a triangulated three-ball
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_simplicialArc_one_with_interior_edge [FiniteDimensional ℝ E]
    (hn : Module.finrank ℝ E = 3) :
    ∃ (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E), K.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 K ∧
      (∀ i ≤ 1, ({v i} : Finset E) ∈ K.faces) ∧
      (∀ i < 1, ({v i, v (i + 1)} : Finset E) ∈ K.faces) ∧
      (∀ i ≤ 1, ∀ j ≤ 1, v i = v j → i = j) ∧
      arcChainFace v 0 ∉ (boundaryComplex 3 K).faces ∧
      arcChainFace v 1 ∉ (boundaryComplex 3 K).faces := by
  obtain ⟨T, hT, hTcard, -, -, -⟩ :=
    exists_affineIndependent_openSimplex_subset (n := 2) hn (0 : E) Filter.univ_mem
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  let K₀ := simplexComplex T hT
  let K := barycentricSubdivision K₀
  let c := T.centroid ℝ id
  let v : ℕ → E := fun i => if i = 0 then c else a
  have hv0 : v 0 = c := by simp only [v, if_pos rfl]
  have hv1 : v 1 = a := by simp only [v, if_neg one_ne_zero]
  have hTne : T.Nonempty := ⟨a, ha⟩
  have hTface : T ∈ K₀.faces := (mem_simplexComplex_faces_iff T hT).mpr ⟨hTne, subset_rfl⟩
  have haface : ({a} : Finset E) ∈ K₀.faces :=
    (mem_simplexComplex_faces_iff T hT).mpr
      ⟨Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr ha⟩
  let _ : Finite K₀.faces := (simplexComplex_faces_finite T hT).to_subtype
  let _ : Finite K.faces := inferInstance
  have hK₀space : K₀.space = convexHull ℝ (T : Set E) := simplexComplex_space T hT hTne
  have hK₀ball : IsPLBall 3 K₀.space := by
    rw [hK₀space]
    exact isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hK₀man : IsCombinatorialManifoldWithBoundary 3 K₀ :=
    hK₀ball.isCombinatorialManifoldWithBoundary
  have hsub : IsSubdivision K K₀ := barycentricSubdivision_isSubdivision K₀
  have hKman : IsCombinatorialManifoldWithBoundary 3 K := hK₀man.of_isSubdivision hsub
  have hcface : ({c} : Finset E) ∈ K.faces :=
    singleton_centroid_mem_barycentricSubdivision K₀ hTface
  have hafaceK : ({a} : Finset E) ∈ K.faces := hsub.singleton_mem haface
  have hTneha : T ≠ {a} := by
    intro h
    rw [h, Finset.card_singleton] at hTcard
    omega
  have hca : c ≠ a := by
    have h := centroid_ne_centroid_of_ne K₀ hTface haface hTneha
    simpa only [Finset.centroid_singleton, id_eq] using h
  have hcape : ({c, a} : Finset E) ∈ K.faces := by
    have h := pair_centroid_mem_barycentricSubdivision_of_subset_or_subset
      K₀ hTface haface (Or.inr (Finset.singleton_subset_iff.mpr ha))
    simpa only [Finset.centroid_singleton, id_eq] using h
  have hcnot : ({c} : Finset E) ∉ (boundaryComplex 3 K).faces := by
    intro hcB
    have hcspace : c ∈ (boundaryComplex 3 K).space :=
      (boundaryComplex 3 K).subset_space hcB (Finset.mem_singleton_self c)
    rw [boundaryComplex_space_of_isSubdivision K₀ K hK₀man hsub,
      boundaryComplex_simplexComplex hT hTcard] at hcspace
    rw [simplexBoundary_space T hT (by omega)] at hcspace
    exact notMem_boundary_of_mem_openSimplex hT (centroid_mem_openSimplex hTne) hcspace
  have hcapenot : ({c, a} : Finset E) ∉ (boundaryComplex 3 K).faces := by
    intro h
    exact hcnot ((boundaryComplex 3 K).down_closed h
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self c {a}))
      (Finset.singleton_nonempty c))
  refine ⟨K, v, Set.toFinite K.faces, hKman, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · simpa only [hv0] using hcface
    · simpa only [hv1] using hafaceK
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa only [hv0, zero_add, hv1] using hcape
  · intro i hi j hj hij
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · rfl
    · exact (hca (by simpa only [hv0, hv1] using hij)).elim
    · exact (hca (by simpa only [hv0, hv1] using hij.symm)).elim
    · rfl
  · rw [show arcChainFace v 0 = {v 0} by simpa using arcChainFace_two_mul v 0]
    simpa only [hv0] using hcnot
  · rw [show 1 = 2 * 0 + 1 by omega, arcChainFace_two_mul_add_one]
    simpa only [hv0, zero_add, hv1] using hcapenot

open Classical in
theorem exists_simplicialArc_one_with_all_faces_interior [FiniteDimensional ℝ E]
    (hn : Module.finrank ℝ E = 3) :
    ∃ (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E), K.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 K ∧
      (∀ i ≤ 1, ({v i} : Finset E) ∈ K.faces) ∧
      (∀ i < 1, ({v i, v (i + 1)} : Finset E) ∈ K.faces) ∧
      (∀ i ≤ 1, ∀ j ≤ 1, v i = v j → i = j) ∧
      ∀ j ≤ 2, arcChainFace v j ∉ (boundaryComplex 3 K).faces := by
  obtain ⟨K₁, u, hfin₁, hK₁, hvert₁, hedge₁, hinj₁, hzeroB, honeB⟩ :=
    exists_simplicialArc_one_with_interior_edge hn
  let _ : Finite K₁.faces := hfin₁.to_subtype
  let s := arcChainFace u 0
  let t := arcChainFace u 1
  have hs : s ∈ K₁.faces := arcChainFace_mem_faces hvert₁ hedge₁ (j := 0) (by omega)
  have ht : t ∈ K₁.faces := arcChainFace_mem_faces hvert₁ hedge₁ (j := 1) (by omega)
  have hst : s ⊆ t ∨ t ⊆ s :=
    (arcChainFace_comparable_iff hinj₁ (i := 0) (j := 1) (by omega) (by omega)).mpr
      (by omega)
  have hstne : s ≠ t := by
    intro h
    have := arcChainFace_injective hinj₁ (i := 0) (j := 1) (by omega) (by omega) h
    omega
  let K := barycentricSubdivision K₁
  let p := s.centroid ℝ id
  let q := t.centroid ℝ id
  let v : ℕ → E := fun i => if i = 0 then p else q
  let _ : Finite K.faces := inferInstance
  have hsub : IsSubdivision K K₁ := barycentricSubdivision_isSubdivision K₁
  have hK : IsCombinatorialManifoldWithBoundary 3 K := hK₁.of_isSubdivision hsub
  have hp : ({p} : Finset E) ∈ K.faces :=
    singleton_centroid_mem_barycentricSubdivision K₁ hs
  have hq : ({q} : Finset E) ∈ K.faces :=
    singleton_centroid_mem_barycentricSubdivision K₁ ht
  have hpq : ({p, q} : Finset E) ∈ K.faces :=
    pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K₁ hs ht hst
  have hpqne : p ≠ q := centroid_ne_centroid_of_ne K₁ hs ht hstne
  have hcentroidInterior : ∀ {r : Finset E}, r ∈ K₁.faces →
      r ∉ (boundaryComplex 3 K₁).faces →
      ({r.centroid ℝ id} : Finset E) ∉ (boundaryComplex 3 K).faces := by
    intro r hr hrB hcentroidB
    have hspace : r.centroid ℝ id ∈ (boundaryComplex 3 K).space :=
      (boundaryComplex 3 K).subset_space hcentroidB (Finset.mem_singleton_self _)
    rw [boundaryComplex_space_of_isSubdivision K₁ K hK₁ hsub] at hspace
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 3 K₁) hr hrB
      (centroid_mem_openSimplex_of_mem_faces K₁ r hr) hspace
  have hpB : ({p} : Finset E) ∉ (boundaryComplex 3 K).faces :=
    hcentroidInterior hs hzeroB
  have hqB : ({q} : Finset E) ∉ (boundaryComplex 3 K).faces :=
    hcentroidInterior ht honeB
  have hpqB : ({p, q} : Finset E) ∉ (boundaryComplex 3 K).faces := by
    intro h
    exact hpB ((boundaryComplex 3 K).down_closed h
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self p {q}))
      (Finset.singleton_nonempty p))
  have hv0 : v 0 = p := by simp only [v, if_pos rfl]
  have hv1 : v 1 = q := by simp only [v, if_neg one_ne_zero]
  refine ⟨K, v, Set.toFinite K.faces, hK, ?_, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · simpa only [hv0] using hp
    · simpa only [hv1] using hq
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa only [hv0, zero_add, hv1] using hpq
  · intro i hi j hj hij
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · rfl
    · exact (hpqne (by simpa only [hv0, hv1] using hij)).elim
    · exact (hpqne (by simpa only [hv0, hv1] using hij.symm)).elim
    · rfl
  · intro j hj
    interval_cases j
    · rw [show arcChainFace v 0 = {v 0} by simpa using arcChainFace_two_mul v 0]
      simpa only [hv0] using hpB
    · rw [show 1 = 2 * 0 + 1 by omega, arcChainFace_two_mul_add_one]
      simpa only [hv0, zero_add, hv1] using hpqB
    · rw [show arcChainFace v 2 = {v 1} by simpa using arcChainFace_two_mul v 1]
      simpa only [hv1] using hqB

end DifferentialGeometry.Topology.PiecewiseLinear
