/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedWeights

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
private theorem centroid_pair_eq_combo (a b : E) (hab : a ≠ b) :
    ({a, b} : Finset E).centroid ℝ id = (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b := by
  rw [centroid_eq_sum _ (by simp)]
  norm_num [hab]

open Classical in
private theorem centroid_triple_eq_combo (a b c : E)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset E).centroid ℝ id =
      (1 / 3 : ℝ) • a + (1 / 3 : ℝ) • b + (1 / 3 : ℝ) • c := by
  rw [centroid_eq_sum _ (by simp)]
  norm_num [hab, hac, hbc, add_assoc]

open Classical in
theorem exists_mem_derivedNeighborhood_not_mem_relativeDerivedNeighborhood
    {K A : Geometry.SimplicialComplex ℝ E} (hA : A.faces ⊆ K.faces)
    {a b : E} (hab : a ≠ b) (habA : {a, b} ∈ A.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hsA : s ∉ A.faces) (has : a ∈ s) (hbs : b ∈ s) :
    ∃ x, x ∈ (derivedNeighborhood K A).space ∧
      x ∉ (relativeDerivedNeighborhood hA A).space := by
  let g := s.centroid ℝ id
  let c := ({a, b} : Finset E).centroid ℝ id
  let r : Finset E := {a, b, g}
  let h := r.centroid ℝ id
  let x := ({c, g} : Finset E).centroid ℝ id
  let R := relativeBarycentricSubdivision hA
  have hgA : g ∉ A.space := notMem_space_of_notMem_faces hA hs hsA
    (centroid_mem_openSimplex_of_mem_faces K s hs)
  have haA : a ∈ A.space := A.subset_space habA (by simp)
  have hbA : b ∈ A.space := A.subset_space habA (by simp)
  have hag : a ≠ g := fun heq => hgA (heq ▸ haA)
  have hbg : b ≠ g := fun heq => hgA (heq ▸ hbA)
  have hcA : c ∈ A.space := A.convexHull_subset_space habA
    (({a, b} : Finset E).centroid_mem_convexHull (by simp))
  have hcg : c ≠ g := fun heq => hgA (heq ▸ hcA)
  have hflags : IsFlag K {s} := by
    refine ⟨?_, ?_⟩
    · intro t ht
      simpa only [Finset.mem_singleton.mp ht] using hs
    · intro t ht u hu
      rw [Finset.mem_singleton.mp ht, Finset.mem_singleton.mp hu]
      exact Or.inl (Finset.Subset.refl _)
  have hr : r ∈ R.faces := by
    refine ⟨{a, b}, {s}, ?_, ?_⟩
    · refine ⟨Or.inr habA, hflags, ?_, ?_, Or.inl (by simp)⟩
      · intro t ht
        simpa only [Finset.mem_singleton.mp ht] using hsA
      · intro t ht v hv
        rw [Finset.mem_singleton.mp ht]
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact subset_convexHull ℝ _ has
        · exact subset_convexHull ℝ _ hbs
    · simp [r, g]
  have hgr : g ∈ r := by simp [r]
  have hgR : {g} ∈ R.faces :=
    R.down_closed hr (Finset.singleton_subset_iff.mpr hgr) (Finset.singleton_nonempty g)
  have hrA : r ∉ A.faces := fun hrA => hgA (A.subset_space hrA hgr)
  have hgAf : {g} ∉ A.faces := fun hgAf => hgA (A.subset_space hgAf (by simp))
  have hflagR : IsFlag R {{g}, r} := by
    refine ⟨?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hgR
      · exact hr
    · intro t ht u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht hu
      rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
      · exact Or.inl (Finset.Subset.refl _)
      · exact Or.inl (Finset.singleton_subset_iff.mpr hgr)
      · exact Or.inr (Finset.singleton_subset_iff.mpr hgr)
      · exact Or.inl (Finset.Subset.refl _)
  have hhgface : {h, g} ∈ (relativeSecondDerived hA).faces := by
    refine ⟨∅, {{g}, r}, ?_, ?_⟩
    · refine ⟨Or.inl rfl, hflagR, ?_, ?_, Or.inr (by simp)⟩
      · intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact hgAf
        · exact hrA
      · intro t ht
        simp only [Finset.coe_empty, empty_subset]
    · simp only [Finset.image_insert, Finset.image_singleton, Finset.centroid_singleton,
        id_eq, Finset.empty_union, h, Finset.pair_comm]
  have hhg : h ≠ g := by
    intro heq
    have heqr : r = {g} := injOn_faces_of_mem_openSimplex R
      (centroid_mem_openSimplex_of_mem_faces R) hr hgR
      (by simpa only [Finset.centroid_singleton, id_eq, h] using heq)
    have hcard : r.card = 3 := by simp [r, hab, hag, hbg]
    rw [heqr] at hcard
    norm_num at hcard
  have hcombo : (3 / 4 : ℝ) • h + (1 / 4 : ℝ) • g = x := by
    dsimp [h, r, x]
    rw [centroid_triple_eq_combo a b g hab hag hbg,
      centroid_pair_eq_combo c g hcg]
    dsimp [c]
    rw [centroid_pair_eq_combo a b hab]
    module
  have hxopen : x ∈ openSimplex ({h, g} : Finset E) := by
    refine ⟨fun v => if v = h then (3 / 4 : ℝ) else 1 / 4, ?_, ?_, ?_⟩
    · intro v hv
      dsimp only
      split <;> norm_num
    · norm_num [hhg, hhg.symm]
    · simpa [hhg, hhg.symm] using hcombo
  have he : {c, g} ∈ (barycentricSubdivision K).faces := by
    refine ⟨{{a, b}, s}, ?_, by simp, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact hA habA
        · exact hs
      · have hsub : {a, b} ⊆ s :=
          Finset.insert_subset_iff.mpr ⟨has, Finset.singleton_subset_iff.mpr hbs⟩
        intro t ht u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht hu
        rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
        · exact Or.inl (Finset.Subset.refl _)
        · exact Or.inl hsub
        · exact Or.inr hsub
        · exact Or.inl (Finset.Subset.refl _)
    · simp [c, g]
  have hxN : x ∈ (derivedNeighborhood K A).space := by
    have hxface : {x} ∈ (derivedNeighborhood K A).faces :=
      (singleton_centroid_mem_derivedNeighborhood_iff K A he).mpr
        ⟨{a, b}, habA, by simp [c]⟩
    exact (derivedNeighborhood K A).subset_space hxface (by simp)
  have hgK : {g} ∈ (barycentricSubdivision K).faces := by
    refine ⟨{s}, hflags, by simp, ?_⟩
    simp [g]
  have hgNface : {g} ∉ (derivedNeighborhood K A).faces := by
    intro hmem
    have hm : {({g} : Finset E).centroid ℝ id} ∈ (derivedNeighborhood K A).faces := by
      simpa only [Finset.centroid_singleton, id_eq] using hmem
    obtain ⟨t, ht, htg⟩ := (singleton_centroid_mem_derivedNeighborhood_iff K A hgK).mp hm
    have htgs : t.centroid ℝ id = s.centroid ℝ id := Finset.mem_singleton.mp htg
    exact hsA ((injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) (hA ht) hs htgs) ▸ ht)
  have hgK₂ : {g} ∈ (secondDerived K).faces :=
    (barycentricSubdivision_isSubdivision (barycentricSubdivision K)).singleton_mem hgK
  have hgN : g ∉ (derivedNeighborhood K A).space :=
    notMem_space_of_notMem_faces (derivedNeighborhood_faces_subset K A) hgK₂ hgNface
      (mem_openSimplex_singleton g)
  refine ⟨x, hxN, ?_⟩
  intro hxR
  obtain ⟨t, ht, hxt⟩ := (relativeDerivedNeighborhood hA A).mem_space_iff.mp hxR
  have hsub : {h, g} ⊆ t := face_subset_of_mem_openSimplex_of_mem_convexHull
    (relativeSecondDerived hA) hhgface ht.1 hxopen hxt
  exact hgN (ht.2 (subset_convexHull ℝ _ (hsub (by simp))))

open Classical in
theorem mem_faces_of_relativeDerivedNeighborhood_space_eq
    {K A : Geometry.SimplicialComplex ℝ E} (hA : A.faces ⊆ K.faces)
    (hspace : (relativeDerivedNeighborhood hA A).space = (derivedNeighborhood K A).space)
    {a b : E} (hab : a ≠ b) (habA : {a, b} ∈ A.faces)
    {s : Finset E} (hs : s ∈ K.faces) (has : a ∈ s) (hbs : b ∈ s) : s ∈ A.faces := by
  by_contra hsA
  obtain ⟨x, hx, hxnot⟩ :=
    exists_mem_derivedNeighborhood_not_mem_relativeDerivedNeighborhood hA hab habA hs hsA has hbs
  exact hxnot (hspace.symm ▸ hx)
end DifferentialGeometry.Topology.PiecewiseLinear
