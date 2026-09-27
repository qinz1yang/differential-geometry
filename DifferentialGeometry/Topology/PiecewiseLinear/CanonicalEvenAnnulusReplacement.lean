/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalReturningAnnulusDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerPatchedSurfaceClosed

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.towerSurface_update_even_eq_sdiff
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (E : ℤ → Set E3) (hET : ∀ i, E (2 * i) ⊆ T'' (2 * i))
    (k : ℤ) (hfull : E (2 * k) = T'' (2 * k)) {B₀ B₁ J₀ J₁ : Set E3}
    (hcover : B₀ ∪ B₁ = T'' (2 * k)) (hmeet : B₀ ∩ B₁ = J₀ ∪ J₁)
    (hleft : (X (k - 1)).space ∩ T'' (2 * k) = J₀)
    (hright : (X k).space ∩ T'' (2 * k) = J₁) :
    towerSurface (Function.update E (2 * k) B₀) (fun j => (X j).space) P' =
      towerSurface E (fun j => (X j).space) P' \ (B₁ \ (J₀ ∪ J₁)) := by
  classical
  have hB₀T : B₀ ⊆ T'' (2 * k) := subset_union_left.trans hcover.subset
  have hB₁T : B₁ ⊆ T'' (2 * k) := subset_union_right.trans hcover.subset
  have hother (j : ℤ) (hjk : j ≠ k) : Disjoint (E (2 * j)) (B₁ \ (J₀ ∪ J₁)) :=
    (htw.apart (2 * j) (2 * k) (by rw [le_abs]; omega)).mono
      ((hET j).trans (htw.boundary_subset_outer _))
      (sdiff_subset.trans (hB₁T.trans (htw.boundary_subset_outer _)))
  have hrow (j : ℤ) : Disjoint (X j).space (B₁ \ (J₀ ∪ J₁)) := by
    apply disjoint_left.mpr
    rintro x hx ⟨hxB, hxJ⟩
    have hxT := hB₁T hxB
    by_cases hjlo : j = k - 1
    · subst j
      exact hxJ (Or.inl (hleft.subset ⟨hx, hxT⟩))
    · by_cases hjhi : j = k
      · subst j
        exact hxJ (Or.inr (hright.subset ⟨hx, hxT⟩))
      · rcases hX.carrier j hx with (hxlo | hxmid) | hxhi
        · exact disjoint_left.mp (htw.apart (2 * j) (2 * k) (by rw [le_abs]; omega))
            hxlo (htw.boundary_subset_outer _ hxT)
        · exact disjoint_left.mp (htw.apart (2 * j + 1) (2 * k) (by rw [le_abs]; omega))
            hxmid (htw.boundary_subset_outer _ hxT)
        · exact disjoint_left.mp (htw.apart (2 * (j + 1)) (2 * k) (by rw [le_abs]; omega))
            hxhi (htw.boundary_subset_outer _ hxT)
  have hcenter : P' ∉ B₁ \ (J₀ ∪ J₁) := by
    intro hx
    have hinner : S'' (2 * k) ⊆ interior (φ '' S (2 * k)) := by
      simpa using (htw.config (2 * k)).innerSubset 0
    exact htw.center_notMem_interior_outer _ (hinner (htw.boundary_subset_solid _ (hB₁T hx.1)))
  have hB₀D : Disjoint B₀ (B₁ \ (J₀ ∪ J₁)) := by
    apply disjoint_left.mpr
    rintro x hx ⟨hxB, hxJ⟩
    exact hxJ (hmeet.subset ⟨hx, hxB⟩)
  ext x
  constructor
  · rintro (hx | hxP)
    · obtain ⟨j, hxE | hxX⟩ := mem_iUnion.mp hx
      · by_cases hjk : j = k
        · subst j
          rw [Function.update_self] at hxE
          exact ⟨Or.inl (mem_iUnion.mpr ⟨k, Or.inl (hfull.symm ▸ hB₀T hxE)⟩),
            disjoint_left.mp hB₀D hxE⟩
        · rw [Function.update_of_ne (by omega : 2 * j ≠ 2 * k)] at hxE
          exact ⟨Or.inl (mem_iUnion.mpr ⟨j, Or.inl hxE⟩),
            disjoint_left.mp (hother j hjk) hxE⟩
      · exact ⟨Or.inl (mem_iUnion.mpr ⟨j, Or.inr hxX⟩), disjoint_left.mp (hrow j) hxX⟩
    · exact ⟨Or.inr hxP, hxP ▸ hcenter⟩
  · rintro ⟨hx | hxP, hxD⟩
    · obtain ⟨j, hxE | hxX⟩ := mem_iUnion.mp hx
      · by_cases hjk : j = k
        · subst j
          have hxB₀ : x ∈ B₀ := by
            rcases hcover.symm.subset (hfull ▸ hxE) with hxB₀ | hxB₁
            · exact hxB₀
            · by_contra hnot
              exact hxD ⟨hxB₁, fun hxJ => hnot (hmeet.symm.subset hxJ).1⟩
          exact Or.inl (mem_iUnion.mpr ⟨k, Or.inl (by simpa using hxB₀)⟩)
        · exact Or.inl (mem_iUnion.mpr ⟨j, Or.inl (by
            simpa only [Function.update_of_ne (by omega : 2 * j ≠ 2 * k)] using hxE)⟩)
      · exact Or.inl (mem_iUnion.mpr ⟨j, Or.inr hxX⟩)
    · exact Or.inr hxP

theorem IsCanonicalSurface.isSeparatorIn_after_replace_even_annulus
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hI : IsOpen I) (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    (E : ℤ → Set E3) (hE : ∀ i, IsClosed (E (2 * i)))
    (hET : ∀ i, E (2 * i) ⊆ T'' (2 * i))
    (hM : IsSeparatorIn I (towerSurface E (fun j => (X j).space) P') {a} {b})
    (k : ℤ) (hfull : E (2 * k) = T'' (2 * k)) {B₀ B₁ J₀ J₁ : Set E3}
    (hB₀ : IsPLAnnulusWithEnds B₀ J₀ J₁) (hB₁ : IsPLAnnulusWithEnds B₁ J₀ J₁)
    (hcover : B₀ ∪ B₁ = T'' (2 * k)) (hmeet : B₀ ∩ B₁ = J₀ ∪ J₁)
    (hleft : (X (k - 1)).space ∩ T'' (2 * k) = J₀)
    (hright : (X k).space ∩ T'' (2 * k) = J₁) :
    IsSeparatorIn I
      (towerSurface (Function.update E (2 * k) B₀) (fun j => (X j).space) P') {a} {b} := by
  classical
  have hB₀T : B₀ ⊆ T'' (2 * k) := subset_union_left.trans hcover.subset
  have hB₁T : B₁ ⊆ T'' (2 * k) := subset_union_right.trans hcover.subset
  have hB₀closed : IsClosed B₀ := by
    obtain ⟨L, hLfin, -, -, hLs, -⟩ := hB₀.exists_complex
    let _ : Finite L.faces := hLfin.to_subtype
    exact hLs ▸ (isPolyhedron_space L).isClosed
  have hclosed : IsClosed (((↑) : I → E3) ⁻¹'
      towerSurface (Function.update E (2 * k) B₀) (fun j => (X j).space) P') := by
    apply htw.isClosed_towerSurface_of_even_subset
    · intro i
      by_cases hik : 2 * i = 2 * k
      · simpa only [hik, Function.update_self] using hB₀closed
      · simpa only [Function.update_of_ne hik] using hE i
    · intro i
      by_cases hik : 2 * i = 2 * k
      · simpa only [hik, Function.update_self] using hB₀T
      · simpa only [Function.update_of_ne hik] using hET i
    · intro i
      let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
      exact (isPolyhedron_space (X i)).isClosed
    · exact hX.carrier
  have hsurface := hX.towerSurface_update_even_eq_sdiff htw E hET k hfull
    hcover hmeet hleft hright
  have htorusM : T'' (2 * k) ⊆ towerSurface E (fun j => (X j).space) P' :=
    fun _ hx => Or.inl (mem_iUnion.mpr ⟨k, Or.inl (hfull.symm ▸ hx)⟩)
  let V := (φ '' S (2 * k) ∪ φ '' S (2 * k + 1)) ∪ φ '' S (2 * k + 2)
  have hV : IsTopologicalSolidTorus V := htw.outer_triple_isTopologicalSolidTorus (2 * k)
  have hVI : V ⊆ I :=
    union_subset (union_subset (htw.subsetInterior _) (htw.subsetInterior _))
      (htw.subsetInterior _)
  have hTV : T'' (2 * k) ⊆ interior V := by
    have hinner : S'' (2 * k) ⊆ interior (φ '' S (2 * k)) := by
      simpa using (htw.config (2 * k)).innerSubset 0
    exact (htw.boundary_subset_solid _).trans
      (hinner.trans (interior_mono (subset_union_left.trans subset_union_left)))
  have hVavoid : Disjoint V ({a, b} : Set E3) :=
    ((havoid (2 * k)).union_left (havoid (2 * k + 1))).union_left (havoid (2 * k + 2))
  refine ⟨hclosed, ?_⟩
  rw [hsurface]
  exact hB₁.separates_after_delete_interior hB₀ (by rw [inter_comm, hmeet]) hI hV hVI
    (union_subset (hB₁T.trans hTV) (hB₀T.trans hTV)) (hB₁T.trans htorusM)
    (hB₀T.trans htorusM) (hsurface ▸ hclosed)
    (fun hx => disjoint_left.mp hVavoid hx (Or.inl rfl))
    (fun hx => disjoint_left.mp hVavoid hx (Or.inr rfl)) hM.2

theorem IsCanonicalSurface.exists_even_annulus_replacement
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hI : IsOpen I) (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    (E : ℤ → Set E3) (hE : ∀ i, IsClosed (E (2 * i)))
    (hET : ∀ i, E (2 * i) ⊆ T'' (2 * i))
    (hM : IsSeparatorIn I (towerSurface E (fun j => (X j).space) P') {a} {b})
    (k : ℤ) (hfull : E (2 * k) = T'' (2 * k)) {J₀ J₁ : Set E3}
    (h₀ : IsPLSphere 1 J₀) (h₁ : IsPLSphere 1 J₁)
    (hess₀ : ¬ boundsDiskIn J₀ (T'' (2 * k)))
    (hess₁ : ¬ boundsDiskIn J₁ (T'' (2 * k)))
    (hleft : (X (k - 1)).space ∩ T'' (2 * k) = J₀)
    (hright : (X k).space ∩ T'' (2 * k) = J₁) :
    ∃ B₀ B₁ : Set E3, IsPLAnnulusWithEnds B₀ J₀ J₁ ∧ IsPLAnnulusWithEnds B₁ J₀ J₁ ∧
      B₀ ∪ B₁ = T'' (2 * k) ∧ B₀ ∩ B₁ = J₀ ∪ J₁ ∧
      IsSeparatorIn I
        (towerSurface (Function.update E (2 * k) B₀) (fun j => (X j).space) P') {a} {b} ∧
      towerSurface (Function.update E (2 * k) B₀) (fun j => (X j).space) P' =
        towerSurface E (fun j => (X j).space) P' \ (B₁ \ (J₀ ∪ J₁)) := by
  have hsolid : IsCombinatorialSolidTorus (S'' (2 * k)) := by
    simpa using (htw.config (2 * k)).isPolyhedralSolidTorus 0
  have h₀T : J₀ ⊆ frontier (S'' (2 * k)) :=
    fun _ hx => (htw.boundary_eq _).subset (hleft.symm.subset hx).2
  have h₁T : J₁ ⊆ frontier (S'' (2 * k)) :=
    fun _ hx => (htw.boundary_eq _).subset (hright.symm.subset hx).2
  have hdis : Disjoint J₀ J₁ := (hX.piecesDisjoint (by omega : k - 1 ≠ k)).mono
    (hleft.symm.subset.trans inter_subset_left) (hright.symm.subset.trans inter_subset_left)
  obtain ⟨B₀, B₁, hB₀, hB₁, hcover, hmeet⟩ :=
    hsolid.exists_annulus_pair_of_essential_circles h₀ h₁ h₀T h₁T hdis
      (by simpa only [← htw.boundary_eq] using hess₀)
      (by simpa only [← htw.boundary_eq] using hess₁)
  have hcover' : B₀ ∪ B₁ = T'' (2 * k) := hcover.trans (htw.boundary_eq _).symm
  exact ⟨B₀, B₁, hB₀, hB₁, hcover', hmeet,
    hX.isSeparatorIn_after_replace_even_annulus htw hI havoid E hE hET hM
      k hfull hB₀ hB₁ hcover' hmeet hleft hright,
    hX.towerSurface_update_even_eq_sdiff htw E hET k hfull hcover' hmeet hleft hright⟩

end DifferentialGeometry.Topology.PiecewiseLinear
