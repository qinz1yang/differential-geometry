/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification
import Mathlib.Topology.Homeomorph.Lemmas

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K K' : Geometry.SimplicialComplex ℝ E3} {h : E3 → E3}

private theorem not_isBounded_image_homeomorph (Ψ : E3 ≃ₜ E3) {S : Set E3}
    (hS : ¬ Bornology.IsBounded S) : ¬ Bornology.IsBounded (Ψ '' S) := by
  intro hb
  apply hS
  apply (hb.isCompact_closure.image Ψ.symm.continuous).isBounded.subset
  intro x hx
  exact ⟨Ψ x, subset_closure (mem_image_of_mem Ψ hx), Ψ.symm_apply_apply x⟩

open Classical in
theorem Section34CompactExterior.update_image_of_supported
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {fbl : Section34CompactSimplexIndex K 3 → Set E3}
    (hext : Section34CompactExterior K K' h tgtV fbl)
    (hmarkers : ∀ z : Section34CompactVertexIndex K K', h '' (z.1 : Set E3) ⊆ tgtV z)
    {s : Section34CompactSimplexIndex K 3} {w v : Section34CompactVertexIndex K K'}
    (hwi : Section34Incident w.1 s.1) (hvi : Section34Incident v.1 s.1)
    (Ψ : E3 ≃ₜ E3) {O : Set E3} (hfix : EqOn Ψ id Oᶜ)
    (hV : Ψ '' (⋃ z, tgtV z) = ⋃ z, tgtV z)
    (hOV : O ∩ (⋃ z, tgtV z) = O ∩ (tgtV w ∪ tgtV v))
    (hOf : Disjoint O (⋃ s' ≠ s, fbl s')) :
    Section34CompactExterior K K' h tgtV (Function.update fbl s (Ψ '' fbl s)) := by
  let fbl' := Function.update fbl s (Ψ '' fbl s)
  have hO : Ψ '' O = O := image_eq_of_homeomorph_eqOn_compl_of_subset Ψ hfix Subset.rfl
  have hΨO : ∀ x, Ψ x ∈ O ↔ x ∈ O := by
    intro x
    conv_lhs => rw [← hO]
    exact Ψ.injective.mem_set_image
  have hΨV : ∀ x, Ψ x ∈ ⋃ z, tgtV z ↔ x ∈ ⋃ z, tgtV z := by
    intro x
    conv_lhs => rw [← hV]
    exact Ψ.injective.mem_set_image
  have hother : ∀ s', s' ≠ s → Ψ '' fbl s' = fbl s' := by
    intro s' hs'
    apply Set.EqOn.image_eq_self
    intro x hx
    exact hfix (fun hxO => disjoint_left.mp hOf hxO (mem_iUnion₂.mpr ⟨s', hs', hx⟩))
  have hface : ∀ s', Ψ '' fbl s' = fbl' s' := by
    intro s'
    by_cases hs' : s' = s
    · subst s'
      simp [fbl']
    · simp [fbl', hs', hother s' hs']
  have hverts : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Ψ '' (⋃ (a : Section34CompactPatchIndex K K') (_ : a.1.1 = t), tgtV a.1.2) =
        ⋃ (a : Section34CompactPatchIndex K K') (_ : a.1.1 = t), tgtV a.1.2 := by
    intro t hst
    let Vt := ⋃ (a : Section34CompactPatchIndex K K') (_ : a.1.1 = t), tgtV a.1.2
    have hpair : tgtV w ∪ tgtV v ⊆ Vt := by
      refine union_subset ?_ ?_
      · exact subset_iUnion₂
          (s := fun (a : Section34CompactPatchIndex K K') (_ : a.1.1 = t) => tgtV a.1.2)
          ⟨⟨t, w⟩, hwi.trans (convexHull_min hst (convex_convexHull ℝ _))⟩ rfl
      · exact subset_iUnion₂
          (s := fun (a : Section34CompactPatchIndex K K') (_ : a.1.1 = t) => tgtV a.1.2)
          ⟨⟨t, v⟩, hvi.trans (convexHull_min hst (convex_convexHull ℝ _))⟩ rfl
    have hsub : Vt ⊆ ⋃ z, tgtV z := by
      rintro x hx
      obtain ⟨a, _, hxa⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨a.1.2, hxa⟩
    have hlocal : ∀ x ∈ O, x ∈ Vt ↔ x ∈ ⋃ z, tgtV z := by
      intro x hx
      exact ⟨fun hxV => hsub hxV, fun hxV =>
        hpair ((Set.ext_iff.mp hOV x).mp ⟨hx, hxV⟩).2⟩
    change Ψ '' Vt = Vt
    ext x
    rw [Ψ.image_eq_preimage_symm]
    change Ψ.symm x ∈ Vt ↔ x ∈ Vt
    by_cases hxO : x ∈ O
    · have hxiO : Ψ.symm x ∈ O := (hΨO _).mp (by simpa)
      rw [hlocal _ hxiO, hlocal _ hxO]
      exact (hΨV (Ψ.symm x)).symm.trans (by simp)
    · have hxi : Ψ.symm x = x := by
        apply Ψ.injective
        rw [Ψ.apply_symm_apply, hfix hxO]
        rfl
      rw [hxi]
  have hobs : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Ψ '' section34CompactTetraObstacle tgtV fbl t =
        section34CompactTetraObstacle tgtV fbl' t := by
    intro t hst
    simp only [section34CompactTetraObstacle, image_union, image_iUnion, hverts t hst, hface]
  have hunchanged : ∀ t : Section34CompactSimplexIndex K 4, ¬ Section34Incident s.1 t.1 →
      section34CompactTetraObstacle tgtV fbl' t = section34CompactTetraObstacle tgtV fbl t := by
    intro t hst
    unfold section34CompactTetraObstacle
    congr 1
    apply iUnion₂_congr
    intro s' hs'
    have hne : s' ≠ s := fun he => hst (he ▸ hs')
    simp [fbl', hne]
  intro t z hzt y hy
  have hunbounded := hext t z hzt y hy
  by_cases hst : Section34Incident s.1 t.1
  · have hyobs : y ∈ (section34CompactTetraObstacle tgtV fbl t)ᶜ := by
      by_contra hyobs
      rw [connectedComponentIn_eq_empty hyobs] at hunbounded
      exact hunbounded Bornology.isBounded_empty
    have hyO : y ∉ O := by
      intro hyO
      have hypair := ((Set.ext_iff.mp hOV y).mp
        ⟨hyO, mem_iUnion.mpr ⟨z, hmarkers z hy⟩⟩).2
      apply hyobs
      apply Or.inl
      rcases hypair with hyw | hyv
      · exact mem_iUnion₂.mpr ⟨⟨⟨t, w⟩,
          hwi.trans (convexHull_min hst (convex_convexHull ℝ _))⟩, rfl, hyw⟩
      · exact mem_iUnion₂.mpr ⟨⟨⟨t, v⟩,
          hvi.trans (convexHull_min hst (convex_convexHull ℝ _))⟩, rfl, hyv⟩
    have hcomp := Ψ.image_connectedComponentIn hyobs
    rw [Ψ.image_compl, hobs t hst, hfix hyO, id_eq] at hcomp
    change ¬ Bornology.IsBounded (connectedComponentIn
      (section34CompactTetraObstacle tgtV fbl' t)ᶜ y)
    rw [← hcomp]
    exact not_isBounded_image_homeomorph Ψ hunbounded
  · change ¬ Bornology.IsBounded (connectedComponentIn
      (section34CompactTetraObstacle tgtV fbl' t)ᶜ y)
    rw [hunchanged t hst]
    exact hunbounded

end DifferentialGeometry.Topology.PiecewiseLinear
