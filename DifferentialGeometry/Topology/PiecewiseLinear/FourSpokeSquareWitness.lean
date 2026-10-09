/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeDisk
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies

theorem fourSpokeIndexCases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide

def fourSpokeModelLeaf : Fin 4 → ℝ × ℝ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (0, -1)

theorem mem_segment_zero_prod_iff {a p : ℝ × ℝ} :
    p ∈ segment ℝ (0 : ℝ × ℝ) a ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p.1 = t * a.1 ∧ p.2 = t * a.2 := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    refine ⟨t, ht, by linarith, ?_, ?_⟩ <;> simp
  · rintro ⟨t, ht0, ht1, h1, h2⟩
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp [h1, h2]

theorem fourSpokeModelLeaf_ne_zero (i : Fin 4) : fourSpokeModelLeaf i ≠ (0 : ℝ × ℝ) := by
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    simp [fourSpokeModelLeaf, Prod.ext_iff]

theorem fourSpokeModelLeaf_injective : Function.Injective fourSpokeModelLeaf := by
  intro i j hij
  revert hij
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
      norm_num [fourSpokeModelLeaf, Prod.ext_iff]

theorem segment_zero_fourSpokeModelLeaf_subset (i : Fin 4) :
    segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ⊆ spliceSquare := by
  intro p hp
  obtain ⟨t, ht0, ht1, h1, h2⟩ := mem_segment_zero_prod_iff.mp hp
  rw [mem_spliceSquare]
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    · norm_num [fourSpokeModelLeaf] at h1 h2
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem eq_of_mem_frontier_spliceSquare_of_snd_eq_zero {p : ℝ × ℝ}
    (hp : p ∈ frontier spliceSquare) (h : p.2 = 0) : p = (1, 0) ∨ p = (-1, 0) := by
  rw [← spliceSquareBoundary_eq_frontier, mem_spliceSquareBoundary] at hp
  rcases hp.2 with h1 | h1 | h1 | h1
  · exact Or.inr (Prod.ext h1 h)
  · exact Or.inl (Prod.ext h1 h)
  · rw [h] at h1; norm_num at h1
  · rw [h] at h1; norm_num at h1

theorem segment_zero_fourSpokeModelLeaf_inter_frontier (i : Fin 4) :
    segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ∩ frontier spliceSquare =
      {fourSpokeModelLeaf i} := by
  rw [← spliceSquareBoundary_eq_frontier]
  refine Subset.antisymm ?_ ?_
  · rintro p ⟨hp, hb⟩
    obtain ⟨t, ht0, ht1, h1, h2⟩ := mem_segment_zero_prod_iff.mp hp
    rw [mem_spliceSquareBoundary] at hb
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl
    · norm_num [fourSpokeModelLeaf] at h1 h2
      simp only [fourSpokeModelLeaf]
      refine mem_singleton_iff.mpr (Prod.ext ?_ ?_)
      · change p.1 = (1 : ℝ)
        rcases hb.2 with h | h | h | h <;> linarith
      · change p.2 = (0 : ℝ)
        linarith
    · norm_num [fourSpokeModelLeaf] at h1 h2
      simp only [fourSpokeModelLeaf]
      refine mem_singleton_iff.mpr (Prod.ext ?_ ?_)
      · change p.1 = (0 : ℝ)
        linarith
      · change p.2 = (1 : ℝ)
        rcases hb.2 with h | h | h | h <;> linarith
    · norm_num [fourSpokeModelLeaf] at h1 h2
      simp only [fourSpokeModelLeaf]
      refine mem_singleton_iff.mpr (Prod.ext ?_ ?_)
      · change p.1 = (-1 : ℝ)
        rcases hb.2 with h | h | h | h <;> linarith
      · change p.2 = (0 : ℝ)
        linarith
    · norm_num [fourSpokeModelLeaf] at h1 h2
      simp only [fourSpokeModelLeaf]
      refine mem_singleton_iff.mpr (Prod.ext ?_ ?_)
      · change p.1 = (0 : ℝ)
        linarith
      · change p.2 = (-1 : ℝ)
        rcases hb.2 with h | h | h | h <;> linarith
  · rintro p rfl
    refine ⟨right_mem_segment ℝ _ _, ?_⟩
    rw [mem_spliceSquareBoundary]
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_⟩ <;> norm_num [fourSpokeModelLeaf, mem_spliceSquare]

theorem segment_zero_fourSpokeModelLeaf_inter {i j : Fin 4} (hij : i ≠ j) :
    segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ∩
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf j) = {(0 : ℝ × ℝ)} := by
  refine Subset.antisymm ?_ ?_
  · rintro p ⟨hp, hq⟩
    obtain ⟨t, ht0, ht1, h1, h2⟩ := mem_segment_zero_prod_iff.mp hp
    obtain ⟨s, hs0, hs1, k1, k2⟩ := mem_segment_zero_prod_iff.mp hq
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
      rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hij
          | (norm_num [fourSpokeModelLeaf] at h1 h2 k1 k2
             exact mem_singleton_iff.mpr
               (Prod.ext (show p.1 = (0 : ℝ) by linarith) (show p.2 = (0 : ℝ) by linarith)))
  · rintro p rfl
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

noncomputable def fourSpokePlaneEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

theorem isPLHomeomorphOn_fourSpokePlaneEquiv {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPLHomeomorphOn fourSpokePlaneEquiv S (fourSpokePlaneEquiv '' S) :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hS
    ((isPiecewiseAffineOn_of_affine fourSpokePlaneEquiv.toLinearMap.toAffineMap
      isOpen_univ).mono_of_isPolyhedron hS (subset_univ _))
    fourSpokePlaneEquiv.injective.injOn.bijOn_image

theorem image_segment_fourSpokePlaneEquiv (a b : ℝ × ℝ) :
    fourSpokePlaneEquiv '' segment ℝ a b =
      segment ℝ (fourSpokePlaneEquiv a) (fourSpokePlaneEquiv b) := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, t, hs, ht, hst, rfl⟩, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [map_add, map_smul, map_smul]⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨s • a + t • b, ⟨s, t, hs, ht, hst, rfl⟩, by rw [map_add, map_smul, map_smul]⟩

noncomputable def fourSpokeSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  fourSpokePlaneEquiv '' spliceSquare

noncomputable def fourSpokeCentre : EuclideanSpace ℝ (Fin 2) := fourSpokePlaneEquiv 0

noncomputable def fourSpokeLeaf (i : Fin 4) : EuclideanSpace ℝ (Fin 2) :=
  fourSpokePlaneEquiv (fourSpokeModelLeaf i)

noncomputable def fourSpokeArm (i : Fin 4) : Set (EuclideanSpace ℝ (Fin 2)) :=
  segment ℝ fourSpokeCentre (fourSpokeLeaf i)

theorem fourSpokeArm_eq_image (i : Fin 4) :
    fourSpokeArm i = fourSpokePlaneEquiv '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) :=
  (image_segment_fourSpokePlaneEquiv _ _).symm

theorem fourSpokeCentre_ne_leaf (i : Fin 4) : fourSpokeCentre ≠ fourSpokeLeaf i := fun h =>
  (fourSpokeModelLeaf_ne_zero i) (fourSpokePlaneEquiv.injective h.symm)

theorem isPLBall_fourSpokeSquare : IsPLBall 2 fourSpokeSquare :=
  isPLBall_spliceSquare.of_isPLHomeomorphOn
    (isPLHomeomorphOn_fourSpokePlaneEquiv isPLBall_spliceSquare.isPolyhedron)

theorem frontier_fourSpokeSquare :
    frontier fourSpokeSquare = fourSpokePlaneEquiv '' frontier spliceSquare := by
  simpa [fourSpokeSquare] using
    (fourSpokePlaneEquiv.toHomeomorph.image_frontier spliceSquare).symm

theorem isPLBall_fourSpokeArm (i : Fin 4) : IsPLBall 1 (fourSpokeArm i) :=
  isPLBall_segment (fourSpokeCentre_ne_leaf i)

theorem isArcBetween_fourSpokeArm (i : Fin 4) :
    IsArcBetween (fourSpokeArm i) fourSpokeCentre (fourSpokeLeaf i) :=
  isArcBetween_segment (fourSpokeCentre_ne_leaf i)

theorem fourSpokeArm_subset (i : Fin 4) : fourSpokeArm i ⊆ fourSpokeSquare := by
  rw [fourSpokeArm_eq_image, fourSpokeSquare]
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, segment_zero_fourSpokeModelLeaf_subset i hy, rfl⟩

theorem fourSpokeArm_inter_frontier (i : Fin 4) :
    fourSpokeArm i ∩ frontier fourSpokeSquare = {fourSpokeLeaf i} := by
  rw [fourSpokeArm_eq_image, frontier_fourSpokeSquare,
    ← Set.image_inter fourSpokePlaneEquiv.injective,
    segment_zero_fourSpokeModelLeaf_inter_frontier, image_singleton]
  rfl

theorem fourSpokeArm_inter {i j : Fin 4} (hij : i ≠ j) :
    fourSpokeArm i ∩ fourSpokeArm j = {fourSpokeCentre} := by
  rw [fourSpokeArm_eq_image, fourSpokeArm_eq_image,
    ← Set.image_inter fourSpokePlaneEquiv.injective,
    segment_zero_fourSpokeModelLeaf_inter hij, image_singleton]
  rfl

theorem fourSpokeLeaf_mem_frontier (i : Fin 4) :
    fourSpokeLeaf i ∈ frontier fourSpokeSquare :=
  ((fourSpokeArm_inter_frontier i).symm.subset rfl).2

theorem fourSpokeLeaf_injective : Function.Injective fourSpokeLeaf := fun _ _ h =>
  fourSpokeModelLeaf_injective (fourSpokePlaneEquiv.injective h)

theorem exists_isCutPair_fourSpokeSquare :
    ∃ A₁ A₂ : Set (EuclideanSpace ℝ (Fin 2)),
      IsCutPair (frontier fourSpokeSquare) (fourSpokeLeaf 0) (fourSpokeLeaf 2) A₁ A₂ ∧
        fourSpokeLeaf 1 ∈ A₁ ∧ fourSpokeLeaf 3 ∈ A₂ := by
  have hne02 : fourSpokeLeaf 0 ≠ fourSpokeLeaf 2 := fun h =>
    (by decide : (0 : Fin 4) ≠ 2) (fourSpokeLeaf_injective h)
  obtain ⟨A, B, hcut, -, -⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one
    isPLBall_fourSpokeSquare.isPLSphere_frontier (fourSpokeLeaf_mem_frontier 0)
    (fourSpokeLeaf_mem_frontier 2) hne02
  have hsep : ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin 2)),
      IsCutPair (frontier fourSpokeSquare) (fourSpokeLeaf 0) (fourSpokeLeaf 2) C₁ C₂ →
      fourSpokeLeaf 1 ∈ C₁ → fourSpokeLeaf 3 ∈ C₁ → False := by
    intro C₁ C₂ hc hm1 hm3
    have hmem : ∀ k : Fin 4, k ≠ 0 → k ≠ 2 → fourSpokeLeaf k ∈ C₁ →
        fourSpokeModelLeaf k ∈ fourSpokePlaneEquiv.symm ''
          (C₁ \ {fourSpokeLeaf 0, fourSpokeLeaf 2}) := by
      intro k hk0 hk2 hkC
      refine ⟨fourSpokeLeaf k, ⟨hkC, ?_⟩, ?_⟩
      · rintro (h | h)
        · exact hk0 (fourSpokeLeaf_injective h)
        · exact hk2 (fourSpokeLeaf_injective h)
      · exact fourSpokePlaneEquiv.symm_apply_apply _
    have hsub : fourSpokePlaneEquiv.symm '' (C₁ \ {fourSpokeLeaf 0, fourSpokeLeaf 2}) ⊆
        {p : ℝ × ℝ | 0 < p.2} ∪ {p : ℝ × ℝ | p.2 < 0} := by
      rintro p ⟨x, ⟨hxC, hx⟩, rfl⟩
      have hxJ : x ∈ frontier fourSpokeSquare := hc.fst_subset hxC
      rw [frontier_fourSpokeSquare] at hxJ
      obtain ⟨y, hy, rfl⟩ := hxJ
      rw [fourSpokePlaneEquiv.symm_apply_apply]
      rcases lt_trichotomy y.2 0 with h | h | h
      · exact Or.inr h
      · exfalso
        rcases eq_of_mem_frontier_spliceSquare_of_snd_eq_zero hy h with rfl | rfl
        · exact hx (Or.inl rfl)
        · exact hx (Or.inr rfl)
      · exact Or.inl h
    have hpre : IsPreconnected (fourSpokePlaneEquiv.symm ''
        (C₁ \ {fourSpokeLeaf 0, fourSpokeLeaf 2})) :=
      hc.fst.isPreconnected_diff.image _ fourSpokePlaneEquiv.symm.continuous.continuousOn
    have hd : Disjoint {p : ℝ × ℝ | 0 < p.2} {p : ℝ × ℝ | p.2 < 0} := by
      rw [Set.disjoint_left]
      intro p hp hp'
      have hp1 : (0 : ℝ) < p.2 := hp
      have hp2 : p.2 < 0 := hp'
      linarith
    have hone := IsPreconnected.subset_or_subset
      (isOpen_lt continuous_const continuous_snd) (isOpen_lt continuous_snd continuous_const)
      hd hsub hpre
    have h1 := hmem 1 (by decide) (by decide) hm1
    have h3 := hmem 3 (by decide) (by decide) hm3
    rcases hone with h | h
    · have hx : (0 : ℝ) < (fourSpokeModelLeaf 3).2 := h h3
      simp only [fourSpokeModelLeaf] at hx
      norm_num at hx
    · have hx : (fourSpokeModelLeaf 1).2 < 0 := h h1
      simp only [fourSpokeModelLeaf] at hx
      norm_num at hx
  have hmemAB : fourSpokeLeaf 1 ∈ A ∪ B := by
    rw [hcut.union_eq]; exact fourSpokeLeaf_mem_frontier 1
  have hmemAB' : fourSpokeLeaf 3 ∈ A ∪ B := by
    rw [hcut.union_eq]; exact fourSpokeLeaf_mem_frontier 3
  rcases hmemAB with h1 | h1
  · exact ⟨A, B, hcut, h1, hmemAB'.resolve_left fun h3 => hsep A B hcut h1 h3⟩
  · exact ⟨B, A, hcut.symm, h1, hmemAB'.resolve_right fun h3 => hsep B A hcut.symm h1 h3⟩

theorem exists_isPLHomeomorphOn_fourSpokeSquare :
    ∃ F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn F fourSpokeSquare fourSpokeSquare ∧
        EqOn F id (frontier fourSpokeSquare) ∧ ∀ i, EqOn F id (fourSpokeArm i) := by
  obtain ⟨A₁, A₂, hcut, hv1, hv3⟩ := exists_isCutPair_fourSpokeSquare
  exact exists_isPLHomeomorphOn_of_fourSpokeDisk isPLBall_fourSpokeSquare
    isPLBall_fourSpokeSquare isPLBall_fourSpokeArm isPLBall_fourSpokeArm
    isArcBetween_fourSpokeArm isArcBetween_fourSpokeArm fourSpokeArm_subset
    fourSpokeArm_subset fourSpokeArm_inter_frontier fourSpokeArm_inter_frontier
    (fun _ _ h => fourSpokeArm_inter h) (fun _ _ h => fourSpokeArm_inter h) hcut hv1 hv3
    (π := 1) (g := id)
    isPLBall_fourSpokeSquare.isPLSphere_frontier.isPolyhedron.isPLHomeomorphOn_id
    (fun _ => rfl) (q := fun _ => id)
    (fun i => (isPLBall_fourSpokeArm i).isPolyhedron.isPLHomeomorphOn_id)
    (fun _ => rfl) (fun _ => rfl)

noncomputable def fourSpokeFlip :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (fourSpokePlaneEquiv.symm.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)).trans
    fourSpokePlaneEquiv

def fourSpokeFlipPerm : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem fourSpokeFlipPerm_zero : fourSpokeFlipPerm 0 = 1 := by decide

theorem fourSpokeFlipPerm_one : fourSpokeFlipPerm 1 = 0 := by decide

theorem fourSpokeFlipPerm_two : fourSpokeFlipPerm 2 = 3 := by decide

theorem fourSpokeFlipPerm_three : fourSpokeFlipPerm 3 = 2 := by decide

theorem fourSpokeFlip_apply (x : ℝ × ℝ) :
    fourSpokeFlip (fourSpokePlaneEquiv x) = fourSpokePlaneEquiv (Prod.swap x) := by
  simp [fourSpokeFlip, Prod.swap]

theorem image_swap_spliceSquare : Prod.swap '' spliceSquare = spliceSquare := by
  have hiff : ∀ p : ℝ × ℝ, Prod.swap p ∈ spliceSquare ↔ p ∈ spliceSquare := by
    intro p
    simp only [mem_spliceSquare, Prod.fst_swap, Prod.snd_swap]
    tauto
  refine Subset.antisymm ?_ fun p hp => ⟨Prod.swap p, (hiff p).mpr hp, Prod.swap_swap p⟩
  rintro x ⟨y, hy, rfl⟩
  exact (hiff y).mpr hy

theorem image_swap_segment (a b : ℝ × ℝ) :
    Prod.swap '' segment ℝ a b = segment ℝ (Prod.swap a) (Prod.swap b) := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, t, hs, ht, hst, rfl⟩, rfl⟩
    refine ⟨s, t, hs, ht, hst, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    refine ⟨s • a + t • b, ⟨s, t, hs, ht, hst, rfl⟩, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp

theorem swap_fourSpokeModelLeaf (i : Fin 4) :
    Prod.swap (fourSpokeModelLeaf i) = fourSpokeModelLeaf (fourSpokeFlipPerm i) := by
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl
  · rw [fourSpokeFlipPerm_zero]; rfl
  · rw [fourSpokeFlipPerm_one]; rfl
  · rw [fourSpokeFlipPerm_two]; rfl
  · rw [fourSpokeFlipPerm_three]; rfl

theorem isPLHomeomorphOn_fourSpokeFlip {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : IsPolyhedron S) : IsPLHomeomorphOn fourSpokeFlip S (fourSpokeFlip '' S) :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hS
    ((isPiecewiseAffineOn_of_affine fourSpokeFlip.toLinearMap.toAffineMap
      isOpen_univ).mono_of_isPolyhedron hS (subset_univ _))
    fourSpokeFlip.injective.injOn.bijOn_image

theorem image_fourSpokeFlip_square : fourSpokeFlip '' fourSpokeSquare = fourSpokeSquare := by
  have hcomp : (fourSpokeFlip : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) ∘
      (fourSpokePlaneEquiv : (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) =
      (fourSpokePlaneEquiv : (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) ∘ Prod.swap :=
    funext fourSpokeFlip_apply
  rw [fourSpokeSquare, ← image_comp, hcomp, image_comp, image_swap_spliceSquare]

theorem image_fourSpokeFlip_frontier :
    fourSpokeFlip '' frontier fourSpokeSquare = frontier fourSpokeSquare := by
  have h : fourSpokeFlip '' frontier fourSpokeSquare =
      frontier (fourSpokeFlip '' fourSpokeSquare) := by
    simpa using fourSpokeFlip.toHomeomorph.image_frontier fourSpokeSquare
  rw [h, image_fourSpokeFlip_square]

theorem fourSpokeFlip_centre : fourSpokeFlip fourSpokeCentre = fourSpokeCentre := by
  rw [fourSpokeCentre, fourSpokeFlip_apply]
  rfl

theorem fourSpokeFlip_leaf (i : Fin 4) :
    fourSpokeFlip (fourSpokeLeaf i) = fourSpokeLeaf (fourSpokeFlipPerm i) := by
  rw [fourSpokeLeaf, fourSpokeLeaf, fourSpokeFlip_apply, swap_fourSpokeModelLeaf]

theorem image_fourSpokeFlip_arm (i : Fin 4) :
    fourSpokeFlip '' fourSpokeArm i = fourSpokeArm (fourSpokeFlipPerm i) := by
  have hcomp : (fourSpokeFlip : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) ∘
      (fourSpokePlaneEquiv : (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) =
      (fourSpokePlaneEquiv : (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) ∘ Prod.swap :=
    funext fourSpokeFlip_apply
  have hzero : Prod.swap (0 : ℝ × ℝ) = 0 := rfl
  rw [fourSpokeArm_eq_image, fourSpokeArm_eq_image, ← image_comp, hcomp, image_comp,
    image_swap_segment, hzero, swap_fourSpokeModelLeaf]

theorem exists_isPLHomeomorphOn_fourSpokeSquare_flip :
    ∃ F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn F fourSpokeSquare fourSpokeSquare ∧
        EqOn F fourSpokeFlip (frontier fourSpokeSquare) ∧
        ∀ i, EqOn F fourSpokeFlip (fourSpokeArm i) := by
  obtain ⟨A₁, A₂, hcut, hv1, hv3⟩ := exists_isCutPair_fourSpokeSquare
  have hg : IsPLHomeomorphOn fourSpokeFlip (frontier fourSpokeSquare)
      (frontier fourSpokeSquare) := by
    have h := isPLHomeomorphOn_fourSpokeFlip
      isPLBall_fourSpokeSquare.isPLSphere_frontier.isPolyhedron
    rwa [image_fourSpokeFlip_frontier] at h
  have hq : ∀ i, IsPLHomeomorphOn fourSpokeFlip (fourSpokeArm i)
      (fourSpokeArm (fourSpokeFlipPerm i)) := by
    intro i
    have h := isPLHomeomorphOn_fourSpokeFlip (isPLBall_fourSpokeArm i).isPolyhedron
    rwa [image_fourSpokeFlip_arm] at h
  exact exists_isPLHomeomorphOn_of_fourSpokeDisk isPLBall_fourSpokeSquare
    isPLBall_fourSpokeSquare isPLBall_fourSpokeArm isPLBall_fourSpokeArm
    isArcBetween_fourSpokeArm isArcBetween_fourSpokeArm fourSpokeArm_subset
    fourSpokeArm_subset fourSpokeArm_inter_frontier fourSpokeArm_inter_frontier
    (fun _ _ h => fourSpokeArm_inter h) (fun _ _ h => fourSpokeArm_inter h) hcut hv1 hv3
    (π := fourSpokeFlipPerm) (g := fourSpokeFlip) hg fourSpokeFlip_leaf
    (q := fun _ => fourSpokeFlip) hq (fun _ => fourSpokeFlip_centre) (fun _ => rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
