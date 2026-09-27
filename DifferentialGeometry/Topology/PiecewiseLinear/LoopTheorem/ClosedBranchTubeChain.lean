/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeMarkedCell

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem segment_fourSpokeModelLeaf_subset_spliceSquare (i : Fin 4) :
    segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ⊆ spliceSquare :=
  isHPolytope_spliceSquare.convex.segment_subset zero_mem_spliceSquare
    (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1

theorem segment_fourSpokeModelLeaf_zero_inter_one :
    segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 0) ∩ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 1) =
      {0} := by
  apply Subset.antisymm
  · rintro p ⟨h0, h1⟩
    obtain ⟨a, -, rfl⟩ := mem_segment_zero_iff_smul.mp h0
    obtain ⟨b, -, hb⟩ := mem_segment_zero_iff_smul.mp h1
    have ha : a = 0 := by
      have h := congrArg Prod.fst hb
      simpa [fourSpokeModelLeaf] using h
    rw [ha, zero_smul]
    exact mem_singleton _
  · rintro p rfl
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

theorem eq_zero_of_image_segment_fourSpokeModelLeaf {h : ℝ × ℝ → ℝ × ℝ}
    (hseg : ∀ i, h '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i)) : h 0 = 0 := by
  have h0 : h 0 ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 0) := by
    rw [← hseg 0]
    exact mem_image_of_mem h (left_mem_segment ℝ _ _)
  have h1 : h 0 ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 1) := by
    rw [← hseg 1]
    exact mem_image_of_mem h (left_mem_segment ℝ _ _)
  have hmem : h 0 ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 0) ∩
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 1) := ⟨h0, h1⟩
  rw [segment_fourSpokeModelLeaf_zero_inter_one] at hmem
  exact hmem

theorem image_comp_prodMap_id_right {F : Type*} (Φ : (ℝ × ℝ) × ℝ → F) (s : ℝ → ℝ)
    (X : Set (ℝ × ℝ)) (Y : Set ℝ) : (Φ ∘ Prod.map id s) '' (X ×ˢ Y) = Φ '' (X ×ˢ (s '' Y)) := by
  rw [image_comp, prodMap_image_prod, image_id]

theorem image_comp_prodMap_id_left {F : Type*} (Φ : (ℝ × ℝ) × ℝ → F) (h : ℝ × ℝ → ℝ × ℝ)
    (X : Set (ℝ × ℝ)) (Y : Set ℝ) : (Φ ∘ Prod.map h id) '' (X ×ˢ Y) = Φ '' ((h '' X) ×ˢ Y) := by
  rw [image_comp, prodMap_image_prod, image_id]

theorem exists_spliceSquare_transition {G G' : (ℝ × ℝ) × ℝ → E} {B B' : Set E}
    (hG : IsPLHomeomorphOn G (spliceSquare ×ˢ Icc (0 : ℝ) 1) B)
    (hG' : IsPLHomeomorphOn G' (spliceSquare ×ˢ Icc (0 : ℝ) 1) B')
    (hcap : G '' (spliceSquare ×ˢ ({1} : Set ℝ)) = G' '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (harm : ∀ i, G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
      G' '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)))
    (hpt : ∀ i, G (fourSpokeModelLeaf i, 1) = G' (fourSpokeModelLeaf i, 0)) :
    ∃ h : ℝ × ℝ → ℝ × ℝ, IsPLHomeomorphOn h spliceSquare spliceSquare ∧
      (∀ x ∈ spliceSquare, G' (h x, 0) = G (x, 1)) ∧
      (∀ i, h '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
        segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i)) ∧
      ∀ i, h (fourSpokeModelLeaf i) = fourSpokeModelLeaf i := by
  have hsq : IsPolyhedron spliceSquare := isHPolytope_spliceSquare.isPolyhedron
  have hsub : ∀ a ∈ Icc (0 : ℝ) 1,
      spliceSquare ×ˢ ({a} : Set ℝ) ⊆ spliceSquare ×ˢ Icc (0 : ℝ) 1 :=
    fun a ha => prod_mono subset_rfl (singleton_subset_iff.mpr ha)
  have htop : IsPLHomeomorphOn G (spliceSquare ×ˢ ({1} : Set ℝ))
      (G '' (spliceSquare ×ˢ ({1} : Set ℝ))) :=
    hG.restrict (isPolyhedron_prod_singleton hsq 1) (hsub 1 ⟨zero_le_one, le_rfl⟩)
  have hbot : IsPLHomeomorphOn G' (spliceSquare ×ˢ ({0} : Set ℝ))
      (G' '' (spliceSquare ×ˢ ({0} : Set ℝ))) :=
    hG'.restrict (isPolyhedron_prod_singleton hsq 0) (hsub 0 ⟨le_rfl, zero_le_one⟩)
  have hbot' : IsPLHomeomorphOn (Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)))
      (G '' (spliceSquare ×ˢ ({1} : Set ℝ))) (spliceSquare ×ˢ ({0} : Set ℝ)) := by
    rw [hcap]
    exact hbot.symm
  obtain ⟨h, hh, hhG, hhseg⟩ : ∃ h : ℝ × ℝ → ℝ × ℝ,
      IsPLHomeomorphOn h spliceSquare spliceSquare ∧
        (∀ x ∈ spliceSquare, G' (h x, 0) = G (x, 1)) ∧
        ∀ i, h '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
          segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) := by
    refine ⟨Prod.fst ∘ Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) ∘ G ∘
      fun x => (x, (1 : ℝ)), (((hsq.isPLHomeomorphOn_prod_const 1).trans htop).trans
        hbot').trans (hsq.isPLHomeomorphOn_fst_prod_const 0), fun x hx => ?_, fun i => ?_⟩
    · have hmem : G (x, 1) ∈ G' '' (spliceSquare ×ˢ ({0} : Set ℝ)) := by
        rw [← hcap]
        exact mem_image_of_mem G ⟨hx, mem_singleton _⟩
      have hw := hbot.bijOn.invOn_invFunOn.2 hmem
      have hw2 : (Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) (G (x, 1))).2 = 0 :=
        (hbot.symm.bijOn.mapsTo hmem).2
      have hpair : ((Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) (G (x, 1))).1,
          (0 : ℝ)) = Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) (G (x, 1)) :=
        Prod.ext rfl hw2.symm
      change G' ((Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) (G (x, 1))).1, 0) =
        G (x, 1)
      rw [hpair]
      exact hw
    · rw [image_comp, image_comp, image_comp, ← prod_singleton, harm i,
        ((hbot.bijOn.invOn_invFunOn.1).mono
          (prod_mono (segment_fourSpokeModelLeaf_subset_spliceSquare i) subset_rfl)).image_image,
        fst_image_prod _ (singleton_nonempty 0)]
  refine ⟨h, hh, hhG, hhseg, fun i => ?_⟩
  have hri : fourSpokeModelLeaf i ∈ spliceSquare :=
    (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1
  have heq := hhG _ hri
  rw [hpt i] at heq
  have hsame := hG'.bijOn.injOn ⟨hh.bijOn.mapsTo hri, le_rfl, zero_le_one⟩
    ⟨hri, le_rfl, zero_le_one⟩ heq
  exact congrArg Prod.fst hsame

theorem exists_spliceCylinder_stack {Φ Ψ : (ℝ × ℝ) × ℝ → E} {A B : Set E}
    (hΦ : IsPLHomeomorphOn Φ (spliceSquare ×ˢ Icc (0 : ℝ) 1) A)
    (hΨ : IsPLHomeomorphOn Ψ (spliceSquare ×ˢ Icc (0 : ℝ) 1) B)
    (hΦΨ : ∀ x ∈ spliceSquare, Φ (x, 1) = Ψ (x, 0))
    (hAB : A ∩ B = Φ '' (spliceSquare ×ˢ ({1} : Set ℝ))) :
    ∃ Θ : (ℝ × ℝ) × ℝ → E, IsPLHomeomorphOn Θ (spliceSquare ×ˢ Icc (0 : ℝ) 1) (A ∪ B) ∧
      (∀ x ∈ spliceSquare, Θ (x, 0) = Φ (x, 0)) ∧ (∀ x ∈ spliceSquare, Θ (x, 1) = Ψ (x, 1)) ∧
      ∀ X ⊆ spliceSquare, Θ '' (X ×ˢ Icc (0 : ℝ) 1) =
        Φ '' (X ×ˢ Icc (0 : ℝ) 1) ∪ Ψ '' (X ×ˢ Icc (0 : ℝ) 1) := by
  have hsq : IsPolyhedron spliceSquare := isHPolytope_spliceSquare.isPolyhedron
  have hs₀ : IsPLHomeomorphOn (fun t : ℝ => 2 * t + 0) (Icc 0 (1 / 2)) (Icc 0 1) :=
    isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num) (by norm_num)
  have hs₁ : IsPLHomeomorphOn (fun t : ℝ => 2 * t + -1) (Icc (1 / 2) 1) (Icc 0 1) :=
    isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num) (by norm_num)
  have hf := (hsq.isPLHomeomorphOn_id.prodMap hs₀).trans hΦ
  have hg := (hsq.isPLHomeomorphOn_id.prodMap hs₁).trans hΨ
  obtain ⟨Θ, hΘ, hΘf, hΘg⟩ := exists_isPLHomeomorphOn_union
    (hsq.prod isHPolytope_Icc.isPolyhedron) (hsq.prod isHPolytope_Icc.isPolyhedron) hf hg
    (by
      rintro ⟨x, t⟩ ⟨⟨hx, -, ht1⟩, -, ht2, -⟩
      obtain rfl : t = 1 / 2 := le_antisymm ht1 ht2
      simp only [Function.comp_apply, Prod.map_apply, id_eq]
      rw [show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num, show (2 : ℝ) * (1 / 2) + -1 = 0 by norm_num]
      exact hΦΨ x hx)
    (by
      rintro y ⟨hyA, hyB⟩
      have hy : y ∈ Φ '' (spliceSquare ×ˢ ({1} : Set ℝ)) := by
        rw [← hAB]
        exact ⟨hyA, hyB⟩
      obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hy
      obtain rfl : t = 1 := ht
      refine ⟨(x, 1 / 2), ⟨⟨hx, by norm_num, le_rfl⟩, hx, le_rfl, by norm_num⟩, ?_⟩
      simp only [Function.comp_apply, Prod.map_apply, id_eq]
      rw [show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num])
  have hPQ : spliceSquare ×ˢ Icc (0 : ℝ) (1 / 2) ∪ spliceSquare ×ˢ Icc (1 / 2 : ℝ) 1 =
      spliceSquare ×ˢ Icc (0 : ℝ) 1 := by
    rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  rw [hPQ] at hΘ
  refine ⟨Θ, hΘ, fun x hx => ?_, fun x hx => ?_, fun X hX => ?_⟩
  · rw [hΘf ⟨hx, le_rfl, by norm_num⟩]
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    rw [show (2 : ℝ) * 0 + 0 = 0 by norm_num]
  · rw [hΘg ⟨hx, by norm_num, le_rfl⟩]
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    rw [show (2 : ℝ) * 1 + -1 = 1 by norm_num]
  · have hXs : X ×ˢ Icc (0 : ℝ) 1 = X ×ˢ Icc (0 : ℝ) (1 / 2) ∪ X ×ˢ Icc (1 / 2 : ℝ) 1 := by
      rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
    conv_lhs => rw [hXs, image_union]
    rw [(hΘf.mono (prod_mono hX subset_rfl)).image_eq,
      (hΘg.mono (prod_mono hX subset_rfl)).image_eq, image_comp_prodMap_id_right,
      image_comp_prodMap_id_right, hs₀.image_eq, hs₁.image_eq]

theorem iUnion_le_zero_eq_of_nat {α : Type*} (u : ℕ → Set α) : ⋃ k ≤ 0, u k = u 0 := by
  ext x
  simp only [mem_iUnion, exists_prop, Nat.le_zero, exists_eq_left]

theorem exists_spliceCylinder_chain {G : ℕ → (ℝ × ℝ) × ℝ → E} {B : ℕ → Set E} (m : ℕ)
    (hG : ∀ k ≤ m, IsPLHomeomorphOn (G k) (spliceSquare ×ˢ Icc (0 : ℝ) 1) (B k))
    (hcap : ∀ k < m, G k '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G (k + 1) '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (harm : ∀ k < m, ∀ i,
      G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
        G (k + 1) '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)))
    (hpt : ∀ k < m, ∀ i, G k (fourSpokeModelLeaf i, 1) = G (k + 1) (fourSpokeModelLeaf i, 0))
    (hadj : ∀ k < m, B k ∩ B (k + 1) = G k '' (spliceSquare ×ˢ ({1} : Set ℝ)))
    (hfar : ∀ j k, j + 1 < k → k ≤ m → Disjoint (B j) (B k)) :
    ∃ Φ : (ℝ × ℝ) × ℝ → E,
      IsPLHomeomorphOn Φ (spliceSquare ×ˢ Icc (0 : ℝ) 1) (⋃ k ≤ m, B k) ∧
      (∀ x ∈ spliceSquare, Φ (x, 0) = G 0 (x, 0)) ∧
      Φ '' (spliceSquare ×ˢ ({1} : Set ℝ)) = G m '' (spliceSquare ×ˢ ({1} : Set ℝ)) ∧
      (∀ i, Φ '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
        G m '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ))) ∧
      (∀ i, Φ (fourSpokeModelLeaf i, 1) = G m (fourSpokeModelLeaf i, 1)) ∧
      (∀ i, Φ '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        ⋃ k ≤ m, G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1)) ∧
      Φ '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) =
        ⋃ k ≤ m, G k '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) := by
  induction m with
  | zero =>
    refine ⟨G 0, ?_, fun x _ => rfl, rfl, fun i => rfl, fun i => rfl, fun i => ?_, ?_⟩
    · rw [iUnion_le_zero_eq_of_nat]
      exact hG 0 le_rfl
    · rw [iUnion_le_zero_eq_of_nat (fun k => G k '' _)]
    · rw [iUnion_le_zero_eq_of_nat (fun k => G k '' _)]
  | succ m ih =>
    obtain ⟨Φ, hΦ, hΦ0, hΦtop, hΦarm, hΦpt, hΦstrip, hΦcore⟩ := ih
      (fun k hk => hG k (hk.trans (Nat.le_succ m)))
      (fun k hk => hcap k (hk.trans (Nat.lt_succ_self m)))
      (fun k hk => harm k (hk.trans (Nat.lt_succ_self m)))
      (fun k hk => hpt k (hk.trans (Nat.lt_succ_self m)))
      (fun k hk => hadj k (hk.trans (Nat.lt_succ_self m)))
      (fun j k hjk hk => hfar j k hjk (hk.trans (Nat.le_succ m)))
    have hGm := hG (m + 1) le_rfl
    obtain ⟨h, hh, hhG, hhseg, hhr⟩ := exists_spliceSquare_transition hΦ hGm
      (hΦtop.trans (hcap m (Nat.lt_succ_self m)))
      (fun i => (hΦarm i).trans (harm m (Nat.lt_succ_self m) i))
      (fun i => (hΦpt i).trans (hpt m (Nat.lt_succ_self m) i))
    have hΨ : IsPLHomeomorphOn (G (m + 1) ∘ Prod.map h id) (spliceSquare ×ˢ Icc (0 : ℝ) 1)
        (B (m + 1)) :=
      (hh.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hGm
    have hAB : (⋃ k ≤ m, B k) ∩ B (m + 1) = Φ '' (spliceSquare ×ˢ ({1} : Set ℝ)) := by
      rw [hΦtop, ← hadj m (Nat.lt_succ_self m)]
      apply Subset.antisymm
      · rintro x ⟨hx, hx'⟩
        obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
        rcases hk.lt_or_eq with hk | rfl
        · exact absurd hx' (disjoint_left.mp (hfar k (m + 1) (by omega) le_rfl) hxk)
        · exact ⟨hxk, hx'⟩
      · rintro x ⟨hx, hx'⟩
        exact ⟨mem_iUnion₂.mpr ⟨m, le_rfl, hx⟩, hx'⟩
    obtain ⟨Θ, hΘ, hΘ0, hΘ1, hΘimg⟩ := exists_spliceCylinder_stack hΦ hΨ
      (fun x hx => (hhG x hx).symm) hAB
    have hΘtop : EqOn Θ (G (m + 1) ∘ Prod.map h id) (spliceSquare ×ˢ ({1} : Set ℝ)) := by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      obtain rfl : t = 1 := ht
      exact hΘ1 x hx
    have h0 : h 0 = 0 := eq_zero_of_image_segment_fourSpokeModelLeaf hhseg
    refine ⟨Θ, ?_, fun x hx => (hΘ0 x hx).trans (hΦ0 x hx), ?_, fun i => ?_, fun i => ?_,
      fun i => ?_, ?_⟩
    · rw [biUnion_le_succ]
      exact hΘ
    · rw [hΘtop.image_eq, image_comp_prodMap_id_left, hh.image_eq]
    · rw [(hΘtop.mono (prod_mono (segment_fourSpokeModelLeaf_subset_spliceSquare i)
        subset_rfl)).image_eq, image_comp_prodMap_id_left, hhseg i]
    · rw [hΘ1 _ (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1]
      simp only [Function.comp_apply, Prod.map_apply, id_eq]
      rw [hhr i]
    · rw [hΘimg _ (segment_fourSpokeModelLeaf_subset_spliceSquare i), hΦstrip i,
        image_comp_prodMap_id_left, hhseg i,
        biUnion_le_succ (fun k => G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ
          Icc (0 : ℝ) 1))]
    · rw [hΘimg _ (singleton_subset_iff.mpr zero_mem_spliceSquare), hΦcore,
        image_comp_prodMap_id_left, image_singleton, h0,
        biUnion_le_succ (fun k => G k '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1))]

theorem exists_isCylindricalDiagram_spliceSquare_of_chain {G : ℕ → (ℝ × ℝ) × ℝ → E}
    {B : ℕ → Set E} (m : ℕ)
    (hG : ∀ k ≤ m + 1, IsPLHomeomorphOn (G k) (spliceSquare ×ˢ Icc (0 : ℝ) 1) (B k))
    (hcap : ∀ k ≤ m, G k '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G (k + 1) '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (harm : ∀ k ≤ m, ∀ i,
      G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
        G (k + 1) '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)))
    (hpt : ∀ k ≤ m, ∀ i, G k (fourSpokeModelLeaf i, 1) = G (k + 1) (fourSpokeModelLeaf i, 0))
    (hadj : ∀ k < m, B k ∩ B (k + 1) = G k '' (spliceSquare ×ˢ ({1} : Set ℝ)))
    (hfar : ∀ j k, j + 1 < k → k ≤ m → Disjoint (B j) (B k))
    (hlast : (⋃ k ≤ m, B k) ∩ B (m + 1) =
      G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)) ∪ G m '' (spliceSquare ×ˢ ({1} : Set ℝ)))
    (hclose : G (m + 1) '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    {σ : Fin 4 → Fin 4}
    (hσ : ∀ i, G (m + 1) (fourSpokeModelLeaf (σ i), 1) = G 0 (fourSpokeModelLeaf i, 0)) :
    ∃ (φ : (ℝ × ℝ) × ℝ → E) (u : ℝ × ℝ → ℝ × ℝ),
      IsCylindricalDiagram φ spliceSquare (⋃ k ≤ m + 1, B k) ∧
      IsPLHomeomorphOn u spliceSquare spliceSquare ∧
      (∀ x ∈ spliceSquare, φ (x, 0) = φ (u x, 1)) ∧
      (∀ i, u (fourSpokeModelLeaf i) = fourSpokeModelLeaf (σ i)) ∧
      (∀ x ∈ spliceSquare, φ (x, 0) = G 0 (x, 0)) ∧
      (∀ i, φ (fourSpokeModelLeaf i, 1) = G (m + 1) (fourSpokeModelLeaf i, 1)) ∧
      φ (0, 1) = G (m + 1) (0, 1) ∧
      (∀ i, φ '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        ⋃ k ≤ m + 1, G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) =
        ⋃ k ≤ m + 1, G k '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) := by
  have hsq : IsPolyhedron spliceSquare := isHPolytope_spliceSquare.isPolyhedron
  obtain ⟨Φ, hΦ, hΦ0, hΦtop, hΦarm, hΦpt, hΦstrip, hΦcore⟩ := exists_spliceCylinder_chain m
    (fun k hk => hG k (hk.trans (Nat.le_succ m))) (fun k hk => hcap k hk.le)
    (fun k hk => harm k hk.le) (fun k hk => hpt k hk.le) hadj hfar
  have hGm := hG (m + 1) le_rfl
  obtain ⟨h, hh, hhG, hhseg, hhr⟩ := exists_spliceSquare_transition hΦ hGm
    (hΦtop.trans (hcap m le_rfl)) (fun i => (hΦarm i).trans (harm m le_rfl i))
    (fun i => (hΦpt i).trans (hpt m le_rfl i))
  have hΨ : IsPLHomeomorphOn (G (m + 1) ∘ Prod.map h id) (spliceSquare ×ˢ Icc (0 : ℝ) 1)
      (B (m + 1)) :=
    (hh.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hGm
  have hs₀ : IsPLHomeomorphOn (fun t : ℝ => 2 * t + 0) (Icc 0 (1 / 2)) (Icc 0 1) :=
    isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num) (by norm_num)
  have hs₁ : IsPLHomeomorphOn (fun t : ℝ => 2 * t + -1) (Icc (1 / 2) 1) (Icc 0 1) :=
    isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num) (by norm_num)
  have hf := (hsq.isPLHomeomorphOn_id.prodMap hs₀).trans hΦ
  have hg := (hsq.isPLHomeomorphOn_id.prodMap hs₁).trans hΨ
  have hf₀ : (Φ ∘ Prod.map id fun t : ℝ => 2 * t + 0) '' (spliceSquare ×ˢ ({0} : Set ℝ)) =
      G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)) := by
    rw [image_comp_prodMap_id_right, image_singleton, show (2 : ℝ) * 0 + 0 = 0 by norm_num]
    refine image_congr ?_
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    obtain rfl : t = 0 := ht
    exact hΦ0 x hx
  have hg₁ : ((G (m + 1) ∘ Prod.map h id) ∘ Prod.map id fun t : ℝ => 2 * t + -1) ''
      (spliceSquare ×ˢ ({1} : Set ℝ)) = G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)) := by
    rw [image_comp_prodMap_id_right, image_singleton, show (2 : ℝ) * 1 + -1 = 1 by norm_num,
      image_comp_prodMap_id_left, hh.image_eq, hclose]
  have hfm : (Φ ∘ Prod.map id fun t : ℝ => 2 * t + 0) '' (spliceSquare ×ˢ ({1 / 2} : Set ℝ)) =
      G m '' (spliceSquare ×ˢ ({1} : Set ℝ)) := by
    rw [image_comp_prodMap_id_right, image_singleton,
      show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num, hΦtop]
  have hfg : EqOn (Φ ∘ Prod.map id fun t : ℝ => 2 * t + 0)
      ((G (m + 1) ∘ Prod.map h id) ∘ Prod.map id fun t : ℝ => 2 * t + -1)
      (spliceSquare ×ˢ ({1 / 2} : Set ℝ)) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    obtain rfl : t = 1 / 2 := ht
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    rw [show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num, show (2 : ℝ) * (1 / 2) + -1 = 0 by norm_num]
    exact (hhG x hx).symm
  have hinter : (⋃ k ≤ m, B k) ∩ B (m + 1) =
      G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)) ∪ G m '' (spliceSquare ×ˢ ({1} : Set ℝ)) := hlast
  have hcyl := isCylindricalDiagram_piecewise hsq hf hg hf₀ hg₁ hfm hfg hinter
  obtain ⟨φ, hφcyl, hφf, hφg⟩ : ∃ φ : (ℝ × ℝ) × ℝ → E,
      IsCylindricalDiagram φ spliceSquare ((⋃ k ≤ m, B k) ∪ B (m + 1)) ∧
        EqOn φ (Φ ∘ Prod.map id fun t : ℝ => 2 * t + 0) (spliceSquare ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
        EqOn φ ((G (m + 1) ∘ Prod.map h id) ∘ Prod.map id fun t : ℝ => 2 * t + -1)
          (spliceSquare ×ˢ Icc (1 / 2 : ℝ) 1) := by
    classical
    refine ⟨_, hcyl, piecewise_eqOn _ _ _, fun p hp => ?_⟩
    by_cases hpP : p ∈ spliceSquare ×ˢ Icc (0 : ℝ) (1 / 2)
    · rw [piecewise_eq_of_mem _ _ _ hpP]
      exact hfg ⟨hpP.1, le_antisymm hpP.2.2 hp.2.1⟩
    · exact piecewise_eq_of_notMem _ _ _ hpP
  rw [← biUnion_le_succ] at hφcyl
  obtain ⟨u, hu, hφu⟩ := hφcyl.exists_isPLHomeomorphOn_endMap hsq
  have hφ0 : ∀ x ∈ spliceSquare, φ (x, 0) = G 0 (x, 0) := by
    intro x hx
    rw [hφf ⟨hx, le_rfl, by norm_num⟩]
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    rw [show (2 : ℝ) * 0 + 0 = 0 by norm_num]
    exact hΦ0 x hx
  have hφ1 : ∀ x ∈ spliceSquare, φ (x, 1) = G (m + 1) (h x, 1) := by
    intro x hx
    rw [hφg ⟨hx, by norm_num, le_rfl⟩]
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    rw [show (2 : ℝ) * 1 + -1 = 1 by norm_num]
  have hstrip : ∀ X ⊆ spliceSquare, φ '' (X ×ˢ Icc (0 : ℝ) 1) =
      Φ '' (X ×ˢ Icc (0 : ℝ) 1) ∪ G (m + 1) '' ((h '' X) ×ˢ Icc (0 : ℝ) 1) := by
    intro X hX
    have hX' : X ×ˢ Icc (0 : ℝ) 1 = X ×ˢ Icc (0 : ℝ) (1 / 2) ∪ X ×ˢ Icc (1 / 2 : ℝ) 1 := by
      rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
    conv_lhs => rw [hX', image_union]
    rw [(hφf.mono (prod_mono hX subset_rfl)).image_eq,
      (hφg.mono (prod_mono hX subset_rfl)).image_eq, image_comp_prodMap_id_right,
      image_comp_prodMap_id_right, hs₀.image_eq, hs₁.image_eq, image_comp_prodMap_id_left]
  refine ⟨φ, u, hφcyl, hu, hφu, fun i => ?_, hφ0, fun i => ?_, ?_, fun i => ?_, ?_⟩
  · have hri : fourSpokeModelLeaf i ∈ spliceSquare :=
      (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1
    have hrσ : fourSpokeModelLeaf (σ i) ∈ spliceSquare :=
      (fourSpokeModelLeaf_mem_spliceSquareBoundary (σ i)).1
    refine hφcyl.eq_of_eq_top (hu.bijOn.mapsTo hri) hrσ ?_
    rw [← hφu _ hri, hφ0 _ hri, hφ1 _ hrσ, hhr (σ i), hσ i]
  · rw [hφ1 _ (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1, hhr i]
  · rw [hφ1 _ zero_mem_spliceSquare, eq_zero_of_image_segment_fourSpokeModelLeaf hhseg]
  · rw [hstrip _ (segment_fourSpokeModelLeaf_subset_spliceSquare i), hΦstrip i, hhseg i,
      biUnion_le_succ (fun k => G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ
        Icc (0 : ℝ) 1))]
  · rw [hstrip _ (singleton_subset_iff.mpr zero_mem_spliceSquare), hΦcore, image_singleton,
      eq_zero_of_image_segment_fourSpokeModelLeaf hhseg,
      biUnion_le_succ (fun k => G k '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1))]

end DifferentialGeometry.Topology.PiecewiseLinear
