/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSquareLoop

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem coneSet_inter_of_isRadiallyInjective {c : E} {S X Y : Set E}
    (hrad : IsRadiallyInjective c S) (hcS : c ∉ S) (hX : X ⊆ S) (hY : Y ⊆ S) :
    coneSet c X ∩ Y = X ∩ Y := by
  ext x
  constructor
  · rintro ⟨hx, hxY⟩
    rcases mem_coneSet_iff.mp hx with rfl | ⟨z, hz, s, hs, -, rfl⟩
    · exact absurd (hY hxY) hcS
    · have hzx := hrad z (hX hz) _ (hY hxY) s hs rfl
      rw [hzx] at hxY ⊢
      exact ⟨hz, hxY⟩
  · rintro ⟨hx, hxY⟩
    exact ⟨subset_coneSet c X hx, hxY⟩

theorem image_swap_segment_fourSpokeModelLeaf (i : Fin 4) :
    Prod.swap '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (fourSpokeFlipPerm i)) := by
  rw [image_swap_segment, swap_fourSpokeModelLeaf]
  rfl

theorem fourSpokeFlipPerm_flip (i : Fin 4) : fourSpokeFlipPerm (fourSpokeFlipPerm i) = i := by
  revert i
  decide

theorem exists_cylinder_of_markedCells {m : ℕ} (hm : 2 ≤ m) {c : ℕ → E}
    {K : ℕ → Geometry.SimplicialComplex ℝ E} (hKfin : ∀ k, (K k).faces.Finite)
    (hK : ∀ k, IsConeBase (c k) (K k)) (hS : ∀ k, IsPLSphere 2 (K k).space)
    {y₀ y₁ : ℕ → E} {T : ℕ → Fin 4 → Set E} {γ : ℕ → Fin 4 → ℝ → E}
    {q₀ q₁ : ℕ → (Fin 3 → ℝ) → E} {D₀ D₁ : ℕ → Set E}
    (hγ : ∀ k i, IsPLHomeomorphOn (γ k i) (Icc 0 1) (T k i)) (hγzero : ∀ k i, γ k i 0 = y₀ k)
    (hγone : ∀ k i, γ k i 1 = y₁ k) (hTS : ∀ k i, T k i ⊆ (K k).space)
    (hTT : ∀ k i j, i ≠ j → T k i ∩ T k j = {y₀ k, y₁ k})
    (hsep : ∀ k, ∀ i : Fin 4, ∀ U ⊆ (K k).space \ (T k i ∪ T k (i + 2)), IsPreconnected U →
      (U ∩ T k (i + 1)).Nonempty → (U ∩ T k (i + 3)).Nonempty → False)
    (hq₀ : ∀ k, IsPLHomeomorphOn (q₀ k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D₀ k))
    (hq₁ : ∀ k, IsPLHomeomorphOn (q₁ k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D₁ k))
    (hD₀S : ∀ k, D₀ k ⊆ (K k).space) (hD₁S : ∀ k, D₁ k ⊆ (K k).space)
    (hdis : ∀ k, Disjoint (D₀ k) (D₁ k))
    (hb₀ : ∀ k i, q₀ k '' stdSimplexBoundary 2 ∩ T k i = {γ k i (1 / 4)})
    (hb₁ : ∀ k i, q₁ k '' stdSimplexBoundary 2 ∩ T k i = {γ k i (3 / 4)})
    (hy₀ : ∀ k, y₀ k ∈ D₀ k) (hy₁ : ∀ k, y₁ k ∈ D₁ k)
    (hcap : ∀ k < m, D₁ k = D₀ (k + 1)) (hcapc : D₁ m = D₀ 0)
    (harm : ∀ k < m, ∀ i, T k i ∩ D₁ k = T (k + 1) i ∩ D₀ (k + 1))
    (harmc : ∀ i, T m i ∩ D₁ m = T 0 (fourSpokeFlipPerm i) ∩ D₀ 0)
    (hpt : ∀ k < m, ∀ i, γ k i (3 / 4) = γ (k + 1) i (1 / 4))
    (hptc : ∀ i, γ m i (3 / 4) = γ 0 (fourSpokeFlipPerm i) (1 / 4))
    (hadj : ∀ k < m,
      coneSet (c k) (K k).space ∩ coneSet (c (k + 1)) (K (k + 1)).space = D₁ k)
    (hadjc : coneSet (c m) (K m).space ∩ coneSet (c 0) (K 0).space = D₀ 0)
    (hfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) →
      Disjoint (coneSet (c j) (K j).space) (coneSet (c k) (K k).space)) :
    ∃ (φ : (ℝ × ℝ) × ℝ → E) (u : ℝ × ℝ → ℝ × ℝ),
      IsCylindricalDiagram φ spliceSquare (⋃ k ≤ m, coneSet (c k) (K k).space) ∧
      IsPLHomeomorphOn u spliceSquare spliceSquare ∧
      (∀ x ∈ spliceSquare, φ (x, 0) = φ (u x, 1)) ∧ u 0 = 0 ∧
      (∀ i, u (fourSpokeModelLeaf i) = fourSpokeModelLeaf (fourSpokeFlipPerm i)) ∧
      φ '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) = ⋃ k ≤ m, coneSet (c k) {y₀ k, y₁ k} ∧
      (∀ i, φ (fourSpokeModelLeaf i, 0) = γ 0 i (1 / 2)) ∧ φ (0, 0) = c 0 := by
  classical
  have hsq : IsPolyhedron spliceSquare := isHPolytope_spliceSquare.isPolyhedron
  have hMCL : ∀ k, ∃ G : (ℝ × ℝ) × ℝ → E,
      IsPLHomeomorphOn G (spliceSquare ×ˢ Icc (0 : ℝ) 1) (coneSet (c k) (K k).space) ∧
      G ((0 : ℝ × ℝ), (1 / 2 : ℝ)) = c k ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, G (tubeMeridianParam (fourSpokeModelLeaf i) t) = γ k i t) ∧
      (∀ i, G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        coneSet (c k) (T k i)) ∧
      G '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) = coneSet (c k) {y₀ k, y₁ k} ∧
      G '' (spliceSquare ×ˢ ({0} : Set ℝ)) = D₀ k ∧
      G '' (spliceSquare ×ˢ ({1} : Set ℝ)) = D₁ k := by
    intro k
    have : Finite (K k).faces := (hKfin k).to_subtype
    obtain ⟨G, hG, hGc, hGγ, hGstrip, hGcore, hG0, hG1, -⟩ :=
      exists_isPLHomeomorphOn_spliceCylinder_of_marked (hK k) (hS k) (hγ k) (hγzero k)
        (hγone k) (hTS k) (hTT k) (hsep k) (hq₀ k) (hq₁ k) (hD₀S k) (hD₁S k) (hdis k) (hb₀ k)
        (hb₁ k) (hy₀ k) (hy₁ k)
    exact ⟨G, hG, hGc, hGγ, hGstrip, hGcore, hG0, hG1⟩
  choose G hG hGc hGγ hGstrip hGcore hG0 hG1 using hMCL
  have hzero : (0 : ℝ × ℝ) ∈ spliceSquare := zero_mem_spliceSquare
  have hGbot : ∀ k i, G k (fourSpokeModelLeaf i, 0) = γ k i (1 / 4) := by
    intro k i
    rw [← tubeMeridianParam_quarter]
    exact hGγ k i _ ⟨by norm_num, by norm_num⟩
  have hGtop : ∀ k i, G k (fourSpokeModelLeaf i, 1) = γ k i (3 / 4) := by
    intro k i
    rw [← tubeMeridianParam_threeQuarter]
    exact hGγ k i _ ⟨by norm_num, by norm_num⟩
  have hGmid : ∀ k i, G k (fourSpokeModelLeaf i, 1 / 2) = γ k i (1 / 2) := by
    intro k i
    rw [← tubeMeridianParam_half]
    exact hGγ k i _ ⟨by norm_num, by norm_num⟩
  have hsegsub : ∀ i, segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ⊆ spliceSquare :=
    segment_fourSpokeModelLeaf_subset_spliceSquare
  have hGarm : ∀ k i (a : ℝ), a ∈ Icc (0 : ℝ) 1 → G k '' (spliceSquare ×ˢ ({a} : Set ℝ)) ⊆
      (K k).space →
      G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({a} : Set ℝ)) =
        T k i ∩ G k '' (spliceSquare ×ˢ ({a} : Set ℝ)) := by
    intro k i a ha hsub
    have hlev : segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({a} : Set ℝ) =
        segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1 ∩
          spliceSquare ×ˢ ({a} : Set ℝ) := by
      rw [prod_inter_prod, inter_eq_left.mpr (hsegsub i),
        inter_eq_right.mpr (singleton_subset_iff.mpr ha)]
    rw [hlev, (hG k).bijOn.injOn.image_inter (prod_mono (hsegsub i) subset_rfl)
      (prod_mono subset_rfl (singleton_subset_iff.mpr ha)), hGstrip k i]
    exact coneSet_inter_of_isRadiallyInjective (hK k).radial (hK k).notMem_space (hTS k i) hsub
  have hGarm0 : ∀ k i, G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)) =
      T k i ∩ D₀ k := by
    intro k i
    rw [hGarm k i 0 ⟨le_rfl, zero_le_one⟩ (by rw [hG0 k]; exact hD₀S k), hG0 k]
  have hGarm1 : ∀ k i, G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
      T k i ∩ D₁ k := by
    intro k i
    rw [hGarm k i 1 ⟨zero_le_one, le_rfl⟩ (by rw [hG1 k]; exact hD₁S k), hG1 k]
  have hs₁ : IsPLHomeomorphOn (fun t : ℝ => 1 / 2 * t + 1 / 2) (Icc 0 1) (Icc (1 / 2) 1) :=
    isPLHomeomorphOn_mul_add_Icc (by norm_num) (by norm_num) (by norm_num)
  have hs₀ : IsPLHomeomorphOn (fun t : ℝ => 1 / 2 * t + 0) (Icc 0 1) (Icc 0 (1 / 2)) :=
    isPLHomeomorphOn_mul_add_Icc (by norm_num) (by norm_num) (by norm_num)
  have hup : IsPLHomeomorphOn (G 0 ∘ Prod.map id fun t : ℝ => 1 / 2 * t + 1 / 2)
      (spliceSquare ×ˢ Icc (0 : ℝ) 1) (G 0 '' (spliceSquare ×ˢ Icc (1 / 2 : ℝ) 1)) :=
    (hsq.isPLHomeomorphOn_id.prodMap hs₁).trans ((hG 0).restrict
      (hsq.prod isHPolytope_Icc.isPolyhedron) (prod_mono subset_rfl
        (Icc_subset_Icc (by norm_num) le_rfl)))
  have hlow : IsPLHomeomorphOn (G 0 ∘ Prod.map Prod.swap fun t : ℝ => 1 / 2 * t + 0)
      (spliceSquare ×ˢ Icc (0 : ℝ) 1) (G 0 '' (spliceSquare ×ˢ Icc (0 : ℝ) (1 / 2))) := by
    have h := (isPLHomeomorphOn_swap_spliceSquare.prodMap hs₀).trans ((hG 0).restrict
      (hsq.prod isHPolytope_Icc.isPolyhedron) (prod_mono subset_rfl
        (Icc_subset_Icc le_rfl (by norm_num))))
    exact h
  have himgUp : ∀ (X : Set (ℝ × ℝ)) (Y : Set ℝ),
      (G 0 ∘ Prod.map id fun t : ℝ => 1 / 2 * t + 1 / 2) '' (X ×ˢ Y) =
        G 0 '' (X ×ˢ ((fun t : ℝ => 1 / 2 * t + 1 / 2) '' Y)) :=
    fun X Y => image_comp_prodMap_id_right _ _ X Y
  have himgLow : ∀ (X : Set (ℝ × ℝ)) (Y : Set ℝ),
      (G 0 ∘ Prod.map Prod.swap fun t : ℝ => 1 / 2 * t + 0) '' (X ×ˢ Y) =
        G 0 '' ((Prod.swap '' X) ×ˢ ((fun t : ℝ => 1 / 2 * t + 0) '' Y)) := by
    intro X Y
    rw [image_comp, prodMap_image_prod]
  have hsUp0 : (fun t : ℝ => 1 / 2 * t + 1 / 2) '' {0} = {1 / 2} := by
    rw [image_singleton]
    norm_num
  have hsUp1 : (fun t : ℝ => 1 / 2 * t + 1 / 2) '' {1} = {1} := by
    rw [image_singleton]
    norm_num
  have hsLow0 : (fun t : ℝ => 1 / 2 * t + 0) '' {0} = {0} := by
    rw [image_singleton]
    norm_num
  have hsLow1 : (fun t : ℝ => 1 / 2 * t + 0) '' {1} = {1 / 2} := by
    rw [image_singleton]
    norm_num
  let G' : ℕ → (ℝ × ℝ) × ℝ → E := fun k =>
    if k = 0 then G 0 ∘ Prod.map id fun t : ℝ => 1 / 2 * t + 1 / 2
    else if k = m + 1 then G 0 ∘ Prod.map Prod.swap fun t : ℝ => 1 / 2 * t + 0 else G k
  let B' : ℕ → Set E := fun k =>
    if k = 0 then G 0 '' (spliceSquare ×ˢ Icc (1 / 2 : ℝ) 1)
    else if k = m + 1 then G 0 '' (spliceSquare ×ˢ Icc (0 : ℝ) (1 / 2))
    else coneSet (c k) (K k).space
  have hG'0 : G' 0 = G 0 ∘ Prod.map id fun t : ℝ => 1 / 2 * t + 1 / 2 := ite_eq_left rfl
  have hG'L : G' (m + 1) = G 0 ∘ Prod.map Prod.swap fun t : ℝ => 1 / 2 * t + 0 := by
    change (if m + 1 = 0 then _ else if m + 1 = m + 1 then _ else _) = _
    rw [ite_eq_right (Nat.succ_ne_zero m), ite_eq_left rfl]
  have hG'k : ∀ k, k ≠ 0 → k ≠ m + 1 → G' k = G k := by
    intro k h0 h1
    change (if k = 0 then _ else if k = m + 1 then _ else _) = _
    rw [ite_eq_right h0, ite_eq_right h1]
  have hB'0 : B' 0 = G 0 '' (spliceSquare ×ˢ Icc (1 / 2 : ℝ) 1) := ite_eq_left rfl
  have hB'L : B' (m + 1) = G 0 '' (spliceSquare ×ˢ Icc (0 : ℝ) (1 / 2)) := by
    change (if m + 1 = 0 then _ else if m + 1 = m + 1 then _ else _) = _
    rw [ite_eq_right (Nat.succ_ne_zero m), ite_eq_left rfl]
  have hB'k : ∀ k, k ≠ 0 → k ≠ m + 1 → B' k = coneSet (c k) (K k).space := by
    intro k h0 h1
    change (if k = 0 then _ else if k = m + 1 then _ else _) = _
    rw [ite_eq_right h0, ite_eq_right h1]
  have hUsub : G 0 '' (spliceSquare ×ˢ Icc (1 / 2 : ℝ) 1) ⊆ coneSet (c 0) (K 0).space := by
    rw [← (hG 0).image_eq]
    exact image_mono (prod_mono subset_rfl (Icc_subset_Icc (by norm_num) le_rfl))
  have hLsub : G 0 '' (spliceSquare ×ˢ Icc (0 : ℝ) (1 / 2)) ⊆ coneSet (c 0) (K 0).space := by
    rw [← (hG 0).image_eq]
    exact image_mono (prod_mono subset_rfl (Icc_subset_Icc le_rfl (by norm_num)))
  have hGdisj : ∀ (Y Z : Set ℝ), Y ⊆ Icc (0 : ℝ) 1 → Z ⊆ Icc (0 : ℝ) 1 → Disjoint Y Z →
      Disjoint (G 0 '' (spliceSquare ×ˢ Y)) (G 0 '' (spliceSquare ×ˢ Z)) := by
    intro Y Z hY hZ hYZ
    rw [disjoint_iff_inter_eq_empty, ← (hG 0).bijOn.injOn.image_inter
      (prod_mono subset_rfl hY) (prod_mono subset_rfl hZ), prod_inter_prod, hYZ.inter_eq,
      prod_empty, image_empty]
  have hsw0 : Prod.swap (0 : ℝ × ℝ) = 0 := rfl
  have hcone_sub : ∀ k (X : Set E), X ⊆ (K k).space → X ⊆ coneSet (c k) (K k).space :=
    fun k X hX => hX.trans (subset_coneSet _ _)
  have hG' : ∀ k ≤ m + 1, IsPLHomeomorphOn (G' k) (spliceSquare ×ˢ Icc (0 : ℝ) 1) (B' k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hG'0, hB'0]
      exact hup
    · rcases eq_or_lt_of_le hk with rfl | hk1
      · rw [hG'L, hB'L]
        exact hlow
      · rw [hG'k k hk0.ne' hk1.ne, hB'k k hk0.ne' hk1.ne]
        exact hG k
  have hcap' : ∀ k ≤ m, G' k '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G' (k + 1) '' (spliceSquare ×ˢ ({0} : Set ℝ)) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hG'0, himgUp, hsUp1, hG1, zero_add, hG'k 1 one_ne_zero (by omega), hG0,
        hcap 0 (by omega)]
    · rcases eq_or_lt_of_le hk with rfl | hk1
      · rw [hG'k k hk0.ne' (by omega), hG1, hcapc, hG'L, himgLow, image_swap_spliceSquare,
          hsLow0, hG0]
      · rw [hG'k k hk0.ne' (by omega), hG'k (k + 1) (by omega) (by omega), hG1, hG0,
          hcap k hk1]
  have harm' : ∀ k ≤ m, ∀ i,
      G' k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
        G' (k + 1) '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)) := by
    intro k hk i
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hG'0, himgUp, hsUp1, hGarm1, zero_add, hG'k 1 one_ne_zero (by omega), hGarm0,
        harm 0 (by omega)]
    · rcases eq_or_lt_of_le hk with rfl | hk1
      · rw [hG'k k hk0.ne' (by omega), hGarm1, harmc, hG'L, himgLow,
          image_swap_segment_fourSpokeModelLeaf, hsLow0, hGarm0]
      · rw [hG'k k hk0.ne' (by omega), hG'k (k + 1) (by omega) (by omega), hGarm1, hGarm0,
          harm k hk1]
  have hpt' : ∀ k ≤ m, ∀ i,
      G' k (fourSpokeModelLeaf i, 1) = G' (k + 1) (fourSpokeModelLeaf i, 0) := by
    intro k hk i
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hG'0, zero_add, hG'k 1 one_ne_zero (by omega)]
      change G 0 (fourSpokeModelLeaf i, 1 / 2 * 1 + 1 / 2) = _
      rw [show (1 : ℝ) / 2 * 1 + 1 / 2 = 1 by norm_num, hGtop, hpt 0 (by omega), hGbot]
    · rcases eq_or_lt_of_le hk with rfl | hk1
      · rw [hG'k k hk0.ne' (by omega), hG'L, hGtop, hptc]
        change _ = G 0 (Prod.swap (fourSpokeModelLeaf i), 1 / 2 * 0 + 0)
        rw [swap_fourSpokeModelLeaf, show (1 : ℝ) / 2 * 0 + 0 = 0 by norm_num, hGbot]
      · rw [hG'k k hk0.ne' (by omega), hG'k (k + 1) (by omega) (by omega), hGtop, hGbot,
          hpt k hk1]
  have hadj' : ∀ k < m, B' k ∩ B' (k + 1) = G' k '' (spliceSquare ×ˢ ({1} : Set ℝ)) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hB'0, zero_add, hB'k 1 one_ne_zero (by omega), hG'0, himgUp, hsUp1, hG1]
      apply Subset.antisymm
      · rw [← hadj 0 hk, zero_add]
        exact inter_subset_inter_left _ hUsub
      · refine subset_inter ?_ ?_
        · rw [← hG1]
          exact image_mono (prod_mono subset_rfl (singleton_subset_iff.mpr ⟨by norm_num, le_rfl⟩))
        · rw [hcap 0 hk]
          exact hcone_sub 1 _ (hD₀S 1)
    · rw [hB'k k hk0.ne' (by omega), hB'k (k + 1) (by omega) (by omega),
        hG'k k hk0.ne' (by omega), hG1, hadj k hk]
  have hfar' : ∀ j k, j + 1 < k → k ≤ m → Disjoint (B' j) (B' k) := by
    intro j k hjk hk
    rw [hB'k k (by omega) (by omega)]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hB'0]
      rcases eq_or_lt_of_le hk with hkm | hk1
      · rw [disjoint_left]
        intro x hxU hxm
        have hx0 : x ∈ D₀ 0 := by
          rw [← hadjc]
          exact ⟨hkm ▸ hxm, hUsub hxU⟩
        rw [← hG0] at hx0
        exact disjoint_left.mp (hGdisj _ _ (Icc_subset_Icc (by norm_num) le_rfl)
          (singleton_subset_iff.mpr ⟨le_rfl, zero_le_one⟩)
          (disjoint_singleton_right.mpr fun h => by norm_num at h)) hxU hx0
      · exact (hfar 0 k hjk hk (Or.inr hk1.ne)).mono_left hUsub
    · rw [hB'k j hj0.ne' (by omega)]
      exact hfar j k hjk hk (Or.inl hj0.ne')
  have hlast' : (⋃ k ≤ m, B' k) ∩ B' (m + 1) = G' 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)) ∪
      G' m '' (spliceSquare ×ˢ ({1} : Set ℝ)) := by
    rw [hB'L, hG'0, himgUp, hsUp0, hG'k m (by omega) (by omega), hG1, hcapc]
    apply Subset.antisymm
    · rintro x ⟨hx, hxL⟩
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [hB'0] at hxk
        left
        have hmem : x ∈ G 0 '' (spliceSquare ×ˢ Icc (1 / 2 : ℝ) 1) ∩
            G 0 '' (spliceSquare ×ˢ Icc (0 : ℝ) (1 / 2)) := ⟨hxk, hxL⟩
        rw [← (hG 0).bijOn.injOn.image_inter
          (prod_mono subset_rfl (Icc_subset_Icc (by norm_num) le_rfl))
          (prod_mono subset_rfl (Icc_subset_Icc le_rfl (by norm_num))), prod_inter_prod,
          inter_self, Icc_inter_Icc, max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2),
          min_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 1), Icc_self] at hmem
        exact hmem
      · rw [hB'k k hk0.ne' (by omega)] at hxk
        rcases eq_or_lt_of_le hk with rfl | hk1
        · right
          rw [← hadjc]
          exact ⟨hxk, hLsub hxL⟩
        · exfalso
          rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hk0.ne') with h1 | h1
          · subst h1
            have hmem : x ∈ coneSet (c 0) (K 0).space ∩ coneSet (c (0 + 1)) (K (0 + 1)).space :=
              ⟨hLsub hxL, hxk⟩
            rw [hadj 0 (by omega), ← hG1] at hmem
            exact disjoint_left.mp (hGdisj _ _ (Icc_subset_Icc le_rfl (by norm_num))
              (singleton_subset_iff.mpr ⟨zero_le_one, le_rfl⟩)
              (disjoint_singleton_right.mpr fun h => by norm_num at h)) hxL hmem
          · exact disjoint_left.mp (hfar 0 k (by omega) hk (Or.inr hk1.ne)) (hLsub hxL) hxk
    · rintro x (hx | hx)
      · refine ⟨mem_iUnion₂.mpr ⟨0, Nat.zero_le _, ?_⟩, ?_⟩
        · rw [hB'0]
          exact image_mono (prod_mono subset_rfl (singleton_subset_iff.mpr
            (show (1 / 2 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 from ⟨le_rfl, by norm_num⟩))) hx
        · exact image_mono (prod_mono subset_rfl (singleton_subset_iff.mpr
            (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) from ⟨by norm_num, le_rfl⟩))) hx
      · refine ⟨mem_iUnion₂.mpr ⟨m, le_rfl, ?_⟩, ?_⟩
        · rw [hB'k m (by omega) (by omega)]
          rw [← hcapc] at hx
          exact hcone_sub m _ (hD₁S m) hx
        · rw [← hG0] at hx
          exact image_mono (prod_mono subset_rfl (singleton_subset_iff.mpr
            (show (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) from ⟨le_rfl, by norm_num⟩))) hx
  have hclose' : G' (m + 1) '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G' 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)) := by
    rw [hG'L, himgLow, image_swap_spliceSquare, hsLow1, hG'0, himgUp, hsUp0]
  have hσ' : ∀ i, G' (m + 1) (fourSpokeModelLeaf (fourSpokeFlipPerm i), 1) =
      G' 0 (fourSpokeModelLeaf i, 0) := by
    intro i
    rw [hG'L, hG'0]
    change G 0 (Prod.swap (fourSpokeModelLeaf (fourSpokeFlipPerm i)), 1 / 2 * 1 + 0) =
      G 0 (fourSpokeModelLeaf i, 1 / 2 * 0 + 1 / 2)
    rw [swap_fourSpokeModelLeaf, fourSpokeFlipPerm_flip]
    norm_num
  obtain ⟨φ, u, hφcyl, hu, hφu, huσ, hφ0, -, hφ01, -, hφcore⟩ :=
    exists_isCylindricalDiagram_spliceSquare_of_chain m hG' hcap' harm' hpt' hadj' hfar' hlast'
      hclose' hσ'
  have hunion : (⋃ k ≤ m + 1, B' k) = ⋃ k ≤ m, coneSet (c k) (K k).space := by
    rw [biUnion_le_succ, hB'L]
    apply Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [hB'0] at hxk
          exact mem_iUnion₂.mpr ⟨0, Nat.zero_le _, hUsub hxk⟩
        · rw [hB'k k hk0.ne' (by omega)] at hxk
          exact mem_iUnion₂.mpr ⟨k, hk, hxk⟩
      · exact mem_iUnion₂.mpr ⟨0, Nat.zero_le _, hLsub hx⟩
    · intro x hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [← (hG 0).image_eq] at hxk
        have hsplit : spliceSquare ×ˢ Icc (0 : ℝ) 1 = spliceSquare ×ˢ Icc (1 / 2 : ℝ) 1 ∪
            spliceSquare ×ˢ Icc (0 : ℝ) (1 / 2) := by
          rw [← prod_union, union_comm, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
        rw [hsplit, image_union] at hxk
        rcases hxk with hxk | hxk
        · refine Or.inl (mem_iUnion₂.mpr ⟨0, Nat.zero_le _, ?_⟩)
          rw [hB'0]
          exact hxk
        · exact Or.inr hxk
      · refine Or.inl (mem_iUnion₂.mpr ⟨k, hk, ?_⟩)
        rw [hB'k k hk0.ne' (by omega)]
        exact hxk
  rw [hunion] at hφcyl
  refine ⟨φ, u, hφcyl, hu, hφu, ?_, huσ, ?_, fun i => ?_, ?_⟩
  · apply hφcyl.eq_of_eq_top (hu.bijOn.mapsTo hzero) hzero
    rw [← hφu 0 hzero, hφ0 0 hzero, hφ01, hG'0, hG'L]
    change G 0 (0, 1 / 2 * 0 + 1 / 2) = G 0 (Prod.swap 0, 1 / 2 * 1 + 0)
    rw [hsw0]
    norm_num
  · rw [hφcore, biUnion_le_succ, hG'L]
    apply Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [hG'0, himgUp] at hxk
          refine mem_iUnion₂.mpr ⟨0, Nat.zero_le _, ?_⟩
          rw [← hGcore 0]
          exact image_mono (prod_mono subset_rfl (hs₁.bijOn.mapsTo.image_subset.trans
            (Icc_subset_Icc (by norm_num) le_rfl))) hxk
        · rw [hG'k k hk0.ne' (by omega), hGcore] at hxk
          exact mem_iUnion₂.mpr ⟨k, hk, hxk⟩
      · rw [himgLow, image_singleton, hsw0] at hx
        refine mem_iUnion₂.mpr ⟨0, Nat.zero_le _, ?_⟩
        rw [← hGcore 0]
        exact image_mono (prod_mono subset_rfl (hs₀.bijOn.mapsTo.image_subset.trans
          (Icc_subset_Icc le_rfl (by norm_num)))) hx
    · intro x hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [← hGcore 0] at hxk
        have hsplit : ({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1 =
            ({0} : Set (ℝ × ℝ)) ×ˢ Icc (1 / 2 : ℝ) 1 ∪
              ({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) (1 / 2) := by
          rw [← prod_union, union_comm, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
        rw [hsplit, image_union] at hxk
        rcases hxk with hxk | hxk
        · refine Or.inl (mem_iUnion₂.mpr ⟨0, Nat.zero_le _, ?_⟩)
          rw [hG'0, himgUp, hs₁.image_eq]
          exact hxk
        · right
          rw [himgLow, image_singleton, hsw0, hs₀.image_eq]
          exact hxk
      · refine Or.inl (mem_iUnion₂.mpr ⟨k, hk, ?_⟩)
        rw [hG'k k hk0.ne' (by omega), hGcore]
        exact hxk
  · rw [hφ0 _ (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1, hG'0]
    change G 0 (fourSpokeModelLeaf i, 1 / 2 * 0 + 1 / 2) = _
    rw [show (1 : ℝ) / 2 * 0 + 1 / 2 = 1 / 2 by norm_num, hGmid]
  · rw [hφ0 0 hzero, hG'0]
    change G 0 (0, 1 / 2 * 0 + 1 / 2) = _
    rw [show (1 : ℝ) / 2 * 0 + 1 / 2 = 1 / 2 by norm_num]
    exact hGc 0

end DifferentialGeometry.Topology.PiecewiseLinear
