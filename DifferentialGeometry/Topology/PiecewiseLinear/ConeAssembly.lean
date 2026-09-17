import DifferentialGeometry.Topology.PiecewiseLinear.ConeLayerMap

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem inter_stdConeLayer_subset_edge {σ' σ : ℝ} :
    stdConeLayer 0 σ' ∩ stdConeLayer σ' σ ⊆ {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 = σ'} := by
  rintro z ⟨⟨h1, h2, -, h4⟩, ⟨-, -, h5, -⟩⟩
  exact ⟨h1, h2, le_antisymm h4 h5⟩

theorem mem_stdConeLayerLow_bottom {p q t : ℝ} (hp : 0 ≤ p) (ht : t ∈ Icc p q) :
    ((t, 0) : ℝ × ℝ) ∈ stdConeLayerLow p q := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨le_trans hp h1, le_rfl, by simpa using h1, by simpa using h2, ?_⟩
  simp only
  nlinarith

theorem mem_stdConeLayerHigh_left {p q t : ℝ} (hp : 0 ≤ p) (hq : p ≤ q) (ht : t ∈ Icc p q) :
    ((0, t) : ℝ × ℝ) ∈ stdConeLayerHigh p q := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨le_rfl, le_trans hp h1, by simpa using h1, by simpa using h2, ?_⟩
  simp only
  nlinarith

open Classical in
theorem exists_isPiecewiseAffineOn_stdCone_of_layers {N : ℕ} {σ : ℕ → ℝ} (A B : ℕ → F)
    (hσ0 : σ 0 = 0) (hσN : σ (N + 1) = 1) (hmono : ∀ k ≤ N, σ k < σ (k + 1))
    (hAB : A 0 = B 0) :
    ∃ Ψ : ℝ × ℝ → F, IsPiecewiseAffineOn Ψ stdCone ∧ Ψ (0, 0) = A 0 ∧
      EqOn Ψ (centralConeMap 1 0 (A (N + 1)) (B (N + 1)))
        {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 = 1} ∧
      (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
        Ψ (t, 0) = AffineMap.lineMap (A k) (A (k + 1)) ((t - σ k) / (σ (k + 1) - σ k))) ∧
      (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
        Ψ (0, t) = AffineMap.lineMap (B k) (B (k + 1)) ((t - σ k) / (σ (k + 1) - σ k))) ∧
      ∀ z ∈ stdCone, ∃ k ≤ N, Ψ z ∈ convexHull ℝ ({A k, B k, A (k + 1), B (k + 1)} : Set F) := by
  classical
  have hchain := le_of_chain (fun k hk => (hmono k hk).le)
  have hσnn : ∀ k ≤ N + 1, 0 ≤ σ k := by
    intro k hk
    have h := hchain k hk 0 (Nat.zero_le _)
    rwa [hσ0] at h
  have hpos : ∀ k ≤ N, 0 < σ (k + 1) :=
    fun k hk => lt_of_le_of_lt (hσnn k (by omega)) (hmono k hk)
  have hle : ∀ k ≤ N + 1, σ k ≤ 1 := by
    intro k hk
    have h := hchain (N + 1) le_rfl k hk
    rwa [hσN] at h
  have hsub : ∀ a b c d : F, convexHull ℝ ({a, c, d} : Set F) ⊆
      convexHull ℝ ({a, b, c, d} : Set F) := by
    intro a b c d
    refine convexHull_mono ?_
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢
    tauto
  have hsubL : ∀ a b c d : F, convexHull ℝ ({a, b, c} : Set F) ⊆
      convexHull ℝ ({a, b, c, d} : Set F) := by
    intro a b c d
    refine convexHull_mono ?_
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢
    tauto
  have hsub' : ∀ a b c d : F, convexHull ℝ ({b, c, d} : Set F) ⊆
      convexHull ℝ ({a, b, c, d} : Set F) := by
    intro a b c d
    refine convexHull_mono ?_
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢
    tauto
  have key : ∀ k, k ≤ N → ∃ Ψ : ℝ × ℝ → F,
      IsPiecewiseAffineOn Ψ (stdConeLayer 0 (σ (k + 1))) ∧ Ψ (0, 0) = A 0 ∧
      EqOn Ψ (centralConeMap (σ (k + 1)) 0 (A (k + 1)) (B (k + 1)))
        {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 = σ (k + 1)} ∧
      (∀ j ≤ k, ∀ t ∈ Icc (σ j) (σ (j + 1)),
        Ψ (t, 0) = AffineMap.lineMap (A j) (A (j + 1)) ((t - σ j) / (σ (j + 1) - σ j))) ∧
      (∀ j ≤ k, ∀ t ∈ Icc (σ j) (σ (j + 1)),
        Ψ (0, t) = AffineMap.lineMap (B j) (B (j + 1)) ((t - σ j) / (σ (j + 1) - σ j))) ∧
      ∀ z ∈ stdConeLayer 0 (σ (k + 1)), ∃ j ≤ k,
        Ψ z ∈ convexHull ℝ ({A j, B j, A (j + 1), B (j + 1)} : Set F) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hs : σ 1 ≠ 0 := ne_of_gt (hpos 0 hk)
      refine ⟨centralConeMap (σ 1) (A 0) (A 1) (B 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact isPiecewiseAffineOn_of_affine_of_isHPolytope _
          (isHPolytope_stdConeLayer (hle 1 (by omega)))
      · exact centralConeMap_apex _ _ _ _
      · exact eqOn_central_central (hpos 0 hk) _ _ _
      · intro j hj t _
        have hj0 : j = 0 := by omega
        subst hj0
        rw [centralConeMap, affineOfCoeffs_apply, coeffLin_apply, coeffLin_apply,
          AffineMap.lineMap_apply_module, hσ0]
        match_scalars <;> field_simp <;> ring
      · intro j hj t _
        have hj0 : j = 0 := by omega
        subst hj0
        rw [centralConeMap, affineOfCoeffs_apply, coeffLin_apply, coeffLin_apply,
          AffineMap.lineMap_apply_module, hσ0, ← hAB]
        match_scalars <;> field_simp <;> ring
      · intro z hz
        exact ⟨0, le_rfl, hsub (A 0) (B 0) (A 1) (B 1)
          (centralConeMap_mem_convexHull (hpos 0 hk) _ _ _ hz)⟩
    | succ k ih =>
      intro hk
      obtain ⟨Ψ, hPA, hapex, hedge, hbot, hleft, himg⟩ := ih (by omega)
      obtain ⟨Φ, hΦPA, hΦlow, hΦhigh⟩ :=
        exists_isPiecewiseAffineOn_layer (hpos k (by omega)) (hmono (k + 1) hk)
          (hle (k + 1 + 1) (by omega)) (A (k + 1)) (B (k + 1)) (A (k + 1 + 1)) (B (k + 1 + 1))
      have hcompat : EqOn Ψ Φ (stdConeLayer 0 (σ (k + 1)) ∩
          stdConeLayer (σ (k + 1)) (σ (k + 1 + 1))) := by
        intro z hz
        have hzedge := inter_stdConeLayer_subset_edge hz
        rw [hedge hzedge, hΦlow (inner_edge_subset_low (hpos k (by omega))
          (hmono (k + 1) hk).le hzedge)]
        exact (eqOn_layerLow_central (hpos k (by omega)) (hmono (k + 1) hk) _ _ _ hzedge).symm
      have hΦval : ∀ z ∈ stdConeLayer (σ (k + 1)) (σ (k + 1 + 1)),
          (stdConeLayer 0 (σ (k + 1))).piecewise Ψ Φ z = Φ z := by
        intro z hz
        by_cases hmem : z ∈ stdConeLayer 0 (σ (k + 1))
        · rw [piecewise_eq_of_mem _ _ _ hmem]
          exact hcompat ⟨hmem, hz⟩
        · exact piecewise_eq_of_notMem _ _ _ hmem
      refine ⟨(stdConeLayer 0 (σ (k + 1))).piecewise Ψ Φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← stdConeLayer_union_consecutive (hmono (k + 1) hk).le]
        exact hPA.piecewise_of_isClosed hΦPA
          (isHPolytope_stdConeLayer (hle (k + 1) (by omega))).isClosed
          (isHPolytope_stdConeLayer (hle (k + 1 + 1) (by omega))).isClosed hcompat
      · have h00 : ((0, 0) : ℝ × ℝ) ∈ stdConeLayer 0 (σ (k + 1)) := by
          refine ⟨le_rfl, le_rfl, by norm_num, ?_⟩
          simpa using (hpos k (by omega)).le
        rw [piecewise_eq_of_mem _ _ _ h00]
        exact hapex
      · rintro z ⟨hz1, hz2, hz3⟩
        have hznot : z ∉ stdConeLayer 0 (σ (k + 1)) := by
          rintro ⟨-, -, -, h4⟩
          rw [hz3] at h4
          exact absurd h4 (not_le.mpr (hmono (k + 1) hk))
        rw [piecewise_eq_of_notMem _ _ _ hznot,
          hΦhigh (outer_edge_subset_high (hpos k (by omega)).le (hmono (k + 1) hk).le
            ⟨hz1, hz2, hz3⟩)]
        exact eqOn_layerHigh_central (hpos k (by omega)) (hmono (k + 1) hk) _ _ _
          ⟨hz1, hz2, hz3⟩
      · intro j hj t ht
        rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
        · have hmem : ((t, 0) : ℝ × ℝ) ∈ stdConeLayer 0 (σ (k + 1)) :=
            ⟨le_trans (hσnn j (by omega)) ht.1, le_rfl,
              by simpa using le_trans (hσnn j (by omega)) ht.1,
              by simpa using le_trans ht.2 (hchain (k + 1) (by omega) (j + 1) (by omega))⟩
          rw [piecewise_eq_of_mem _ _ _ hmem]
          exact hbot j (by omega) t ht
        · have hj1 : j = k + 1 := by omega
          subst hj1
          have hlow : ((t, 0) : ℝ × ℝ) ∈ stdConeLayerLow (σ (k + 1)) (σ (k + 1 + 1)) :=
            mem_stdConeLayerLow_bottom (hσnn (k + 1) (by omega)) ht
          have hmem : ((t, 0) : ℝ × ℝ) ∈ stdConeLayer (σ (k + 1)) (σ (k + 1 + 1)) := by
            rw [← stdConeLayer_union_split]
            exact Or.inl hlow
          have hd : σ (k + 1 + 1) - σ (k + 1) ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hmono (k + 1) hk))
          have hs2 : σ (k + 1) ≠ 0 := ne_of_gt (hpos k (by omega))
          have hs : σ (k + 1 + 1) ≠ 0 := ne_of_gt (hpos (k + 1) hk)
          rw [hΦval _ hmem, hΦlow hlow, layerLowMap, affineOfCoeffs_apply, coeffLin_apply,
            coeffLin_apply, AffineMap.lineMap_apply_module]
          match_scalars <;> field_simp <;> ring
      · intro j hj t ht
        rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
        · have hmem : ((0, t) : ℝ × ℝ) ∈ stdConeLayer 0 (σ (k + 1)) :=
            ⟨le_rfl, le_trans (hσnn j (by omega)) ht.1,
              by simpa using le_trans (hσnn j (by omega)) ht.1,
              by simpa using le_trans ht.2 (hchain (k + 1) (by omega) (j + 1) (by omega))⟩
          rw [piecewise_eq_of_mem _ _ _ hmem]
          exact hleft j (by omega) t ht
        · have hj1 : j = k + 1 := by omega
          subst hj1
          have hhigh : ((0, t) : ℝ × ℝ) ∈ stdConeLayerHigh (σ (k + 1)) (σ (k + 1 + 1)) :=
            mem_stdConeLayerHigh_left (hσnn (k + 1) (by omega)) (hmono (k + 1) hk).le ht
          have hmem : ((0, t) : ℝ × ℝ) ∈ stdConeLayer (σ (k + 1)) (σ (k + 1 + 1)) := by
            rw [← stdConeLayer_union_split]
            exact Or.inr hhigh
          have hd : σ (k + 1 + 1) - σ (k + 1) ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hmono (k + 1) hk))
          have hs2 : σ (k + 1) ≠ 0 := ne_of_gt (hpos k (by omega))
          have hs : σ (k + 1 + 1) ≠ 0 := ne_of_gt (hpos (k + 1) hk)
          rw [hΦval _ hmem, hΦhigh hhigh, layerHighMap, affineOfCoeffs_apply, coeffLin_apply,
            coeffLin_apply, AffineMap.lineMap_apply_module]
          match_scalars <;> field_simp <;> ring
      · rintro z ⟨hz1, hz2, -, hz4⟩
        by_cases hzP : z ∈ stdConeLayer 0 (σ (k + 1))
        · obtain ⟨j, hj, hjmem⟩ := himg z hzP
          refine ⟨j, by omega, ?_⟩
          rwa [piecewise_eq_of_mem _ _ _ hzP]
        · have hzQ : z ∈ stdConeLayer (σ (k + 1)) (σ (k + 1 + 1)) :=
            ⟨hz1, hz2, not_lt.mp (fun hlt => hzP ⟨hz1, hz2, by linarith, hlt.le⟩), hz4⟩
          have hzu : z ∈ stdConeLayerLow (σ (k + 1)) (σ (k + 1 + 1)) ∪
              stdConeLayerHigh (σ (k + 1)) (σ (k + 1 + 1)) := by
            rw [stdConeLayer_union_split]
            exact hzQ
          rw [piecewise_eq_of_notMem _ _ _ hzP]
          refine ⟨k + 1, le_rfl, ?_⟩
          rcases hzu with hl | hh
          · rw [hΦlow hl]
            exact hsubL _ _ _ (B (k + 1 + 1)) (layerLowMap_mem_convexHull (hpos k (by omega))
              (hmono (k + 1) hk) _ _ _ hl)
          · rw [hΦhigh hh]
            exact hsub' (A (k + 1)) _ _ _ (layerHighMap_mem_convexHull (hpos k (by omega))
              (hmono (k + 1) hk) _ _ _ hh)
  obtain ⟨Ψ, hPA, hapex, hedge, hbot, hleft, himg⟩ := key N le_rfl
  rw [hσN] at hedge
  rw [hσN, stdConeLayer_zero_one] at hPA himg
  exact ⟨Ψ, hPA, hapex, hedge, hbot, hleft, himg⟩

end DifferentialGeometry.Topology.PiecewiseLinear
