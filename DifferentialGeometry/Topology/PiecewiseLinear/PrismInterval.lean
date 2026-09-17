import DifferentialGeometry.Topology.PiecewiseLinear.PrismMap
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def verticalPrismAffine (a c : F) : (ℝ × ℝ) →ᵃ[ℝ] F :=
  AffineMap.const ℝ (ℝ × ℝ) a + ((LinearMap.snd ℝ ℝ ℝ).smulRight (c - a)).toAffineMap

theorem verticalPrismAffine_apply (a c : F) (z : ℝ × ℝ) :
    verticalPrismAffine a c z = a + z.2 • (c - a) := by
  simp [verticalPrismAffine]

theorem verticalPrismAffine_mem_convexHull (a c : F) {z : ℝ × ℝ} (hz : z.2 ∈ Icc (0 : ℝ) 1)
    (S : Set F) (ha : a ∈ S) (hc : c ∈ S) :
    verticalPrismAffine a c z ∈ convexHull ℝ S := by
  rw [verticalPrismAffine_apply]
  have key : a + z.2 • (c - a) = (1 - z.2) • a + z.2 • c := by module
  rw [key]
  exact (convex_convexHull ℝ S) (subset_convexHull ℝ S ha) (subset_convexHull ℝ S hc)
    (by linarith [hz.2]) hz.1 (by ring)

theorem le_of_forall_lt_succ {s : ℕ → ℝ} {n : ℕ} (hmono : ∀ i < n, s i < s (i + 1)) :
    ∀ j, j ≤ n → ∀ i, i ≤ j → s i ≤ s j := by
  intro j
  induction j with
  | zero => intro _ i hi; rw [Nat.le_zero.mp hi]
  | succ j ih =>
    intro hj i hi
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (by omega) i (by omega)).trans (hmono j (by omega)).le
    · rw [Nat.le_antisymm hi h]

theorem mem_Icc_of_forall_lt_succ {s : ℕ → ℝ} {n : ℕ} (hmono : ∀ i < n, s i < s (i + 1))
    (hs0 : s 0 = 0) (hsn : s n = 1) {i : ℕ} (hi : i ≤ n) : s i ∈ Icc (0 : ℝ) 1 :=
  ⟨hs0 ▸ le_of_forall_lt_succ hmono i hi 0 (Nat.zero_le i),
    hsn ▸ le_of_forall_lt_succ hmono n le_rfl i hi⟩

open Classical in
theorem exists_isPiecewiseAffineOn_prism_of_partition {f g : ℝ → F} {n : ℕ} {s : ℕ → ℝ}
    (hs0 : s 0 = 0) (hsn : s n = 1) (hmono : ∀ i < n, s i < s (i + 1))
    (hf : ∀ i < n, ∀ x ∈ Icc (s i) (s (i + 1)),
      f x = f (s i) + ((x - s i) / (s (i + 1) - s i)) • (f (s (i + 1)) - f (s i)))
    (hg : ∀ i < n, ∀ x ∈ Icc (s i) (s (i + 1)),
      g x = g (s i) + ((x - s i) / (s (i + 1) - s i)) • (g (s (i + 1)) - g (s i))) :
    ∃ Φ : ℝ × ℝ → F, IsPiecewiseAffineOn Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 0) = f x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 1) = g x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (0, t) = f 0 + t • (g 0 - f 0)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (1, t) = f 1 + t • (g 1 - f 1)) ∧
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∃ i, i < n ∧
        Φ z ∈ convexHull ℝ ({f (s i), f (s (i + 1)), g (s i), g (s (i + 1))} : Set F)) := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [hs0] at hsn; norm_num at hsn
    · exact h
  have hs_nonneg : ∀ k, k ≤ n → 0 ≤ s k :=
    fun k hk => hs0 ▸ le_of_forall_lt_succ hmono k hk 0 (Nat.zero_le k)
  have key : ∀ k, k ≤ n → ∃ Φ : ℝ × ℝ → F,
      IsPiecewiseAffineOn Φ (Icc (0 : ℝ) (s k) ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Icc (0 : ℝ) (s k), Φ (x, 0) = f x) ∧
      (∀ x ∈ Icc (0 : ℝ) (s k), Φ (x, 1) = g x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (0, t) = f 0 + t • (g 0 - f 0)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (s k, t) = f (s k) + t • (g (s k) - f (s k))) ∧
      (∀ z ∈ Icc (0 : ℝ) (s k) ×ˢ Icc (0 : ℝ) 1, ∃ i, i < n ∧
        Φ z ∈ convexHull ℝ ({f (s i), f (s (i + 1)), g (s i), g (s (i + 1))} : Set F)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨verticalPrismAffine (f 0) (g 0),
        isPiecewiseAffineOn_of_affine_of_isHPolytope _ (isHPolytope_Icc.prod isHPolytope_Icc),
        ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        have hx0 : x = 0 := le_antisymm (by rw [← hs0]; exact hx.2) hx.1
        rw [verticalPrismAffine_apply, hx0]
        simp
      · intro x hx
        have hx0 : x = 0 := le_antisymm (by rw [← hs0]; exact hx.2) hx.1
        rw [verticalPrismAffine_apply, hx0]
        simp
      · intro t _
        rw [verticalPrismAffine_apply]
      · intro t _
        rw [verticalPrismAffine_apply, hs0]
      · intro z hz
        refine ⟨0, hn, verticalPrismAffine_mem_convexHull _ _ hz.2 _ ?_ ?_⟩
        · rw [← hs0]; exact mem_insert _ _
        · rw [← hs0]; exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_insert _ _))
    | succ k ih =>
      intro hk
      obtain ⟨Φ, hPA, hbot, htop, hleft, hright, himg⟩ := ih (by omega)
      have hkn : k < n := by omega
      have hlt : s k < s (k + 1) := hmono k hkn
      have hk0 : 0 ≤ s k := hs_nonneg k (by omega)
      have hAB : Icc (0 : ℝ) (s k) ×ˢ Icc (0 : ℝ) 1 ∪ Icc (s k) (s (k + 1)) ×ˢ Icc (0 : ℝ) 1
          = Icc (0 : ℝ) (s (k + 1)) ×ˢ Icc (0 : ℝ) 1 := by
        rw [← union_prod, Icc_union_Icc_eq_Icc hk0 hlt.le]
      have heq : EqOn Φ (prismStripMap (s k) (s (k + 1)) (f (s k)) (f (s (k + 1)))
          (g (s k)) (g (s (k + 1))))
          (Icc (0 : ℝ) (s k) ×ˢ Icc (0 : ℝ) 1 ∩ Icc (s k) (s (k + 1)) ×ˢ Icc (0 : ℝ) 1) := by
        rintro ⟨x, t⟩ ⟨⟨⟨hx1, hx2⟩, ht⟩, ⟨hx3, _⟩⟩
        have hxk : x = s k := le_antisymm hx2 hx3.1
        subst hxk
        rw [hright t ht, prismStripMap_left _ _ _ _ ht]
      set Ψ := prismStripMap (s k) (s (k + 1)) (f (s k)) (f (s (k + 1))) (g (s k))
        (g (s (k + 1))) with hΨdef
      set A : Set (ℝ × ℝ) := Icc (0 : ℝ) (s k) ×ˢ Icc (0 : ℝ) 1 with hAdef
      set G : ℝ × ℝ → F :=
        @Set.piecewise (ℝ × ℝ) (fun _ => F) A Φ Ψ (fun j => Classical.propDecidable _) with hGdef
      have hGmem : ∀ z ∈ A, G z = Φ z := by
        intro z hz
        rw [hGdef]
        exact if_pos hz
      have hGnot : ∀ z ∉ A, G z = Ψ z := by
        intro z hz
        rw [hGdef]
        exact if_neg hz
      refine ⟨G, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hAB]
        exact hPA.piecewise_of_isClosed (isPiecewiseAffineOn_prismStripMap hlt _ _ _ _)
          (isClosed_Icc.prod isClosed_Icc) (isClosed_Icc.prod isClosed_Icc) heq
      · intro x hx
        by_cases hxk : x ≤ s k
        · rw [hGmem _ ⟨⟨hx.1, hxk⟩, le_rfl, zero_le_one⟩]
          exact hbot x ⟨hx.1, hxk⟩
        · rw [hGnot _ (fun h => hxk h.1.2), hΨdef, prismStripMap_bottom]
          exact (hf k hkn x ⟨le_of_not_ge hxk, hx.2⟩).symm
      · intro x hx
        by_cases hxk : x ≤ s k
        · rw [hGmem _ ⟨⟨hx.1, hxk⟩, zero_le_one, le_rfl⟩]
          exact htop x ⟨hx.1, hxk⟩
        · rw [hGnot _ (fun h => hxk h.1.2), hΨdef,
            prismStripMap_top _ _ _ _ ⟨le_of_not_ge hxk, hx.2⟩ hlt]
          exact (hg k hkn x ⟨le_of_not_ge hxk, hx.2⟩).symm
      · intro t ht
        rw [hGmem _ ⟨⟨le_rfl, hk0⟩, ht⟩]
        exact hleft t ht
      · intro t ht
        rw [hGnot _ (fun h => absurd h.1.2 (not_le.mpr hlt)), hΨdef,
          prismStripMap_right hlt _ _ _ _ ht]
      · intro z hz
        by_cases hzA : z ∈ A
        · rw [hGmem _ hzA]
          exact himg z hzA
        · rw [hGnot _ hzA, hΨdef]
          refine ⟨k, hkn, prismStripMap_mem_convexHull hlt _ _ _ _ ?_⟩
          rw [← hAB] at hz
          exact hz.resolve_left hzA
  obtain ⟨Φ, hPA, hbot, htop, hleft, hright, himg⟩ := key n le_rfl
  rw [hsn] at hPA hbot htop hright himg
  exact ⟨Φ, hPA, hbot, htop, hleft, hright, himg⟩

theorem mapsTo_of_forall_mem_convexHull_cell {Φ : ℝ × ℝ → F} {S : Set F} (hS : Convex ℝ S)
    {n : ℕ} {s : ℕ → ℝ} {f g : ℝ → F}
    (himg : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∃ i, i < n ∧
      Φ z ∈ convexHull ℝ ({f (s i), f (s (i + 1)), g (s i), g (s (i + 1))} : Set F))
    (hcell : ∀ i < n, f (s i) ∈ S ∧ f (s (i + 1)) ∈ S ∧ g (s i) ∈ S ∧ g (s (i + 1)) ∈ S) :
    MapsTo Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) S := by
  intro z hz
  obtain ⟨i, hi, hmem⟩ := himg z hz
  obtain ⟨h1, h2, h3, h4⟩ := hcell i hi
  have hsub : ({f (s i), f (s (i + 1)), g (s i), g (s (i + 1))} : Set F) ⊆ S := by
    rintro y (rfl | rfl | rfl | rfl) <;> assumption
  exact hS.convexHull_subset_iff.mpr hsub hmem

open Classical in
theorem exists_isPiecewiseAffineOn_prism_of_partition_of_loop {f g : ℝ → F} {n : ℕ} {s : ℕ → ℝ}
    (hs0 : s 0 = 0) (hsn : s n = 1) (hmono : ∀ i < n, s i < s (i + 1))
    (hf : ∀ i < n, ∀ x ∈ Icc (s i) (s (i + 1)),
      f x = f (s i) + ((x - s i) / (s (i + 1) - s i)) • (f (s (i + 1)) - f (s i)))
    (hg : ∀ i < n, ∀ x ∈ Icc (s i) (s (i + 1)),
      g x = g (s i) + ((x - s i) / (s (i + 1) - s i)) • (g (s (i + 1)) - g (s i)))
    (hfloop : f 0 = f 1) (hgloop : g 0 = g 1) :
    ∃ Φ : ℝ × ℝ → F, IsPiecewiseAffineOn Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 0) = f x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 1) = g x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (0, t) = Φ (1, t)) ∧
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∃ i, i < n ∧
        Φ z ∈ convexHull ℝ ({f (s i), f (s (i + 1)), g (s i), g (s (i + 1))} : Set F)) := by
  obtain ⟨Φ, hPA, hbot, htop, hleft, hright, himg⟩ :=
    exists_isPiecewiseAffineOn_prism_of_partition hs0 hsn hmono hf hg
  refine ⟨Φ, hPA, hbot, htop, fun t ht => ?_, himg⟩
  rw [hleft t ht, hright t ht, hfloop, hgloop]

end DifferentialGeometry.Topology.PiecewiseLinear
