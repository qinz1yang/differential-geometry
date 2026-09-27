import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeChain

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsCylindricalDiagram.image_endMap_of_eq_marked_caps
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E × ℝ → F} {D X : Set E} {M : Set F} (hφ : IsCylindricalDiagram φ D M)
    {u : E → E} (hu : IsPLHomeomorphOn u D D)
    (hends : ∀ x ∈ D, φ (x, 0) = φ (u x, 1)) (hX : X ⊆ D)
    (hcap : φ '' (X ×ˢ ({0} : Set ℝ)) = φ '' (X ×ˢ ({1} : Set ℝ))) : u '' X = X := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hz : φ (u x, 1) ∈ φ '' (X ×ˢ ({1} : Set ℝ)) := by
      rw [← hends x (hX hx), ← hcap]
      exact mem_image_of_mem φ ⟨hx, rfl⟩
    obtain ⟨⟨y, t⟩, ⟨hy, rfl⟩, heq⟩ := hz
    have hxy := hφ.eq_of_eq_top (hX hy) (hu.bijOn.mapsTo (hX hx)) heq
    exact hxy ▸ hy
  · intro x hx
    have hz : φ (x, 1) ∈ φ '' (X ×ˢ ({0} : Set ℝ)) := by
      rw [hcap]
      exact mem_image_of_mem φ ⟨hx, rfl⟩
    obtain ⟨⟨y, t⟩, ⟨hy, rfl⟩, heq⟩ := hz
    refine ⟨y, hy, hφ.eq_of_eq_top (hu.bijOn.mapsTo (hX hy)) (hX hx) ?_⟩
    exact (hends y (hX hy)).symm.trans heq

theorem exists_marked_cylindrical_diagram_of_chain {G : ℕ → (ℝ × ℝ) × ℝ → E}
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
    (harmclose : ∀ i,
      G (m + 1) '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
        G 0 '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)))
    {σ : Fin 4 → Fin 4}
    (hσ : ∀ i, G (m + 1) (fourSpokeModelLeaf (σ i), 1) = G 0 (fourSpokeModelLeaf i, 0)) :
    ∃ (φ : (ℝ × ℝ) × ℝ → E) (u : ℝ × ℝ → ℝ × ℝ),
      IsCylindricalDiagram φ spliceSquare (⋃ k ≤ m + 1, B k) ∧
      IsPLHomeomorphOn u spliceSquare spliceSquare ∧
      (∀ x ∈ spliceSquare, φ (x, 0) = φ (u x, 1)) ∧
      (∀ i, u (fourSpokeModelLeaf i) = fourSpokeModelLeaf (σ i)) ∧
      (∀ i, u '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
        segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i)) ∧
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
  refine ⟨φ, u, hφcyl, hu, hφu, fun i => ?_, ?_, hφ0, fun i => ?_, ?_, fun i => ?_, ?_⟩
  · have hri : fourSpokeModelLeaf i ∈ spliceSquare :=
      (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1
    have hrσ : fourSpokeModelLeaf (σ i) ∈ spliceSquare :=
      (fourSpokeModelLeaf_mem_spliceSquareBoundary (σ i)).1
    refine hφcyl.eq_of_eq_top (hu.bijOn.mapsTo hri) hrσ ?_
    rw [← hφu _ hri, hφ0 _ hri, hφ1 _ hrσ, hhr (σ i), hσ i]
  · intro i
    apply hφcyl.image_endMap_of_eq_marked_caps hu hφu
      (segment_fourSpokeModelLeaf_subset_spliceSquare i)
    have hbot : EqOn φ (G 0)
        (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)) := by
      rintro ⟨x, t⟩ ⟨hx, rfl⟩
      exact hφ0 x (segment_fourSpokeModelLeaf_subset_spliceSquare i hx)
    have htop : EqOn φ (G (m + 1) ∘ Prod.map h id)
        (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) := by
      rintro ⟨x, t⟩ ⟨hx, rfl⟩
      exact hφ1 x (segment_fourSpokeModelLeaf_subset_spliceSquare i hx)
    rw [hbot.image_eq, htop.image_eq, image_comp_prodMap_id_left, hhseg i, harmclose i]
  · rw [hφ1 _ (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1, hhr i]
  · rw [hφ1 _ zero_mem_spliceSquare, eq_zero_of_image_segment_fourSpokeModelLeaf hhseg]
  · rw [hstrip _ (segment_fourSpokeModelLeaf_subset_spliceSquare i), hΦstrip i, hhseg i,
      biUnion_le_succ (fun k => G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ
        Icc (0 : ℝ) 1))]
  · rw [hstrip _ (singleton_subset_iff.mpr zero_mem_spliceSquare), hΦcore, image_singleton,
      eq_zero_of_image_segment_fourSpokeModelLeaf hhseg,
      biUnion_le_succ (fun k => G k '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1))]

end DifferentialGeometry.Topology.PiecewiseLinear
