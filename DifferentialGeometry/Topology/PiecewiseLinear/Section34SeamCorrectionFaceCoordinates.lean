import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionBaseSides

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.seam_face_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ × ℝ → E} {P A B : Set E} {δ ε : ℝ → E}
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) P)
    (hθbd : θ '' frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = A ∪ B)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) (hε : IsPLHomeomorphOn ε (Icc 0 1) B)
    (hεzero : ε 0 = δ 0) (hεone : ε 1 = δ 1) (hAB : A ∩ B = {δ 0, δ 1})
    (hbottom : θ '' (Icc (0 : ℝ) 1 ×ˢ {0}) =
      ε '' Icc (0 : ℝ) (1 / 4) ∪ δ '' Icc (0 : ℝ) (1 / 4))
    (hleft : θ '' (Icc (0 : ℝ) (1 / 2) ×ˢ {0}) = ε '' Icc (0 : ℝ) (1 / 4))
    (hright : θ '' (Icc (1 / 2 : ℝ) 1 ×ˢ {0}) = δ '' Icc (0 : ℝ) (1 / 4))
    (htop : θ '' (Icc (0 : ℝ) 1 ×ˢ {1}) = δ '' Icc (1 / 2 : ℝ) (3 / 4)) :
    let U := frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ θ ⁻¹' A
    let V := frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ θ ⁻¹' B
    θ '' U = A ∧ θ '' V = B ∧
      U ∩ (Icc (0 : ℝ) 1 ×ˢ {0}) = Icc (1 / 2 : ℝ) 1 ×ˢ {0} ∧
      V ∩ (Icc (0 : ℝ) 1 ×ˢ {0}) = Icc (0 : ℝ) (1 / 2) ×ˢ {0} ∧
      Icc (0 : ℝ) 1 ×ˢ {(1 : ℝ)} ⊆ U ∧
      Disjoint V (Icc (0 : ℝ) 1 ×ˢ {(1 : ℝ)}) := by
  let I := Icc (0 : ℝ) 1
  let Q := I ×ˢ I
  let U := frontier Q ∩ θ ⁻¹' A
  let V := frontier Q ∩ θ ⁻¹' B
  change θ '' U = A ∧ θ '' V = B ∧
    U ∩ (I ×ˢ {0}) = Icc (1 / 2 : ℝ) 1 ×ˢ {0} ∧
    V ∩ (I ×ˢ {0}) = Icc (0 : ℝ) (1 / 2) ×ˢ {0} ∧
    I ×ˢ {(1 : ℝ)} ⊆ U ∧ Disjoint V (I ×ˢ {(1 : ℝ)})
  obtain ⟨hA, hB, hdis⟩ := inter_initial_arcs_of_common_ends hδ hε hεzero hεone hAB
  have hrim (r : ℝ) (hr : r ∈ ({0, 1} : Set ℝ)) : I ×ˢ {r} ⊆ frontier Q := by
    intro p hp
    change p ∈ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc (zero_le_one' ℝ)]
    exact Or.inl ⟨hp.1, hp.2.symm ▸ hr⟩
  have hfront : frontier Q ⊆ Q :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset
  have hhalf {C : Set E} {T : Set (ℝ × ℝ)} (hT : T ⊆ I ×ˢ {(0 : ℝ)})
      (himage : θ '' T = θ '' (I ×ˢ {(0 : ℝ)}) ∩ C) :
      (frontier Q ∩ θ ⁻¹' C) ∩ (I ×ˢ {(0 : ℝ)}) = T := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := himage.symm.subset ⟨⟨x, hx.2, rfl⟩, hx.1.2⟩
      have heq := hθ.bijOn.injOn (hfront (hrim 0 (by simp) (hT hy)))
        (hfront hx.1.1) hyx
      exact heq ▸ hy
    · intro x hx
      exact ⟨⟨hrim 0 (by simp) (hT hx), (himage.subset ⟨x, hx, rfl⟩).2⟩, hT hx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change θ '' (frontier Q ∩ θ ⁻¹' A) = A
    rw [image_inter_preimage, hθbd]
    exact inter_eq_right.mpr subset_union_left
  · change θ '' (frontier Q ∩ θ ⁻¹' B) = B
    rw [image_inter_preimage, hθbd]
    exact inter_eq_right.mpr subset_union_right
  · apply hhalf (prod_mono_left (Icc_subset_Icc (by norm_num) le_rfl))
    rw [hright, hbottom, hA]
  · apply hhalf (prod_mono_left (Icc_subset_Icc le_rfl (by norm_num)))
    rw [hleft, hbottom, hB]
  · intro x hx
    refine ⟨hrim 1 (by simp) hx, ?_⟩
    have hxδ := htop.subset ⟨x, hx, rfl⟩
    exact ((image_mono (Icc_subset_Icc (by norm_num) (by norm_num))).trans
      hδ.image_eq.subset) hxδ
  · apply disjoint_left.mpr
    intro x hxV hx
    exact disjoint_left.mp hdis (htop.subset ⟨x, hx, rfl⟩) hxV.2

end DifferentialGeometry.Topology.PiecewiseLinear
