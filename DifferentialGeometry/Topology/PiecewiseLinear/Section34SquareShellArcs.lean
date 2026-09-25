import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredSheetAnnuliBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLHomeomorphOn_square_shell_path {c : ℝ} (hc : 0 < c)
    {γ : ℝ → ℝ × ℝ} (hγ : IsPiecewiseAffineOn γ (Icc 0 c))
    (hγbd : MapsTo γ (Icc 0 c) (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) :
    let η := fun t : ℝ => section34SquareShellFlatten c (γ t, t)
    IsPLHomeomorphOn η (Icc 0 c) (η '' Icc 0 c) ∧
      η '' Icc 0 c ⊆ Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c) ∧
      η 0 = γ 0 ∧
      (η '' Icc 0 c) ∩ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = {γ 0} ∧
      (η '' Icc 0 c) ∩ frontier (Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)) = {η c} := by
  let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let η := fun t : ℝ => section34SquareShellFlatten c (γ t, t)
  have hσ := isPLHomeomorphOn_section34SquareShellFlatten hc
  have hγQ (t) (ht : t ∈ Icc (0 : ℝ) c) : γ t ∈ Q :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset (hγbd ht)
  have hgraph : IsPiecewiseAffineOn (fun t : ℝ => (γ t, t)) (Icc 0 c) :=
    hγ.prod_mk isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id.isPiecewiseAffineOn
  have hηpa : IsPiecewiseAffineOn η (Icc 0 c) := by
    simpa only [η, Function.comp_def, preimage_univ, inter_univ] using
      (isPiecewiseAffineOn_section34SquareShellFlatten c).comp hgraph
  have hηinj : InjOn η (Icc 0 c) := by
    intro s hs t ht heq
    exact congrArg Prod.snd (hσ.bijOn.injOn
      (Or.inr ⟨hγbd hs, hs⟩) (Or.inr ⟨hγbd ht, ht⟩) heq)
  have hzero : η 0 = γ 0 :=
    section34_square_shell_flatten_zero hc.le (hγQ 0 ⟨le_rfl, hc.le⟩)
  refine ⟨isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    isHPolytope_Icc.isPolyhedron hηpa hηinj.bijOn_image,
    ?_, hzero, ?_, ?_⟩
  · rintro y ⟨t, ht, rfl⟩
    exact hσ.bijOn.mapsTo (Or.inr ⟨hγbd ht, ht⟩)
  · apply Subset.antisymm
    · rintro y ⟨⟨t, ht, rfl⟩, hy⟩
      have heq : section34SquareShellFlatten c (γ t, t) =
          section34SquareShellFlatten c (η t, 0) :=
        (section34_square_shell_flatten_zero hc.le hy).symm
      have ht0 : t = 0 := congrArg Prod.snd
        (hσ.bijOn.injOn (Or.inr ⟨hγbd ht, ht⟩)
          (show (η t, (0 : ℝ)) ∈ Q ×ˢ {0} ∪ frontier Q ×ˢ Icc 0 c from
            Or.inl ⟨hy, rfl⟩) heq)
      exact (congrArg η ht0).trans hzero
    · intro y hy
      have hy0 : y = γ 0 := hy
      rw [hy0]
      exact ⟨⟨0, ⟨le_rfl, hc.le⟩, hzero⟩, hγQ 0 ⟨le_rfl, hc.le⟩⟩
  · apply Subset.antisymm
    · rintro y ⟨⟨t, ht, rfl⟩, hy⟩
      obtain ⟨p, hp, heq⟩ := (section34_square_shell_top_frontier hc.le).symm.subset hy
      have htc : t = c := congrArg Prod.snd
        (hσ.bijOn.injOn (Or.inr ⟨hγbd ht, ht⟩)
          (Or.inr ⟨hp, hc.le, le_rfl⟩) heq.symm)
      exact congrArg η htc
    · intro y hy
      have hyc : y = η c := hy
      rw [hyc]
      exact ⟨mem_image_of_mem η ⟨hc.le, le_rfl⟩,
        (section34_square_shell_top_frontier hc.le).subset
          ⟨γ c, hγbd ⟨hc.le, le_rfl⟩, rfl⟩⟩

theorem square_shell_path_inter_of_pointwise_ne {c : ℝ} (hc : 0 < c)
    {γ δ : ℝ → ℝ × ℝ}
    (hγ : MapsTo γ (Icc 0 c) (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hδ : MapsTo δ (Icc 0 c) (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hzero : γ 0 = δ 0) (hne : ∀ t ∈ Ioc (0 : ℝ) c, γ t ≠ δ t) :
    (fun t : ℝ => section34SquareShellFlatten c (γ t, t)) '' Icc 0 c ∩
      (fun t : ℝ => section34SquareShellFlatten c (δ t, t)) '' Icc 0 c = {γ 0} := by
  have hσ := isPLHomeomorphOn_section34SquareShellFlatten hc
  have hγ0 : γ 0 ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset (hγ ⟨le_rfl, hc.le⟩)
  have hz := section34_square_shell_flatten_zero hc.le hγ0
  apply Subset.antisymm
  · rintro y ⟨⟨s, hs, hsy⟩, ⟨t, ht, hty⟩⟩
    have heq := hσ.bijOn.injOn (Or.inr ⟨hγ hs, hs⟩) (Or.inr ⟨hδ ht, ht⟩)
      (hsy.trans hty.symm)
    have hst : s = t := congrArg Prod.snd heq
    have heq' : γ s = δ s := by simpa only [hst] using congrArg Prod.fst heq
    have hs0 : s = 0 := le_antisymm (not_lt.mp fun h => hne s ⟨h, hs.2⟩ heq') hs.1
    exact hsy.symm.trans (hs0 ▸ hz)
  · intro y hy
    have hy0 : y = γ 0 := hy
    rw [hy0]
    exact ⟨⟨0, ⟨le_rfl, hc.le⟩, hz⟩,
      ⟨0, ⟨le_rfl, hc.le⟩, by simpa only [← hzero] using hz⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
