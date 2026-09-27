import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_spanning_pair_returning_arc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P A : Set E} {T₀ T₁ : Set (E × ℝ)} {α β : ℝ → E × ℝ} {δ : ℝ → E}
    {a b : ℝ} {x y : E} (hab : a < b)
    (hα : IsPLHomeomorphOn α (Icc 0 1) T₀)
    (hβ : IsPLHomeomorphOn β (Icc 0 1) T₁)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A)
    (hα₀ : α 0 = (x, a)) (hα₁ : α 1 = (x, b))
    (hβ₀ : β 0 = (y, a)) (hβ₁ : β 1 = (y, b))
    (hδ₀ : δ 0 = x) (hδ₁ : δ 1 = y)
    (hT₀ : T₀ ⊆ P ×ˢ Icc a b) (hT₁ : T₁ ⊆ P ×ˢ Icc a b) (hAP : A ⊆ P)
    (hT₀a : T₀ ∩ (P ×ˢ ({a} : Set ℝ)) = {(x, a)})
    (hT₀b : T₀ ∩ (P ×ˢ ({b} : Set ℝ)) = {(x, b)})
    (hT₁a : T₁ ∩ (P ×ˢ ({a} : Set ℝ)) = {(y, a)})
    (hT₁b : T₁ ∩ (P ×ˢ ({b} : Set ℝ)) = {(y, b)})
    (hdis : Disjoint T₀ T₁) :
    let U := (T₀ ∪ (A ×ˢ ({a} : Set ℝ))) ∪ T₁
    ∃ γ : ℝ → E × ℝ, IsPLHomeomorphOn γ (Icc 0 1) U ∧
      γ 0 = (x, b) ∧ γ 1 = (y, b) ∧ U ⊆ P ×ˢ Icc a b ∧
      U ∩ (P ×ˢ ({b} : Set ℝ)) = {(x, b), (y, b)} ∧
      U ∩ (P ×ˢ ({a} : Set ℝ)) = A ×ˢ ({a} : Set ℝ) := by
  have hxA : x ∈ A := hδ₀ ▸ hδ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hyA : y ∈ A := hδ₁ ▸ hδ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hxT : (x, a) ∈ T₀ := hα₀ ▸ hα.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hyT : (y, a) ∈ T₁ := hβ₀ ▸ hβ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hA : IsPolyhedron A :=
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hδ).isPolyhedron
  have hδa : IsPLHomeomorphOn (fun t => (δ t, a)) (Icc 0 1)
      (A ×ˢ ({a} : Set ℝ)) := hδ.trans (hA.isPLHomeomorphOn_prod_const a)
  have hmeet₀ : T₀ ∩ (A ×ˢ ({a} : Set ℝ)) = {(x, a)} := by
    apply Subset.antisymm
    · exact fun z hz => hT₀a.subset ⟨hz.1, hAP hz.2.1, hz.2.2⟩
    · rintro z rfl
      exact ⟨hxT, hxA, rfl⟩
  have hmeet₁ : (A ×ˢ ({a} : Set ℝ)) ∩ T₁ = {(y, a)} := by
    apply Subset.antisymm
    · exact fun z hz => hT₁a.subset ⟨hz.2, hAP hz.1.1, hz.1.2⟩
    · rintro z rfl
      exact ⟨⟨hyA, rfl⟩, hyT⟩
  obtain ⟨l, hl, hl₀, -, hl₁⟩ := exists_isPLHomeomorphOn_Icc_concat
    (isPLHomeomorphOn_comp_one_sub hα) hδa (by simp only [sub_self, hα₀, hδ₀])
    (by simpa only [sub_self, hα₀] using hmeet₀)
  have hlend : l 1 = (y, a) := hl₁.trans (congrArg (fun z => (z, a)) hδ₁)
  have hmeet : (T₀ ∪ (A ×ˢ ({a} : Set ℝ))) ∩ T₁ = {l 1} := by
    rw [union_inter_distrib_right, hdis.inter_eq, empty_union, hmeet₁, hlend]
  obtain ⟨γ, hγ, hγ₀, -, hγ₁⟩ := exists_isPLHomeomorphOn_Icc_concat hl hβ
    (hβ₀.trans hlend.symm) hmeet
  refine ⟨γ, hγ, ?_, hγ₁.trans hβ₁, ?_, ?_, ?_⟩
  · simpa only [sub_zero, hα₁] using hγ₀.trans hl₀
  · refine union_subset (union_subset hT₀ ?_) hT₁
    rintro z ⟨hzA, hza⟩
    have hza' : z.2 = a := hza
    exact ⟨hAP hzA, hza'.symm ▸ ⟨le_rfl, hab.le⟩⟩
  · apply Subset.antisymm
    · rintro z ⟨(hz₀ | hzA) | hz₁, hzb⟩
      · exact Or.inl (hT₀b.subset ⟨hz₀, hzb⟩)
      · exact (hab.ne (hzA.2.symm.trans hzb.2)).elim
      · exact Or.inr (hT₁b.subset ⟨hz₁, hzb⟩)
    · rintro z (rfl | rfl)
      · have hx := hT₀b.symm.subset (mem_singleton (x, b))
        exact ⟨Or.inl (Or.inl hx.1), hx.2⟩
      · have hy := hT₁b.symm.subset (mem_singleton (y, b))
        exact ⟨Or.inr hy.1, hy.2⟩
  · apply Subset.antisymm
    · rintro z ⟨(hz₀ | hzA) | hz₁, hza⟩
      · have hz : z = (x, a) := hT₀a.subset ⟨hz₀, hza⟩
        exact hz ▸ ⟨hxA, rfl⟩
      · exact hzA
      · have hz : z = (y, a) := hT₁a.subset ⟨hz₁, hza⟩
        exact hz ▸ ⟨hyA, rfl⟩
    · exact fun z hz => ⟨Or.inl (Or.inr hz), hAP hz.1, hz.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
