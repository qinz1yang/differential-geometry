import DifferentialGeometry.Analysis.Calculus.SmoothExtension.ConvexOpen
import DifferentialGeometry.Topology.Manifold.IntervalExtension
import DifferentialGeometry.Topology.Embedding.Stability

open scoped ContDiff Manifold Topology

namespace Manifold

open Set

private theorem exists_isSmoothEmbedding_eqOn_Icc_of_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℝ × M → V} {a b : ℝ} (hab : a ≤ b)
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ F)
    (hFemb : ∀ t ∈ Icc a b, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x)))
    (hleft : ∀ᶠ t in 𝓝 a, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x)))
    (hright : ∀ᶠ t in 𝓝 b, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x))) :
    ∃ G : ℝ × M → V, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ G ∧
      (∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => G (t, x))) ∧
      EqOn G F (Icc a b ×ˢ univ) := by
  obtain ⟨c, v, ha, hac⟩ := hleft.exists_Ioo_subset
  obtain ⟨u, d, hb, hbd⟩ := hright.exists_Ioo_subset
  have hnear (t : ℝ) (ht : t ∈ Ioo c d) :
      IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x)) := by
    by_cases hta : t < a
    · exact hac ⟨ht.1, hta.trans ha.2⟩
    · by_cases hbt : b < t
      · exact hbd ⟨hb.1.trans hbt, ht.2⟩
      · exact hFemb t ⟨le_of_not_gt hta, le_of_not_gt hbt⟩
  have hsub : Icc a b ⊆ Ioo c d :=
    fun _ ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  obtain ⟨τ, hτ, hτrange, hτeq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn
      isCompact_Icc isOpen_Ioo (convex_Ioo c d) hsub ⟨a, hsub ⟨le_rfl, hab⟩⟩
  refine ⟨fun q => F (τ q.1, q.2),
    hF.comp ((hτ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd),
    fun t => hnear (τ t) (hτrange ⟨t, rfl⟩), ?_⟩
  intro q hq
  change F (τ q.1, q.2) = F q
  rw [hτeq hq.1]
  rfl

theorem exists_isSmoothEmbedding_extension_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : ℝ × M → V} {a b : ℝ} (hab : a ≤ b)
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e (Icc a b ×ˢ univ))
    (hf : ∀ t ∈ Icc a b, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x))) :
    ∃ G : ℝ × M → V, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ G ∧
      (∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => G (t, x))) ∧
      EqOn G e (Icc a b ×ˢ univ) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · refine ⟨fun q => e (a, q.2),
      (hf a ⟨le_rfl, hab⟩).contMDiff.comp contMDiff_snd,
      fun _ => hf a ⟨le_rfl, hab⟩, ?_⟩
    intro q _
    exact hM.elim q.2
  · let h := (hf a ⟨le_rfl, hab⟩).isImmersion
    let hi := h.isImmersionOfComplement_complement x
    let : FiniteDimensional ℝ (E × h.complement) :=
      FiniteDimensional.of_injective hi.equiv.toLinearEquiv.toLinearMap hi.equiv.injective
    let : FiniteDimensional ℝ E :=
      FiniteDimensional.of_injective (LinearMap.inl ℝ E h.complement)
        LinearMap.inl_injective
    have : T2Space M := (hf a ⟨le_rfl, hab⟩).isEmbedding.t2Space
    obtain ⟨F, hF, hFe⟩ := exists_contMDiff_extension_Icc he
    have hFemb (t : ℝ) (ht : t ∈ Icc a b) :
        IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x)) := by
      have hslice : (fun x => F (t, x)) = fun x => e (t, x) :=
        funext fun x => hFe ⟨ht, mem_univ x⟩
      rw [hslice]
      exact hf t ht
    obtain ⟨G, hG, hGemb, hGF⟩ := exists_isSmoothEmbedding_eqOn_Icc_of_eventually
      hab hF hFemb
      (eventually_isSmoothEmbedding hF (hFemb a ⟨le_rfl, hab⟩) (by simp))
      (eventually_isSmoothEmbedding hF (hFemb b ⟨hab, le_rfl⟩) (by simp))
    exact ⟨G, hG, hGemb, hGF.trans hFe⟩

theorem exists_isSmoothEmbedding_extension_Icc_halfspace
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : ℝ × M → V} {a b : ℝ} (hab : a ≤ b)
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e (Icc a b ×ˢ univ))
    (hf : ∀ t ∈ Icc a b, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞
      (fun x => e (t, x))) :
    ∃ G : ℝ × M → V, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ G ∧
      (∀ t, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => G (t, x))) ∧
      EqOn G e (Icc a b ×ˢ univ) := by
  have : T2Space M := (hf a ⟨le_rfl, hab⟩).isEmbedding.t2Space
  obtain ⟨F, hF, hFe⟩ := exists_contMDiff_extension_Icc_halfspace he
  have hFemb (t : ℝ) (ht : t ∈ Icc a b) :
      IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => F (t, x)) := by
    have hslice : (fun x => F (t, x)) = fun x => e (t, x) :=
      funext fun x => hFe ⟨ht, mem_univ x⟩
    rw [hslice]
    exact hf t ht
  obtain ⟨G, hG, hGemb, hGF⟩ := exists_isSmoothEmbedding_eqOn_Icc_of_eventually
    hab hF hFemb
    (eventually_isSmoothEmbedding_halfspace hF (hFemb a ⟨le_rfl, hab⟩))
    (eventually_isSmoothEmbedding_halfspace hF (hFemb b ⟨hab, le_rfl⟩))
  exact ⟨G, hG, hGemb, hGF.trans hFe⟩

end Manifold
