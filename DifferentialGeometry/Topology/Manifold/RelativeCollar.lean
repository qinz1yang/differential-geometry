import DifferentialGeometry.Topology.Diffeomorph.Collar

set_option autoImplicit false

noncomputable section

open Set Filter Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Collar

theorem exists_relative_collar_isotopy
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    {Φ₀ Φ₁ : OpenPartialHomeomorph (N × ℝ) E}
    (hΦ₀ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ₀ Φ₀.source)
    (hi₀ : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ₀.symm Φ₀.target)
    (hΦ₁ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ₁ Φ₁.source)
    (hi₁ : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ₁.symm Φ₁.target)
    {A : Set N} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε)
    (hw₀ : A ×ˢ Set.Icc (-ε) ε ⊆ Φ₀.source)
    (hw₁ : A ×ˢ Set.Icc (-ε) ε ⊆ Φ₁.source)
    (hcore : ∀ p ∈ A, Φ₀ (p, 0) = Φ₁ (p, 0)) :
    ∃ Ψ : ℝ → E ≃ₘ[ℝ] E,
      Ψ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => Ψ q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => (Ψ q.1).symm q.2) ∧
      (∃ K : Set E, IsCompact K ∧ (∀ t, Set.EqOn (Ψ t) id Kᶜ) ∧
        ∀ t, Set.EqOn (Ψ t).symm id Kᶜ) ∧
      ∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε, Ψ t (Φ₀ (p, t)) = Φ₁ (p, t) := by
  obtain ⟨H, hH0, hH, hHi, KH, hKH, _, hKHfix, hHiso⟩ :=
    Diffeomorph.exists_isotopy_eq_collar Φ₀ hΦ₀ hi₀ hA hε hw₀
  obtain ⟨G, hG0, hG, hGi, KG, hKG, _, hKGfix, hGiso⟩ :=
    Diffeomorph.exists_isotopy_eq_collar Φ₁ hΦ₁ hi₁ hA hε hw₁
  refine ⟨fun t => (H t).symm.trans (G t), ?_, ?_, ?_, ?_, ?_⟩
  · show (H 0).symm.trans (G 0) = Diffeomorph.refl 𝓘(ℝ, E) E ∞
    rw [hH0, hG0, Diffeomorph.symm_refl, Diffeomorph.refl_trans]
  · have hfun : (fun q : ℝ × E => ((H q.1).symm.trans (G q.1)) q.2) =
        fun q : ℝ × E => G q.1 ((H q.1).symm q.2) := by
      funext q
      show G q.1 ((H q.1).symm q.2) = G q.1 ((H q.1).symm q.2)
      rfl
    rw [hfun]
    exact hG.comp (contMDiff_fst.prodMk hHi)
  · have hfun : (fun q : ℝ × E => ((H q.1).symm.trans (G q.1)).symm q.2) =
        fun q : ℝ × E => H q.1 ((G q.1).symm q.2) := by
      funext q
      show H q.1 ((G q.1).symm q.2) = H q.1 ((G q.1).symm q.2)
      rfl
    rw [hfun]
    exact hH.comp (contMDiff_fst.prodMk hGi)
  · refine ⟨KH ∪ KG, hKH.union hKG, fun t => ?_, fun t => ?_⟩
    · intro x hx
      have hxH : x ∉ KH := fun h => hx (Or.inl h)
      have hxG : x ∉ KG := fun h => hx (Or.inr h)
      have hHx : (H t).symm x = x := by simpa using (hKHfix t).2 hxH
      have hGx : G t x = x := by simpa using (hKGfix t).1 hxG
      show G t ((H t).symm x) = id x
      rw [hHx, hGx]
      rfl
    · intro x hx
      have hxH : x ∉ KH := fun h => hx (Or.inl h)
      have hxG : x ∉ KG := fun h => hx (Or.inr h)
      have hHx : (H t).symm x = x := by simpa using (hKHfix t).2 hxH
      have hGx : G t x = x := by simpa using (hKGfix t).1 hxG
      have hx' : ((H t).symm.trans (G t)) x = x := by
        show G t ((H t).symm x) = x
        rw [hHx, hGx]
      have h2 := Diffeomorph.symm_apply_apply ((H t).symm.trans (G t)) x
      rw [hx'] at h2
      show ((H t).symm.trans (G t)).symm x = id x
      rw [h2]
      rfl
  · intro p hp t ht
    have hHt : (H t).symm (Φ₀ (p, t)) = Φ₁ (p, 0) := by
      rw [← hHiso p hp t ht, ← hcore p hp, Diffeomorph.symm_apply_apply]
    have hGt : G t (Φ₁ (p, 0)) = Φ₁ (p, t) := hGiso p hp t ht
    show G t ((H t).symm (Φ₀ (p, t))) = Φ₁ (p, t)
    rw [hHt, hGt]

end DifferentialGeometry.Topology.Collar
