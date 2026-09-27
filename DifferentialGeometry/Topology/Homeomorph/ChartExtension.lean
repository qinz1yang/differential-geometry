import DifferentialGeometry.Topology.Homeomorph.SupportedLocalEmbedding
import Mathlib.Topology.OpenPartialHomeomorph.Composition

open Set

namespace OpenPartialHomeomorph

theorem exists_homeomorph_extension {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (e : OpenPartialHomeomorph X Y) (F : Y ≃ₜ Y)
    {K : Set Y} (hK : IsCompact K) (hKt : K ⊆ e.target) (hfix : EqOn F id Kᶜ) :
    ∃ H : X ≃ₜ X,
      (∀ x ∈ e.source, H x = e.symm (F (e x))) ∧
      (∀ x ∈ e.source, H.symm x = e.symm (F.symm (e x))) ∧
      IsCompact (e.symm '' K) ∧ e.symm '' K ⊆ e.source ∧
      EqOn H id (e.symm '' K)ᶜ ∧ EqOn H.symm id (e.symm '' K)ᶜ ∧
      ∀ A : Set X, H '' A = (A \ e.source) ∪
        e.symm '' (F '' (e '' (A ∩ e.source))) := by
  have hfixi : EqOn F.symm id Kᶜ := by
    intro p hp
    apply F.injective
    exact (F.apply_symm_apply p).trans (hfix hp).symm
  have hmap : MapsTo F e.target e.target := by
    intro p hp
    by_contra hn
    have hFK : F p ∉ K := fun h => hn (hKt h)
    have heq : F p = p := F.injective (hfix hFK)
    exact hn (heq.symm ▸ hp)
  have hmapi : MapsTo F.symm e.target e.target := by
    intro p hp
    by_contra hn
    have hFK : F.symm p ∉ K := fun h => hn (hKt h)
    have heq : F.symm p = p := F.symm.injective (hfixi hFK)
    exact hn (heq.symm ▸ hp)
  have himage : F '' e.target = e.target := by
    apply Subset.antisymm hmap.image_subset
    exact fun p hp => ⟨F.symm p, hmapi hp, F.apply_symm_apply p⟩
  have heU : e '' ((univ : Set X) ∩ e.source) = e.target := by
    rw [univ_inter, e.image_source_eq_target]
  obtain ⟨H₀, hH₀, hH₀fix⟩ := e.exists_homeomorph_eqOn_of_isClosed isClosed_univ
    F.continuous.continuousOn F.injective.injOn (heU.symm ▸ hmap) hK hKt
    (fun p hp => hfix hp.2)
  have hwhole : ((univ : Set X) \ e.source) ∪
      e.symm '' (F '' (e '' (univ ∩ e.source))) = univ := by
    rw [heU, himage, e.symm_image_target_eq_source]
    simp
  let H := (Homeomorph.Set.univ X).symm.trans
    (H₀.trans ((Homeomorph.setCongr hwhole).trans (Homeomorph.Set.univ X)))
  have hH (x : X) (hx : x ∈ e.source) : H x = e.symm (F (e x)) := hH₀ ⟨x, mem_univ x⟩ hx
  have hHfix : EqOn H id (e.symm '' K)ᶜ := fun x hx => hH₀fix ⟨x, mem_univ x⟩ hx
  have hKs : e.symm '' K ⊆ e.source := by
    rintro x ⟨p, hp, rfl⟩
    exact e.map_target (hKt hp)
  refine ⟨H, hH, ?_, hK.image_of_continuousOn (e.continuousOn_symm.mono hKt),
    hKs, hHfix, ?_, ?_⟩
  · intro x hx
    apply H.injective
    rw [H.apply_symm_apply, hH _ (e.map_target (hmapi (e.map_source hx))),
      e.right_inv (hmapi (e.map_source hx)), F.apply_symm_apply, e.left_inv hx]
  · intro x hx
    apply H.injective
    exact (H.apply_symm_apply x).trans (hHfix hx).symm
  · intro A
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxs : x ∈ e.source
      · exact Or.inr ⟨F (e x), ⟨e x, ⟨x, ⟨hx, hxs⟩, rfl⟩, rfl⟩, (hH x hxs).symm⟩
      · have hxe : x ∉ e.symm '' K := fun h => hxs (hKs h)
        rw [hHfix hxe]
        exact Or.inl ⟨hx, hxs⟩
    · rintro (hy | ⟨p, ⟨q, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩)
      · exact ⟨y, hy.1, hHfix (fun h => hy.2 (hKs h))⟩
      · exact ⟨x, hx.1, hH x hx.2⟩

theorem eqOn_comp_of_chart_extensions
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (c : OpenPartialHomeomorph X Y) (e : OpenPartialHomeomorph X Z)
    (F : Z → Z) {K : Set Z} (hK : K ⊆ (c.symm.trans e).target)
    (R₀ : X → X) (R₁ : Y → Y)
    (hR₀ : ∀ x ∈ e.source, R₀ x = e.symm (F (e x)))
    (hR₁ : ∀ y ∈ (c.symm.trans e).source,
      R₁ y = (c.symm.trans e).symm (F ((c.symm.trans e) y)))
    (hfix₀ : EqOn R₀ id (e.symm '' K)ᶜ)
    (hfix₁ : EqOn R₁ id ((c.symm.trans e).symm '' K)ᶜ) :
    EqOn (R₁ ∘ c) (c ∘ R₀) c.source := by
  let f := c.symm.trans e
  intro x hx
  change R₁ (c x) = c (R₀ x)
  by_cases hxe : x ∈ e.source
  · have hcf : c x ∈ f.source := by
      refine ⟨c.map_source hx, ?_⟩
      change c.symm (c x) ∈ e.source
      rwa [c.left_inv hx]
    have hfx : f (c x) = e x := by
      change e (c.symm (c x)) = e x
      rw [c.left_inv hx]
    rw [hR₁ _ hcf, hfx, hR₀ _ hxe]
    rfl
  · have hxc : x ∉ e.symm '' K := by
      rintro ⟨p, hp, hpx⟩
      exact hxe (hpx ▸ e.map_target (hK hp).1)
    have hcxf : c x ∉ f.symm '' K := by
      rintro ⟨p, hp, hpc⟩
      have hec : e.symm p ∈ c.source := (hK hp).2
      have he : e.symm p = x := c.injOn hec hx hpc
      exact hxc ⟨p, hp, he⟩
    rw [hfix₀ hxc, hfix₁ hcxf]
    rfl

end OpenPartialHomeomorph
