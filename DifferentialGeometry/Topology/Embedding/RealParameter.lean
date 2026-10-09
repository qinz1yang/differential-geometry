/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.TietzeExtension

open Set Topology

theorem IsCompact.exists_continuous_leftInvOn
    {X : Type*} [TopologicalSpace X] [NormalSpace X] [T2Space X]
    {K : Set ℝ} (hK : IsCompact K) {f : ℝ → X}
    (hf : ContinuousOn f K) (hi : InjOn f K) :
    ∃ g : X → ℝ, Continuous g ∧ LeftInvOn g f K := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hfc : Continuous (fun t : K => f t) := hf.domRestrict
  have hfi : Function.Injective (fun t : K => f t) := fun s t h => Subtype.ext (hi s.2 t.2 h)
  obtain ⟨g, hg⟩ := ContinuousMap.exists_extension' (hfc.isClosedEmbedding hfi)
    (⟨Subtype.val, continuous_subtype_val⟩ : C(K, ℝ))
  refine ⟨g, g.continuous, fun t ht => ?_⟩
  exact congrFun hg ⟨t, ht⟩

theorem IsCompact.exists_pairwise_disjoint_open_image_neighborhoods
    {X ι : Type*} [TopologicalSpace X] [NormalSpace X] [T2Space X]
    {K : Set ℝ} (hK : IsCompact K) {f : ℝ → X}
    (hf : ContinuousOn f K) (hi : InjOn f K)
    {C V : ι → Set ℝ} (hCK : ∀ i, C i ⊆ K) (hV : ∀ i, IsOpen (V i))
    (hCV : ∀ i, C i ⊆ V i) (hdis : Pairwise fun i j => Disjoint (V i) (V j))
    {N : ι → Set X} (hN : ∀ i, N i ∈ 𝓝ˢ (f '' C i)) :
    ∃ U : ι → Set X,
      (∀ i, IsOpen (U i) ∧ f '' C i ⊆ U i ∧ U i ⊆ N i ∧ U i ∩ f '' K ⊆ f '' V i) ∧
      Pairwise fun i j => Disjoint (U i) (U j) := by
  obtain ⟨g, hg, hgf⟩ := hK.exists_continuous_leftInvOn hf hi
  choose W hW hCW hWN using fun i => mem_nhdsSet_iff_exists.mp (hN i)
  refine ⟨fun i => W i ∩ g ⁻¹' V i, ?_, ?_⟩
  · intro i
    refine ⟨(hW i).inter ((hV i).preimage hg), ?_, inter_subset_left.trans (hWN i), ?_⟩
    · rintro x ⟨t, ht, rfl⟩
      refine ⟨hCW i (mem_image_of_mem f ht), ?_⟩
      change g (f t) ∈ V i
      rw [hgf (hCK i ht)]
      exact hCV i ht
    · rintro x ⟨hx, t, ht, rfl⟩
      exact ⟨t, hgf ht ▸ hx.2, rfl⟩
  · intro i j hij
    exact disjoint_left.mpr fun x hxi hxj => disjoint_left.mp (hdis hij) hxi.2 hxj.2
