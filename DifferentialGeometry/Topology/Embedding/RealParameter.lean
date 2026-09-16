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
