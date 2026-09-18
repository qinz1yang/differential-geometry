import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Sets.Opens
set_option autoImplicit false
open Set TopologicalSpace Filter

theorem continuousOn_of_open_cover_prod
    {P M N ι : Type*} [TopologicalSpace P] [TopologicalSpace M] [TopologicalSpace N]
    (U : ι → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    {A : Set P} {B : Set M} {f : P × M → N}
    (hf : ∀ i, ContinuousOn
      (fun p : P × U i => f (p.1, (p.2 : M))) (A ×ˢ (Subtype.val ⁻¹' B))) :
    ContinuousOn f (A ×ˢ B) := by
  rintro ⟨t, x⟩ hp
  obtain ⟨i, hxi⟩ := hcover x
  let y : U i := ⟨x, hxi⟩
  let phi : P × U i → P × M := fun q => (q.1, (q.2 : M))
  have hemb : Topology.IsOpenEmbedding phi :=
    Topology.IsOpenEmbedding.id.prodMap (U i).isOpen.isOpenEmbedding_subtypeVal
  have h := hf i (t, y) ⟨hp.1, hp.2⟩
  change Tendsto (f ∘ phi) (nhdsWithin (t, y) (phi ⁻¹' (A ×ˢ B))) (nhds (f (t, x))) at h
  change Tendsto f (nhdsWithin (t, x) (A ×ˢ B)) (nhds (f (t, x)))
  rw [← hemb.map_nhdsWithin_preimage_eq (A ×ˢ B) (t, y)]
  exact h
