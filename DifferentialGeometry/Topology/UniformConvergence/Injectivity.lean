import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

set_option autoImplicit false

open Set Filter Topology

namespace IsCompact

theorem eventually_injOn_of_local_injOn_of_tendstoLocallyUniformlyOn_comp
    {ι Q Y : Type*} [TopologicalSpace Q] [UniformSpace Y] [T2Space Y]
    {M : ι → Type*} {K : Set Q} {l : Filter ι}
    (hK : IsCompact K) (F : ∀ i, Q → M i) (q : ∀ i, M i → Y)
    (hlocal : ∀ x ∈ K, ∃ U ∈ 𝓝[K] x, ∀ᶠ i in l, InjOn (F i) U)
    {g : Q → Y}
    (hconv : TendstoLocallyUniformlyOn (fun i x => q i (F i x)) g l K)
    (hg : ContinuousOn g K) (hinj : InjOn g K) :
    ∀ᶠ i in l, InjOn (F i) K := by
  have hjoint (x : Q) (hx : x ∈ K) :
      Tendsto (fun p : ι × Q => q p.1 (F p.1 p.2)) (l ×ˢ 𝓝[K] x) (𝓝 (g x)) :=
    (Filter.Tendsto.comp (hg x hx) tendsto_snd).congr_uniformity
      (tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hconv x hx)
  have hpair : ∀ᶠ i in l, ∀ p ∈ K ×ˢ K, F i p.1 = F i p.2 → p.1 = p.2 := by
    apply (hK.prod hK).induction_on
      (p := fun S : Set (Q × Q) => ∀ᶠ i in l, ∀ p ∈ S, F i p.1 = F i p.2 → p.1 = p.2)
    · exact Eventually.of_forall fun _ _ h => h.elim
    · intro S T hST hT
      exact hT.mono fun i hi p hp => hi p (hST hp)
    · intro S T hS hT
      filter_upwards [hS, hT] with i hiS hiT p hp
      rcases hp with hp | hp
      · exact hiS p hp
      · exact hiT p hp
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      by_cases hxy : x = y
      · subst y
        obtain ⟨U, hU, hUi⟩ := hlocal x hx
        refine ⟨U ×ˢ U, ?_, ?_⟩
        · rw [nhdsWithin_prod_eq]
          exact prod_mem_prod hU hU
        · exact hUi.mono fun i hi p hp => hi hp.1 hp.2
      · obtain ⟨A, B, hA, hB, hAB⟩ := t2_separation_nhds (fun h => hxy (hinj hx hy h))
        obtain ⟨I, hI, U, hU, hIU⟩ := mem_prod_iff.mp ((hjoint x hx).eventually hA)
        obtain ⟨J, hJ, V, hV, hJV⟩ := mem_prod_iff.mp ((hjoint y hy).eventually hB)
        refine ⟨U ×ˢ V, ?_, ?_⟩
        · rw [nhdsWithin_prod_eq]
          exact prod_mem_prod hU hV
        · filter_upwards [hI, hJ] with i hi hj p hp hcollision
          have ha : q i (F i p.1) ∈ A :=
            hIU (show (i, p.1) ∈ I ×ˢ U from ⟨hi, hp.1⟩)
          have hb : q i (F i p.2) ∈ B :=
            hJV (show (i, p.2) ∈ J ×ˢ V from ⟨hj, hp.2⟩)
          rw [← hcollision] at hb
          exact False.elim (Set.disjoint_left.mp hAB ha hb)
  exact hpair.mono fun i hi x hx y hy hxy => hi (x, y) ⟨hx, hy⟩ hxy

end IsCompact
