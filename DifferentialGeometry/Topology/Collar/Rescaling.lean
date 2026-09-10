import Mathlib.Topology.Homeomorph.Lemmas
import DifferentialGeometry.Topology.Maps.CompactModification
import Mathlib.Topology.Instances.Real.Lemmas

open Set Function Topology Filter
set_option autoImplicit false
noncomputable section
namespace Poincare.Topology.Collar

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X] {ε : ℝ}

def rescale (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) (x : X) : X := by
  classical
  exact if hx : x ∈ range c then
    let q := hc.toHomeomorph.symm ⟨x, hx⟩
    c (q.1, σ q.2)
  else x


theorem rescale_apply (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) (q : B × Icc (0 : ℝ) ε) :
    rescale c hc σ (c q) = c (q.1, σ q.2) := by
  simp only [rescale, dif_pos (mem_range_self q), hc.toHomeomorph_symm_apply]


theorem rescale_of_not_mem (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) {x : X} (hx : x ∉ range c) :
    rescale c hc σ x = x := dif_neg hx

private theorem continuousOn_rescale_range (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) :
    ContinuousOn (rescale c hc σ) (range c) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hh := hc.toHomeomorph.symm.continuous
  have h := hc.continuous.comp (hh.fst.prodMk (σ.continuous.comp hh.snd))
  exact h.congr (fun x => by simp only [Set.domRestrict, rescale, dif_pos x.property, Function.comp_apply])

private theorem rescale_eq_self_off_core (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) {k : ℝ}
    (hσ : ∀ t : Icc (0 : ℝ) ε, k ≤ t.val → σ t = t)
    {x : X} (hx : x ∉ c '' {q | (q.2 : ℝ) ≤ k}) : rescale c hc σ x = x := by
  by_cases hxc : x ∈ range c
  · obtain ⟨q, rfl⟩ := hxc
    have ht : k ≤ q.2.val := le_of_lt (lt_of_not_ge (fun ht => hx ⟨q, ht, rfl⟩))
    rw [rescale_apply, hσ q.2 ht]
  · exact rescale_of_not_mem c hc σ hxc

theorem continuous_rescale [CompactSpace B] [T2Space X]
    (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) {k δ : ℝ}
    (hkδ : k < δ) (hopen : IsOpen (c '' {q | (q.2 : ℝ) < δ}))
    (hσ : ∀ t : Icc (0 : ℝ) ε, k ≤ t.val → σ t = t) :
    Continuous (rescale c hc σ) := by
  let K := c '' {q | (q.2 : ℝ) ≤ k}
  have hK : IsCompact K :=
    ((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact).image
      hc.continuous
  have hKsub : K ⊆ c '' {q | (q.2 : ℝ) < δ} := image_mono (fun _ hq => hq.trans_lt hkδ)
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ c '' {q | (q.2 : ℝ) < δ}
  · exact (continuousOn_rescale_range c hc σ).continuousAt
      (mem_of_superset (hopen.mem_nhds hx) (image_subset_range _ _))
  · have hxK : x ∉ K := fun h => hx (hKsub h)
    apply continuousAt_id.congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact rescale_eq_self_off_core c hc σ hσ hy


theorem isClosedMap_rescale [CompactSpace B] [T2Space X]
    (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) {k δ : ℝ}
    (hkδ : k < δ) (hopen : IsOpen (c '' {q | (q.2 : ℝ) < δ}))
    (hσ : ∀ t : Icc (0 : ℝ) ε, k ≤ t.val → σ t = t) :
    IsClosedMap (rescale c hc σ) := by
  have hK : IsCompact (c '' {q | (q.2 : ℝ) ≤ k}) :=
    ((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact).image
      hc.continuous
  exact Poincare.Topology.isClosedMap_of_compact_modification
    (continuous_rescale c hc σ hkδ hopen hσ) hK
    (fun _ hx => rescale_eq_self_off_core c hc σ hσ hx)


theorem injective_rescale (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) (hσ : Injective σ) :
    Injective (rescale c hc σ) := by
  intro x y h
  by_cases hx : x ∈ range c
  · obtain ⟨p, rfl⟩ := hx
    rw [rescale_apply] at h
    by_cases hy : y ∈ range c
    · obtain ⟨q, rfl⟩ := hy
      rw [rescale_apply] at h
      have hh := hc.injective h
      have hf := congrArg (fun r : B × Icc (0 : ℝ) ε => r.1) hh
      have ht := congrArg (fun r : B × Icc (0 : ℝ) ε => r.2) hh
      exact congrArg c (Prod.ext hf (hσ ht))
    · rw [rescale_of_not_mem c hc σ hy] at h
      exact False.elim (hy ⟨(p.1, σ p.2), h⟩)
  · rw [rescale_of_not_mem c hc σ hx] at h
    by_cases hy : y ∈ range c
    · obtain ⟨q, rfl⟩ := hy
      rw [rescale_apply] at h
      exact False.elim (hx ⟨(q.1, σ q.2), h.symm⟩)
    · rwa [rescale_of_not_mem c hc σ hy] at h


theorem range_rescale (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) {a : ℝ}
    (hσ : range σ = {t : Icc (0 : ℝ) ε | a ≤ t.val}) :
    range (rescale c hc σ) = (range c)ᶜ ∪ c '' {q | a ≤ (q.2 : ℝ)} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : x ∈ range c
    · obtain ⟨q, rfl⟩ := hx
      rw [rescale_apply]
      have ht : σ q.2 ∈ range σ := mem_range_self q.2
      rw [hσ] at ht
      exact Or.inr ⟨(q.1, σ q.2), ht, rfl⟩
    · rw [rescale_of_not_mem c hc σ hx]
      exact Or.inl hx
  · rintro (hy | ⟨q, hq, rfl⟩)
    · exact ⟨y, rescale_of_not_mem c hc σ hy⟩
    · have ht : q.2 ∈ range σ := by rw [hσ]; exact hq
      obtain ⟨t, ht⟩ := ht
      refine ⟨c (q.1, t), ?_⟩
      rw [rescale_apply, ht]

theorem isClosedEmbedding_rescale [CompactSpace B] [T2Space X]
    (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) (hσinj : Injective σ) {k δ : ℝ}
    (hkδ : k < δ) (hopen : IsOpen (c '' {q | (q.2 : ℝ) < δ}))
    (hσ : ∀ t : Icc (0 : ℝ) ε, k ≤ t.val → σ t = t) :
    IsClosedEmbedding (rescale c hc σ) :=
  Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    ⟨continuous_rescale c hc σ hkδ hopen hσ, injective_rescale c hc σ hσinj,
      isClosedMap_rescale c hc σ hkδ hopen hσ⟩

end Poincare.Topology.Collar
