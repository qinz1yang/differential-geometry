import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

open Set

theorem ContinuousOn.exists_compact_prod_mapsTo
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] {f : A × X → Y} {D : Set (A × X)}
    (hf : ContinuousOn f D) (hD : IsOpen D)
    {T : Set A} {K : Set X} (hT : IsCompact T) (hK : IsCompact K)
    (hsource : T ×ˢ K ⊆ D) {N : Set Y} (hN : IsOpen N)
    (htrace : MapsTo f (T ×ˢ K) N) :
    ∃ K' : Set X, IsCompact K' ∧ K ⊆ interior K' ∧
      T ×ˢ K' ⊆ D ∧ MapsTo f (T ×ˢ K') N := by
  obtain ⟨V, W, _, hW, hTV, hKW, hVW⟩ := generalized_tube_lemma hT hK
    (hf.isOpen_inter_preimage hD hN) (fun p hp => ⟨hsource hp, htrace hp⟩)
  obtain ⟨K', hK', hKK', hK'W⟩ := exists_compact_between hK hW hKW
  have hprod : T ×ˢ K' ⊆ D ∩ f ⁻¹' N :=
    fun p hp => hVW ⟨hTV hp.1, hK'W hp.2⟩
  exact ⟨K', hK', hKK', (fun p hp => (hprod hp).1), fun p hp => (hprod hp).2⟩

section

variable {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X]

theorem IsOpen.setOf_forall_mem_of_compactSpace [CompactSpace T]
    {U : Set (T × X)} (hU : IsOpen U) :
    IsOpen {x : X | ∀ t : T, (t, x) ∈ U} := by
  simpa only [kernImage, Prod.forall, forall_eq] using
    (isClosedMap_iff_kernImage.mp
      (isClosedMap_snd_of_compactSpace : IsClosedMap (Prod.snd : T × X → X)) hU)

theorem UpperSemicontinuous.isOpen_setOf_forall_lt [CompactSpace T] [Preorder Y]
    {f : T × X → Y} (hf : UpperSemicontinuous f) (C : Y) :
    IsOpen {x : X | ∀ t : T, f (t, x) < C} :=
  (hf.isOpen_preimage C).setOf_forall_mem_of_compactSpace

theorem UpperSemicontinuous.exists_open_superset_forall_lt [CompactSpace T] [Preorder Y]
    {f : T × X → Y} (hf : UpperSemicontinuous f) {K : Set X} {C : Y}
    (hK : ∀ t, ∀ x ∈ K, f (t, x) < C) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ ∀ t, ∀ x ∈ U, f (t, x) < C := by
  refine ⟨{x | ∀ t, f (t, x) < C}, hf.isOpen_setOf_forall_lt C, ?_, ?_⟩
  · exact fun x hx t => hK t x hx
  · exact fun t x hx => hx t

theorem ContinuousOn.exists_open_superset_forall_lt
    [TopologicalSpace Y] [LinearOrder Y] [OrderTopology Y]
    {f : T × X → Y} {S : Set T} (hf : ContinuousOn f (S ×ˢ univ))
    (hS : IsCompact S) {K : Set X} {C : Y}
    (hK : ∀ t ∈ S, ∀ x ∈ K, f (t, x) < C) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ ∀ t ∈ S, ∀ x ∈ U, f (t, x) < C := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hres : Continuous (fun p : S × X => f (p.1.1, p.2)) :=
    hf.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun p => ⟨p.1.2, mem_univ _⟩)
  obtain ⟨U, hU, hKU, hbound⟩ := hres.upperSemicontinuous.exists_open_superset_forall_lt
    (K := K) (C := C) (fun t x hx => hK t t.2 x hx)
  exact ⟨U, hU, hKU, fun t ht x hx => hbound ⟨t, ht⟩ x hx⟩

theorem ContinuousOn.exists_pos_radius_open_superset_forall_lt
    [TopologicalSpace Y] [LinearOrder Y] [OrderTopology Y]
    {f : T × (ℝ × X) → Y} {S : Set T}
    (hf : ContinuousOn f (S ×ˢ univ)) (hS : IsCompact S)
    {K : Set X} (hK : IsCompact K) {r : ℝ} {C : Y}
    (hbound : ∀ t ∈ S, ∀ x ∈ K, f (t, (r, x)) < C) :
    ∃ η : ℝ, 0 < η ∧ ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧
      ∀ t ∈ S, ∀ s ∈ Ioo (r - η) (r + η), ∀ x ∈ V, f (t, (s, x)) < C := by
  obtain ⟨W, hW, hKW, hb⟩ := hf.exists_open_superset_forall_lt hS
    (K := ({r} : Set ℝ) ×ˢ K) (C := C) (by
      rintro t ht ⟨s, x⟩ ⟨hs, hx⟩
      rcases hs with rfl
      exact hbound t ht x hx)
  obtain ⟨A, V, hA, hV, hrA, hKV, hAV⟩ :=
    generalized_tube_lemma isCompact_singleton hK hW hKW
  obtain ⟨η, hη, hηA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hrA (mem_singleton r)))
  refine ⟨η, hη, V, hV, hKV, ?_⟩
  intro t ht s hs x hx
  apply hb t ht (s, x) (hAV ⟨hηA ?_, hx⟩)
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

end
