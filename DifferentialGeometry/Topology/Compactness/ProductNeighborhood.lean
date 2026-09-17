import Mathlib.Topology.Compactness.LocallyCompact

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
