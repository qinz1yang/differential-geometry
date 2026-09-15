import DifferentialGeometry.Topology.Compactness.EventualLocality
import Mathlib.Topology.Compactness.LocallyCompact

open Set Filter

theorem IsCompact.eventually_mapsTo_iUnion_of_open_cover
    {ι α Q : Type*} {P : ι → Type*} {M : α → Type*}
    [TopologicalSpace Q] [∀ i, TopologicalSpace (P i)]
    [∀ i, LocallyCompactSpace (P i)]
    {K W : Set Q} {l : Filter α} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (e : ∀ i, P i → Q) (he : ∀ i, Continuous (e i)) (heopen : ∀ i, IsOpenMap (e i))
    (hcover : ∀ q ∈ K, ∃ i p, e i p = q)
    (F : ∀ a, Q → M a) (T : ι → ∀ a, Set (M a))
    (hcapture : ∀ i (L : Set (P i)), IsCompact L → L ⊆ e i ⁻¹' W →
      ∀ᶠ a in l, MapsTo (F a ∘ e i) L (T i a)) :
    ∀ᶠ a in l, MapsTo (F a) K (⋃ i, T i a) := by
  have hlocal : ∀ q ∈ K, ∃ O : Set Q, IsOpen O ∧ q ∈ O ∧ O ⊆ W ∧
      ∀ᶠ a in l, ∀ y ∈ O, F a y ∈ ⋃ i, T i a := by
    intro q hq
    obtain ⟨i, p, rfl⟩ := hcover q hq
    obtain ⟨L, hL, hpL, hLW⟩ := exists_compact_subset
      (hW.preimage (he i)) (hKW hq)
    refine ⟨e i '' interior L, heopen i _ isOpen_interior, ⟨p, hpL, rfl⟩, ?_, ?_⟩
    · rintro q ⟨p, hp, rfl⟩
      exact hLW (interior_subset hp)
    · filter_upwards [hcapture i L hL hLW] with a ha
      rintro q ⟨p, hp, rfl⟩
      exact mem_iUnion.mpr ⟨i, ha (interior_subset hp)⟩
  obtain ⟨O, _, hKO, _, hO⟩ := hK.exists_open_eventually_forall hlocal
  exact hO.mono fun a ha q hq => ha q (hKO hq)
