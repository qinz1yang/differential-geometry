/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraSkeleton

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

open Classical in
theorem Section34CutFrame.exists_vertexIndex_path
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {u v : Ea} (huv : u ≠ v)
    (huvK : ({u, v} : Finset Ea) ∈ 𝒦.complex.faces) :
    ∃ (n : ℕ) (w : ℕ → Section34VertexIndex 𝒦 𝒦')
      (e : ℕ → Section34EdgeIndex 𝒦 𝒦'),
      0 < n ∧ (w 0).1 = {u} ∧ (w n).1 = {v} ∧
      (∀ i ≤ n, ∃ p ∈ segment ℝ u v, (w i).1 = {p} ∧ (0 < i → i < n → p ≠ u ∧ p ≠ v)) ∧
      (∀ i < n, (e i).1 = (w i).1 ∪ (w (i + 1)).1) ∧
      (∀ i ≤ n, ∀ j ≤ n, w i = w j → i = j) ∧
      (∀ w' : Section34VertexIndex 𝒦 𝒦', (∃ p ∈ segment ℝ u v, w'.1 = {p}) →
        ∃ i ≤ n, w' = w i) ∧
      ∀ i ≤ n, ∀ j ≤ n, i + 1 < j → ∀ e' : Section34EdgeIndex 𝒦 𝒦',
        (w i).1 ⊆ e'.1 → (w j).1 ⊆ e'.1 → False := by
  classical
  obtain ⟨-, hsub, hmap, -⟩ := id hcut
  obtain ⟨n, c, hn, hc0, hcn, hmono, hvert, hedge, hsurj, hK'edge⟩ :=
    𝒦.exists_path_of_edge 𝒦' hsub huv huvK
  set L := AffineMap.lineMap (k := ℝ) u v
  have hLinj : Function.Injective L := AffineMap.lineMap_injective ℝ huv
  have hseg : segment ℝ u v = L '' Icc 0 1 := segment_eq_image_lineMap ℝ u v
  have hcIcc : ∀ i ≤ n, c i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    have h0 := hmono.monotoneOn (show 0 ∈ Iic n from Nat.zero_le n) (show i ∈ Iic n from hi)
      (Nat.zero_le i)
    have h1 := hmono.monotoneOn (show i ∈ Iic n from hi)
      (show n ∈ Iic n from Set.mem_Iic.mpr le_rfl) hi
    rw [hc0] at h0
    rw [hcn] at h1
    exact ⟨h0, h1⟩
  have hpt : ∀ i ≤ n, L (c i) ∈ segment ℝ u v := fun i hi => hseg ▸ ⟨c i, hcIcc i hi, rfl⟩
  have hgraph : ∀ {p}, p ∈ segment ℝ u v → 𝒦.map p ∈ graphSkeletonSpace 𝒦 :=
    fun hp => map_mem_graphSkeletonSpace_of_mem_segment huvK hp
  have hw : ∀ i ≤ n, ∃ w' : Section34VertexIndex 𝒦 𝒦', w'.1 = {L (c i)} := fun i hi =>
    exists_section34VertexIndex_eq_singleton hmap (hvert i hi) (hgraph (hpt i hi))
  set w : ℕ → Section34VertexIndex 𝒦 𝒦' := fun i =>
    if h : i ≤ n then Classical.choose (hw i h) else Classical.choose (hw 0 (Nat.zero_le n))
  have hwspec : ∀ i ≤ n, (w i).1 = {L (c i)} := fun i hi => by
    change (if h : i ≤ n then Classical.choose (hw i h)
      else Classical.choose (hw 0 (Nat.zero_le n))).1 = _
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hw i hi)
  have hinj : ∀ i ≤ n, ∀ j ≤ n, c i = c j → i = j := fun i hi j hj h =>
    hmono.injOn (show i ∈ Iic n from hi) (show j ∈ Iic n from hj) h
  have hne : ∀ i < n, L (c i) ≠ L (c (i + 1)) := fun i hi h =>
    absurd (hinj i hi.le (i + 1) hi (hLinj h)) (by omega)
  have he : ∀ i < n, ∃ e' : Section34EdgeIndex 𝒦 𝒦', e'.1 = {L (c i), L (c (i + 1))} :=
    fun i hi => exists_section34EdgeIndex_eq_pair hmap (hne i hi) (hedge i hi)
      (fun z hz => hgraph ((convex_segment u v).segment_subset
        (hpt i hi.le) (hpt (i + 1) hi) hz))
  set e : ℕ → Section34EdgeIndex 𝒦 𝒦' := fun i =>
    if h : i < n then Classical.choose (he i h) else Classical.choose (he 0 hn)
  have hespec : ∀ i < n, (e i).1 = {L (c i), L (c (i + 1))} := fun i hi => by
    change (if h : i < n then Classical.choose (he i h) else Classical.choose (he 0 hn)).1 = _
    rw [dite_eq_left hi]
    exact Classical.choose_spec (he i hi)
  refine ⟨n, w, e, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwspec 0 (Nat.zero_le n), hc0, AffineMap.lineMap_apply_zero]
  · rw [hwspec n le_rfl, hcn, AffineMap.lineMap_apply_one]
  · intro i hi
    refine ⟨L (c i), hpt i hi, hwspec i hi, fun hi0 hin => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [← AffineMap.lineMap_apply_zero (k := ℝ) u v, ← hc0] at h
      exact absurd (hinj i hi 0 (Nat.zero_le n) (hLinj h)) (by omega)
    · rw [← AffineMap.lineMap_apply_one (k := ℝ) u v, ← hcn] at h
      exact absurd (hinj i hi n le_rfl (hLinj h)) (by omega)
  · intro i hi
    rw [hespec i hi, hwspec i hi.le, hwspec (i + 1) hi, Finset.insert_eq]
  · intro i hi j hj h
    have h' := congrArg Subtype.val h
    rw [hwspec i hi, hwspec j hj] at h'
    exact hinj i hi j hj (hLinj (Finset.singleton_injective h'))
  · rintro w' ⟨p, hp, hw'⟩
    rw [hseg] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    obtain ⟨i, hi, hct⟩ := hsurj t ht (hw' ▸ w'.2.1)
    exact ⟨i, hi, Subtype.ext (by rw [hw', hwspec i hi, hct])⟩
  · intro i hi j hj hij e' hie hje
    rw [hwspec i hi] at hie
    rw [hwspec j hj] at hje
    have hij' : L (c i) ≠ L (c j) := fun h => absurd (hinj i hi j hj (hLinj h)) (by omega)
    have hpair : ({L (c i), L (c j)} : Finset Ea) = e'.1 := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hie (Finset.mem_singleton_self _)
        · rw [Finset.mem_singleton.mp hz]
          exact hje (Finset.mem_singleton_self _)
      · rw [e'.2.2.1, Finset.card_pair hij']
    have hconv : convexHull ℝ (e'.1 : Set Ea) ⊆ segment ℝ u v := by
      rw [← hpair, Finset.coe_pair, convexHull_pair]
      exact (convex_segment u v).segment_subset (hpt i hi) (hpt j hj)
    obtain ⟨m, hm, hme⟩ := hK'edge e'.1 e'.2.1 hconv e'.2.2.1
    rw [← hpair] at hme
    have hmem : L (c i) ∈ ({L (c m), L (c (m + 1))} : Finset Ea) :=
      hme ▸ Finset.mem_insert_self _ _
    have hmem' : L (c j) ∈ ({L (c m), L (c (m + 1))} : Finset Ea) :=
      hme ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hmem with h1 | h1 <;>
      rcases Finset.mem_insert.mp hmem' with h2 | h2
    · exact hij' (h1.trans h2.symm)
    · have e1 := hinj i hi m hm.le (hLinj h1)
      have e2 := hinj j hj (m + 1) hm (hLinj (Finset.mem_singleton.mp h2))
      omega
    · have e1 := hinj i hi (m + 1) hm (hLinj (Finset.mem_singleton.mp h1))
      have e2 := hinj j hj m hm.le (hLinj h2)
      omega
    · exact hij' ((Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm)

open Classical in
theorem Section34CutFrame.exists_edgeIndex_mem_subset_segment
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {u v : Ea} (huv : u ≠ v)
    (huvK : ({u, v} : Finset Ea) ∈ 𝒦.complex.faces) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦', u ∈ e.1 ∧
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ u v ∧
      ∀ e' : Section34EdgeIndex 𝒦 𝒦', u ∈ e'.1 →
        convexHull ℝ (e'.1 : Set Ea) ⊆ segment ℝ u v → e' = e := by
  classical
  obtain ⟨-, hsub, hmap, -⟩ := id hcut
  obtain ⟨n, c, hn, hc0, hcn, hmono, -, hedge, -, hsurj⟩ :=
    𝒦.exists_path_of_edge 𝒦' hsub huv huvK
  let L := AffineMap.lineMap (k := ℝ) u v
  have hLinj : Function.Injective L := AffineMap.lineMap_injective ℝ huv
  have hinj : ∀ i ≤ n, ∀ j ≤ n, c i = c j → i = j := fun i hi j hj hij =>
    hmono.injOn (show i ∈ Iic n from hi) (show j ∈ Iic n from hj) hij
  have hcIcc : ∀ i ≤ n, c i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    have h0 := hmono.monotoneOn (show 0 ∈ Iic n from Nat.zero_le n)
      (show i ∈ Iic n from hi) (Nat.zero_le i)
    have h1 := hmono.monotoneOn (show i ∈ Iic n from hi)
      (show n ∈ Iic n from Set.mem_Iic.mpr le_rfl) hi
    exact ⟨hc0 ▸ h0, hcn ▸ h1⟩
  have hpt : ∀ i ≤ n, L (c i) ∈ segment ℝ u v := fun i hi =>
    (segment_eq_image_lineMap ℝ u v).symm ▸ ⟨c i, hcIcc i hi, rfl⟩
  have hne : L (c 0) ≠ L (c 1) := fun h =>
    absurd (hinj 0 (Nat.zero_le n) 1 hn (hLinj h)) (by omega)
  have heconv : convexHull ℝ ({L (c 0), L (c 1)} : Set Ea) ⊆ segment ℝ u v := by
    rw [convexHull_pair]
    exact (convex_segment u v).segment_subset (hpt 0 (Nat.zero_le n)) (hpt 1 hn)
  obtain ⟨e, he⟩ := exists_section34EdgeIndex_eq_pair hmap hne (hedge 0 hn)
    (fun z hz => map_mem_graphSkeletonSpace_of_mem_segment huvK
      ((convex_segment u v).segment_subset (hpt 0 (Nat.zero_le n)) (hpt 1 hn) hz))
  have hL0 : L (c 0) = u := by rw [hc0]; exact AffineMap.lineMap_apply_zero u v
  refine ⟨e, ?_, ?_, ?_⟩
  · rw [he, hL0]
    exact Finset.mem_insert_self _ _
  · rw [he, Finset.coe_pair]
    exact heconv
  · intro e' hue' he'
    obtain ⟨i, hi, hei⟩ := hsurj e'.1 e'.2.1 he' e'.2.2.1
    have hu := hue'
    rw [hei] at hu
    change u ∈ ({L (c i), L (c (i + 1))} : Finset Ea) at hu
    rw [← hL0] at hu
    have hi0 : i = 0 := by
      rcases Finset.mem_insert.mp hu with h | h
      · exact (hinj 0 (Nat.zero_le n) i hi.le (hLinj h)).symm
      · have hbad := hinj 0 (Nat.zero_le n) (i + 1) hi
          (hLinj (Finset.mem_singleton.mp h))
        omega
    exact Subtype.ext (by rw [hei, hi0, he])

end DifferentialGeometry.Topology.PiecewiseLinear
