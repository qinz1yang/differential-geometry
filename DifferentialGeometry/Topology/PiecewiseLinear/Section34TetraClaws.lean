/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraPaths

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

namespace SimplicialComplex

variable {K : Geometry.SimplicialComplex ℝ Ea}

open Classical in
theorem segment_inter_segment_subset {x y u v : Ea}
    (hxy : ({x, y} : Finset Ea) ∈ K.faces) (huv : ({u, v} : Finset Ea) ∈ K.faces) :
    segment ℝ x y ∩ segment ℝ u v ⊆ convexHull ℝ (({x, y} : Set Ea) ∩ {u, v}) := by
  have h := K.inter_subset_convexHull hxy huv
  rwa [Finset.coe_pair, Finset.coe_pair, convexHull_pair, convexHull_pair] at h

open Classical in
theorem segment_inter_segment_subset_singleton {t : Finset Ea} (ht : t ∈ K.faces)
    {a b c : Ea} (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hbc : b ≠ c) :
    segment ℝ a b ∩ segment ℝ a c ⊆ {a} := by
  have hface : ∀ {u v : Ea}, u ∈ t → v ∈ t → ({u, v} : Finset Ea) ∈ K.faces := fun hu hv =>
    K.down_closed ht (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
      (Finset.insert_nonempty _ _)
  intro z hz
  have h := segment_inter_segment_subset (hface ha hb) (hface ha hc) hz
  have hset : ({a, b} : Set Ea) ∩ {a, c} ⊆ {a} := by
    rintro u ⟨hu1, hu2⟩
    rcases hu1 with hu1 | hu1
    · rw [hu1]
      exact mem_singleton _
    · rw [mem_singleton_iff.mp hu1] at hu2 ⊢
      rcases hu2 with h' | h'
      · rw [h']
        exact mem_singleton _
      · exact absurd (mem_singleton_iff.mp h') hbc
  have h' := convexHull_mono hset h
  rwa [convexHull_singleton] at h'

open Classical in
theorem disjoint_segment_segment {t : Finset Ea} (ht : t ∈ K.faces)
    {a b c d : Ea} (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hd : d ∈ t) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : Disjoint (segment ℝ a b) (segment ℝ c d) := by
  have hface : ∀ {u v : Ea}, u ∈ t → v ∈ t → ({u, v} : Finset Ea) ∈ K.faces := fun hu hv =>
    K.down_closed ht (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
      (Finset.insert_nonempty _ _)
  refine Set.disjoint_left.mpr fun z hz hz' => ?_
  have h := segment_inter_segment_subset (hface ha hb) (hface hc hd) ⟨hz, hz'⟩
  have hset : ({a, b} : Set Ea) ∩ {c, d} = ∅ := by
    refine eq_empty_of_forall_notMem fun u hu => ?_
    rcases hu.1 with hu1 | hu1 <;> rcases hu.2 with hu2 | hu2
    · exact hac (hu1.symm.trans hu2)
    · exact had (hu1.symm.trans (mem_singleton_iff.mp hu2))
    · exact hbc ((mem_singleton_iff.mp hu1).symm.trans hu2)
    · exact hbd ((mem_singleton_iff.mp hu1).symm.trans (mem_singleton_iff.mp hu2))
  rw [hset, convexHull_empty] at h
  exact h

open Classical in
theorem mem_claw_or_mem_claw_of_mem_segment {t : Finset Ea} {a b c d : Ea}
    (htabcd : t = {a, b, c, d}) {x y p : Ea} (hx : x ∈ t) (hy : y ∈ t)
    (hp : p ∈ segment ℝ x y) :
    (p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨ (p ∈ segment ℝ b d ∧ p ≠ d)) ∨
      (p ∈ segment ℝ d c ∨ (p ∈ segment ℝ d a ∧ p ≠ a) ∨ (p ∈ segment ℝ c b ∧ p ≠ b)) := by
  have hab : p ∈ segment ℝ a b → (p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨
      (p ∈ segment ℝ b d ∧ p ≠ d)) ∨
      (p ∈ segment ℝ d c ∨ (p ∈ segment ℝ d a ∧ p ≠ a) ∨ (p ∈ segment ℝ c b ∧ p ≠ b)) := fun h =>
    Or.inl (Or.inl h)
  have hdc : p ∈ segment ℝ d c → (p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨
      (p ∈ segment ℝ b d ∧ p ≠ d)) ∨
      (p ∈ segment ℝ d c ∨ (p ∈ segment ℝ d a ∧ p ≠ a) ∨ (p ∈ segment ℝ c b ∧ p ≠ b)) := fun h =>
    Or.inr (Or.inl h)
  have hac : p ∈ segment ℝ a c → (p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨
      (p ∈ segment ℝ b d ∧ p ≠ d)) ∨
      (p ∈ segment ℝ d c ∨ (p ∈ segment ℝ d a ∧ p ≠ a) ∨ (p ∈ segment ℝ c b ∧ p ≠ b)) := by
    intro h
    by_cases hpc : p = c
    · exact Or.inr (Or.inl (hpc ▸ right_mem_segment ℝ d c))
    · exact Or.inl (Or.inr (Or.inl ⟨h, hpc⟩))
  have had : p ∈ segment ℝ d a → (p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨
      (p ∈ segment ℝ b d ∧ p ≠ d)) ∨
      (p ∈ segment ℝ d c ∨ (p ∈ segment ℝ d a ∧ p ≠ a) ∨ (p ∈ segment ℝ c b ∧ p ≠ b)) := by
    intro h
    by_cases hpa : p = a
    · exact Or.inl (Or.inl (hpa ▸ left_mem_segment ℝ a b))
    · exact Or.inr (Or.inr (Or.inl ⟨h, hpa⟩))
  have hcb : p ∈ segment ℝ c b → (p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨
      (p ∈ segment ℝ b d ∧ p ≠ d)) ∨
      (p ∈ segment ℝ d c ∨ (p ∈ segment ℝ d a ∧ p ≠ a) ∨ (p ∈ segment ℝ c b ∧ p ≠ b)) := by
    intro h
    by_cases hpb : p = b
    · exact Or.inl (Or.inl (hpb ▸ right_mem_segment ℝ a b))
    · exact Or.inr (Or.inr (Or.inr ⟨h, hpb⟩))
  have hbd : p ∈ segment ℝ b d → (p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨
      (p ∈ segment ℝ b d ∧ p ≠ d)) ∨
      (p ∈ segment ℝ d c ∨ (p ∈ segment ℝ d a ∧ p ≠ a) ∨ (p ∈ segment ℝ c b ∧ p ≠ b)) := by
    intro h
    by_cases hpd : p = d
    · exact Or.inr (Or.inl (hpd ▸ left_mem_segment ℝ d c))
    · exact Or.inl (Or.inr (Or.inr ⟨h, hpd⟩))
  rw [htabcd] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  have hsymm : ∀ u v : Ea, p ∈ segment ℝ u v → p ∈ segment ℝ v u := fun u v h => by
    rwa [segment_symm]
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  all_goals first
    | exact hab hp
    | exact hab (hsymm _ _ hp)
    | exact hdc hp
    | exact hdc (hsymm _ _ hp)
    | exact hac hp
    | exact hac (hsymm _ _ hp)
    | exact had hp
    | exact had (hsymm _ _ hp)
    | exact hcb hp
    | exact hcb (hsymm _ _ hp)
    | exact hbd hp
    | exact hbd (hsymm _ _ hp)
    | (rw [segment_same, mem_singleton_iff] at hp
       first
        | exact hab (hp ▸ left_mem_segment ℝ _ _)
        | exact hab (hp ▸ right_mem_segment ℝ _ _)
        | exact hdc (hp ▸ left_mem_segment ℝ _ _)
        | exact hdc (hp ▸ right_mem_segment ℝ _ _))

open Classical in
theorem not_mem_claw_and_mem_claw {t : Finset Ea} (ht : t ∈ K.faces) {a b c d : Ea}
    (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hd : d ∈ t) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {p : Ea}
    (h₁ : p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨ (p ∈ segment ℝ b d ∧ p ≠ d))
    (h₂ : p ∈ segment ℝ d c ∨ (p ∈ segment ℝ d a ∧ p ≠ a) ∨ (p ∈ segment ℝ c b ∧ p ≠ b)) :
    False := by
  have hsymm : ∀ {u v : Ea}, p ∈ segment ℝ u v → p ∈ segment ℝ v u := fun h => by
    rwa [segment_symm]
  have hone : ∀ {u v w : Ea}, u ∈ t → v ∈ t → w ∈ t → v ≠ w → p ∈ segment ℝ u v →
      p ∈ segment ℝ u w → p = u := fun hu hv hw hvw h h' =>
    mem_singleton_iff.mp (segment_inter_segment_subset_singleton ht hu hv hw hvw
      ⟨h, h'⟩)
  rcases h₁ with h₁ | ⟨h₁, h₁c⟩ | ⟨h₁, h₁d⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂a⟩ | ⟨h₂, h₂b⟩
  · exact Set.disjoint_left.mp (disjoint_segment_segment ht ha hb hd hc had hac
      hbd hbc) h₁ h₂
  · exact h₂a (hone ha hb hd hbd h₁ (hsymm h₂))
  · exact h₂b (hone hb ha hc hac (hsymm h₁) (hsymm h₂))
  · exact h₁c (hone hc ha hd had (hsymm h₁) (hsymm h₂))
  · exact h₂a (hone ha hc hd hcd h₁ (hsymm h₂))
  · exact h₁c (hone hc ha hb hab (hsymm h₁) h₂)
  · exact h₁d (hone hd hb hc hbc (hsymm h₁) h₂)
  · exact h₁d (hone hd hb ha hab.symm (hsymm h₁) h₂)
  · exact h₂b (hone hb hd hc hcd.symm h₁ (hsymm h₂))

end SimplicialComplex

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

open Classical in
theorem Section34CutFrame.mem_segment_of_mem_segment_of_ne_of_incident
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) {u v p q : Ea} (hu : u ∈ t) (hv : v ∈ t)
    (hp : p ∈ segment ℝ u v) (hpu : p ≠ u) (hpv : p ≠ v) (e : Section34EdgeIndex 𝒦 𝒦')
    (hpe : p ∈ e.1) (hqe : q ∈ e.1) (het : Section34Incident e.1 t) : q ∈ segment ℝ u v := by
  classical
  obtain ⟨-, hsub, hmap, -⟩ := id hcut
  obtain ⟨u', hu', v', hv', -, hconv⟩ :=
    exists_segment_of_incident_section34EdgeIndex hsub hmap ht e het
  have hpseg : p ∈ segment ℝ u' v' := hconv (subset_convexHull ℝ _ hpe)
  have huv : u ≠ v := by
    rintro rfl
    rw [segment_same] at hp
    exact hpu hp
  have hface : ∀ {a b : Ea}, a ∈ t → b ∈ t → ({a, b} : Finset Ea) ∈ 𝒦.complex.faces := fun ha hb =>
    𝒦.complex.down_closed ht (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb))
      (Finset.insert_nonempty _ _)
  have hmeet := SimplicialComplex.segment_inter_segment_subset (hface hu hv) (hface hu' hv')
    ⟨hp, hpseg⟩
  have hin : ∀ {a b : Ea}, a ∉ ({u', v'} : Set Ea) →
      ({a, b} : Set Ea) ∩ {u', v'} ⊆ {b} := by
    intro a b ha z hz
    rcases hz.1 with rfl | rfl
    · exact absurd hz.2 ha
    · exact mem_singleton _
  have huin : u ∈ ({u', v'} : Set Ea) := by
    by_contra h
    have := convexHull_mono (hin (b := v) h) hmeet
    rw [convexHull_singleton] at this
    exact hpv this
  have hvin : v ∈ ({u', v'} : Set Ea) := by
    by_contra h
    have hmeet' : p ∈ convexHull ℝ (({v, u} : Set Ea) ∩ {u', v'}) := by
      rw [pair_comm]
      exact hmeet
    have := convexHull_mono (hin (b := u) h) hmeet'
    rw [convexHull_singleton] at this
    exact hpu this
  simp only [mem_insert_iff, mem_singleton_iff] at huin hvin
  have hsegeq : segment ℝ u' v' = segment ℝ u v := by
    rcases huin with h1 | h1 <;> rcases hvin with h2 | h2
    · exact absurd (h1.trans h2.symm) huv
    · rw [h1, h2]
    · rw [h1, h2, segment_symm]
    · exact absurd (h1.trans h2.symm) huv
  exact hsegeq ▸ hconv (subset_convexHull ℝ _ hqe)

end DifferentialGeometry.Topology.PiecewiseLinear
