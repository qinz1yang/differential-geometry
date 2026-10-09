/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactClawBall

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem segment_inter_segment_subset_singleton_of_mem_faces {t : Finset E3} (ht : t ∈ K.faces)
    {a b c : E3} (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hbc : b ≠ c) :
    segment ℝ a b ∩ segment ℝ a c ⊆ {a} := by
  have hface : ∀ {u v : E3}, u ∈ t → v ∈ t → ({u, v} : Finset E3) ∈ K.faces := fun hu hv =>
    K.down_closed ht (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
      (Finset.insert_nonempty _ _)
  intro z hz
  have h := segment_inter_segment_subset_of_mem_faces (hface ha hb) (hface ha hc) hz
  have hset : ({a, b} : Set E3) ∩ {a, c} ⊆ {a} := by
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

theorem disjoint_segment_segment_of_mem_faces {t : Finset E3} (ht : t ∈ K.faces)
    {a b c d : E3} (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hd : d ∈ t) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : Disjoint (segment ℝ a b) (segment ℝ c d) := by
  have hface : ∀ {u v : E3}, u ∈ t → v ∈ t → ({u, v} : Finset E3) ∈ K.faces := fun hu hv =>
    K.down_closed ht (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
      (Finset.insert_nonempty _ _)
  refine Set.disjoint_left.mpr fun z hz hz' => ?_
  have h := segment_inter_segment_subset_of_mem_faces (hface ha hb) (hface hc hd) ⟨hz, hz'⟩
  have hset : ({a, b} : Set E3) ∩ {c, d} = ∅ := by
    refine eq_empty_of_forall_notMem fun u hu => ?_
    rcases hu.1 with hu1 | hu1 <;> rcases hu.2 with hu2 | hu2
    · exact hac (hu1.symm.trans hu2)
    · exact had (hu1.symm.trans (mem_singleton_iff.mp hu2))
    · exact hbc ((mem_singleton_iff.mp hu1).symm.trans hu2)
    · exact hbd ((mem_singleton_iff.mp hu1).symm.trans (mem_singleton_iff.mp hu2))
  rw [hset, convexHull_empty] at h
  exact h

theorem mem_claw_or_mem_claw_of_mem_segment {t : Finset E3} {a b c d : E3}
    (htabcd : t = {a, b, c, d}) {x y p : E3} (hx : x ∈ t) (hy : y ∈ t)
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
  have hsymm : ∀ u v : E3, p ∈ segment ℝ u v → p ∈ segment ℝ v u := fun u v h => by
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

theorem not_mem_claw_and_mem_claw {t : Finset E3} (ht : t ∈ K.faces) {a b c d : E3}
    (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hd : d ∈ t) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {p : E3}
    (h₁ : p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨ (p ∈ segment ℝ b d ∧ p ≠ d))
    (h₂ : p ∈ segment ℝ d c ∨ (p ∈ segment ℝ d a ∧ p ≠ a) ∨ (p ∈ segment ℝ c b ∧ p ≠ b)) :
    False := by
  have hsymm : ∀ {u v : E3}, p ∈ segment ℝ u v → p ∈ segment ℝ v u := fun h => by
    rwa [segment_symm]
  have hone : ∀ {u v w : E3}, u ∈ t → v ∈ t → w ∈ t → v ≠ w → p ∈ segment ℝ u v →
      p ∈ segment ℝ u w → p = u := fun hu hv hw hvw h h' =>
    mem_singleton_iff.mp (segment_inter_segment_subset_singleton_of_mem_faces ht hu hv hw hvw
      ⟨h, h'⟩)
  rcases h₁ with h₁ | ⟨h₁, h₁c⟩ | ⟨h₁, h₁d⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂a⟩ | ⟨h₂, h₂b⟩
  · exact Set.disjoint_left.mp (disjoint_segment_segment_of_mem_faces ht ha hb hd hc had hac
      hbd hbc) h₁ h₂
  · exact h₂a (hone ha hb hd hbd h₁ (hsymm h₂))
  · exact h₂b (hone hb ha hc hac (hsymm h₁) (hsymm h₂))
  · exact h₁c (hone hc ha hd had (hsymm h₁) (hsymm h₂))
  · exact h₂a (hone ha hc hd hcd h₁ (hsymm h₂))
  · exact h₁c (hone hc ha hb hab (hsymm h₁) h₂)
  · exact h₁d (hone hd hb hc hbc (hsymm h₁) h₂)
  · exact h₁d (hone hd hb ha hab.symm (hsymm h₁) h₂)
  · exact h₂b (hone hb hd hc hcd.symm h₁ (hsymm h₂))

theorem Section34CompactCutFrame.exists_edgeIndex_mem_subset_segment
    (hcut : Section34CompactCutFrame C K K' src srcBd) {u v : E3} (huv : u ≠ v)
    (huvK : ({u, v} : Finset E3) ∈ K.faces) :
    ∃ e : Section34CompactEdgeIndex K K', u ∈ e.1 ∧
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ u v ∧
      ∀ e' : Section34CompactEdgeIndex K K', u ∈ e'.1 →
        convexHull ℝ (e'.1 : Set E3) ⊆ segment ℝ u v → e' = e := by
  classical
  obtain ⟨n, w, e, hn, hw0, -, hwpt, he, -, hsurj, hfar⟩ := hcut.exists_vertexIndex_path huv huvK
  obtain ⟨p₁, hp₁, hw1, -⟩ := hwpt 1 hn
  have he0 : (e 0).1 = {u, p₁} := by
    rw [he 0 hn, hw0, hw1]
    exact (Finset.insert_eq u {p₁}).symm
  refine ⟨e 0, ?_, ?_, ?_⟩
  · rw [he0]
    exact Finset.mem_insert_self u {p₁}
  · rw [he0, Finset.coe_pair, convexHull_pair]
    exact (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hp₁
  · intro e' hue' he'
    obtain ⟨q, hq, hsub⟩ := exists_subset_pair_of_card_le_two e'.2.2.1.le hue'
    have hqu : q ≠ u := by
      intro hqu'
      rw [hqu'] at hsub
      have hcard : e'.1.card ≤ ({u} : Finset E3).card := by
        refine Finset.card_le_card fun z hz => ?_
        have hz' := hsub (Finset.mem_coe.mpr hz)
        simp only [mem_insert_iff, mem_singleton_iff, or_self] at hz'
        exact Finset.mem_singleton.mpr hz'
      rw [e'.2.2.1, Finset.card_singleton] at hcard
      omega
    have hqseg : q ∈ segment ℝ u v := he' (subset_convexHull ℝ _ hq)
    have hqK' : ({q} : Finset E3) ∈ K'.faces :=
      K'.down_closed e'.2.1 (Finset.singleton_subset_iff.mpr hq) (Finset.singleton_nonempty q)
    obtain ⟨wq, hwq⟩ := exists_section34CompactVertexIndex_eq_singleton hqK'
      (e'.2.2.2 (subset_convexHull ℝ _ hq))
    obtain ⟨j, hj, hjq⟩ := hsurj wq ⟨q, hqseg, hwq⟩
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [← hjq, hwq] at hw0
      exact hqu (Finset.singleton_injective hw0)
    have hj1 : j = 1 := by
      by_contra hj1
      refine hfar 0 (Nat.zero_le n) j hj (by omega) e' ?_ ?_
      · rw [hw0]
        exact Finset.singleton_subset_iff.mpr hue'
      · rw [← hjq, hwq]
        exact Finset.singleton_subset_iff.mpr hq
    subst hj1
    have hqp : q = p₁ := by
      rw [← hjq, hwq] at hw1
      exact Finset.singleton_injective hw1
    subst hqp
    refine Subtype.ext (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · rw [he0]
      exact Finset.insert_subset hue' (Finset.singleton_subset_iff.mpr hq)
    · rw [he0, e'.2.2.1, Finset.card_pair hqu.symm]

theorem Section34CompactCutFrame.mem_segment_of_mem_claw_of_mem_claw
    (hcut : Section34CompactCutFrame C K K' src srcBd) {t : Finset E3} (ht : t ∈ K.faces)
    {a b c d : E3} (htabcd : t = {a, b, c, d}) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {e : Section34CompactEdgeIndex K K'} {p p' : E3}
    (hpe : p ∈ e.1) (hp'e : p' ∈ e.1)
    (hp : p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨ (p ∈ segment ℝ b d ∧ p ≠ d))
    (hp' : p' ∈ segment ℝ d c ∨ (p' ∈ segment ℝ d a ∧ p' ≠ a) ∨
      (p' ∈ segment ℝ c b ∧ p' ≠ b)) :
    (a ∈ e.1 ∧ convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a d) ∨
      (b ∈ e.1 ∧ convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ b c) ∨
      (c ∈ e.1 ∧ convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ c a) ∨
      (d ∈ e.1 ∧ convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ d b) := by
  classical
  obtain ⟨-, -, -, -, hsub, -⟩ := id hcut
  have ha : a ∈ t := by rw [htabcd]; simp
  have hb : b ∈ t := by rw [htabcd]; simp
  have hc : c ∈ t := by rw [htabcd]; simp
  have hd : d ∈ t := by rw [htabcd]; simp
  have hsegt : ∀ {u v : E3}, u ∈ t → v ∈ t → segment ℝ u v ⊆ convexHull ℝ (t : Set E3) :=
    fun hu hv => (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hu)
      (subset_convexHull ℝ _ hv)
  have hpt : p ∈ convexHull ℝ (t : Set E3) := by
    rcases hp with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hsegt ha hb h
    · exact hsegt ha hc h
    · exact hsegt hb hd h
  have hp't : p' ∈ convexHull ℝ (t : Set E3) := by
    rcases hp' with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hsegt hd hc h
    · exact hsegt hd ha h
    · exact hsegt hc hb h
  have hpp' : p ≠ p' := by
    rintro rfl
    exact not_mem_claw_and_mem_claw ht ha hb hc hd hab hac had hbc hbd hcd hp hp'
  have hinc : Section34Incident e.1 t := by
    intro z hz
    have hpair : ({p, p'} : Finset E3) = e.1 := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hpe (Finset.singleton_subset_iff.mpr hp'e))
      (by rw [e.2.2.1, Finset.card_pair hpp'])
    rw [← hpair] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hpt
    · rw [Finset.mem_singleton.mp hz]
      exact hp't
  obtain ⟨x, hx, y, hy, hxy, hconv⟩ :=
    exists_segment_of_incident_section34CompactEdgeIndex hsub ht e hinc
  have hq : ∀ {q : E3}, q ∈ e.1 → ∀ {u v : E3}, convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ u v →
      q ∈ segment ℝ u v := fun hq _ _ h => h (subset_convexHull ℝ _ hq)
  have hnot : ∀ {q : E3},
      (q ∈ segment ℝ a b ∨ (q ∈ segment ℝ a c ∧ q ≠ c) ∨ (q ∈ segment ℝ b d ∧ q ≠ d)) →
      (q ∈ segment ℝ d c ∨ (q ∈ segment ℝ d a ∧ q ≠ a) ∨ (q ∈ segment ℝ c b ∧ q ≠ b)) →
      False := fun h₁ h₂ => not_mem_claw_and_mem_claw ht ha hb hc hd hab hac had hbc hbd hcd h₁ h₂
  have hsab : convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a b → False := fun h =>
    hnot (Or.inl (hq hp'e h)) hp'
  have hscd : convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ d c → False := fun h =>
    hnot hp (Or.inl (hq hpe h))
  have hsac : convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ c a →
      c ∈ e.1 ∧ convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ c a := by
    intro h
    refine ⟨?_, h⟩
    by_cases hpc : p' = c
    · exact hpc ▸ hp'e
    · have h' : p' ∈ segment ℝ a c := by
        rw [segment_symm]
        exact hq hp'e h
      exact (hnot (Or.inr (Or.inl ⟨h', hpc⟩)) hp').elim
  have hsad : convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a d →
      a ∈ e.1 ∧ convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a d := by
    intro h
    refine ⟨?_, h⟩
    by_cases hpa : p = a
    · exact hpa ▸ hpe
    · have h' : p ∈ segment ℝ d a := by
        rw [segment_symm]
        exact hq hpe h
      exact (hnot hp (Or.inr (Or.inl ⟨h', hpa⟩))).elim
  have hsbc : convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ b c →
      b ∈ e.1 ∧ convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ b c := by
    intro h
    refine ⟨?_, h⟩
    by_cases hpb : p = b
    · exact hpb ▸ hpe
    · have h' : p ∈ segment ℝ c b := by
        rw [segment_symm]
        exact hq hpe h
      exact (hnot hp (Or.inr (Or.inr ⟨h', hpb⟩))).elim
  have hsbd : convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ d b →
      d ∈ e.1 ∧ convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ d b := by
    intro h
    refine ⟨?_, h⟩
    by_cases hpd : p' = d
    · exact hpd ▸ hp'e
    · have h' : p' ∈ segment ℝ b d := by
        rw [segment_symm]
        exact hq hp'e h
      exact (hnot (Or.inr (Or.inr ⟨h', hpd⟩)) hp').elim
  have hsw : ∀ {u v : E3}, convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ u v →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ v u := fun h => by
    rwa [segment_symm]
  rw [htabcd] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hxy
    | exact (hsab hconv).elim
    | exact (hsab (hsw hconv)).elim
    | exact (hscd hconv).elim
    | exact (hscd (hsw hconv)).elim
    | exact Or.inr (Or.inr (Or.inl (hsac hconv)))
    | exact Or.inr (Or.inr (Or.inl (hsac (hsw hconv))))
    | exact Or.inl (hsad hconv)
    | exact Or.inl (hsad (hsw hconv))
    | exact Or.inr (Or.inl (hsbc hconv))
    | exact Or.inr (Or.inl (hsbc (hsw hconv)))
    | exact Or.inr (Or.inr (Or.inr (hsbd hconv)))
    | exact Or.inr (Or.inr (Or.inr (hsbd (hsw hconv))))

end DifferentialGeometry.Topology.PiecewiseLinear
