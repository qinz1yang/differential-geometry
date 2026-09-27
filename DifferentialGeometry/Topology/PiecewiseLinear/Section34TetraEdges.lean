/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraClaws

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

open Classical in
theorem Section34CutFrame.mem_segment_of_mem_claw_of_mem_claw
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces)
    {a b c d : Ea} (htabcd : t = {a, b, c, d}) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {e : Section34EdgeIndex 𝒦 𝒦'} {p p' : Ea}
    (hpe : p ∈ e.1) (hp'e : p' ∈ e.1)
    (hp : p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨ (p ∈ segment ℝ b d ∧ p ≠ d))
    (hp' : p' ∈ segment ℝ d c ∨ (p' ∈ segment ℝ d a ∧ p' ≠ a) ∨
      (p' ∈ segment ℝ c b ∧ p' ≠ b)) :
    (a ∈ e.1 ∧ convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ a d) ∨
      (b ∈ e.1 ∧ convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ b c) ∨
      (c ∈ e.1 ∧ convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ c a) ∨
      (d ∈ e.1 ∧ convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ d b) := by
  classical
  obtain ⟨-, hsub, hmap, -⟩ := id hcut
  have ha : a ∈ t := by rw [htabcd]; simp
  have hb : b ∈ t := by rw [htabcd]; simp
  have hc : c ∈ t := by rw [htabcd]; simp
  have hd : d ∈ t := by rw [htabcd]; simp
  have hsegt : ∀ {u v : Ea}, u ∈ t → v ∈ t → segment ℝ u v ⊆ convexHull ℝ (t : Set Ea) :=
    fun hu hv => (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hu)
      (subset_convexHull ℝ _ hv)
  have hpt : p ∈ convexHull ℝ (t : Set Ea) := by
    rcases hp with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hsegt ha hb h
    · exact hsegt ha hc h
    · exact hsegt hb hd h
  have hp't : p' ∈ convexHull ℝ (t : Set Ea) := by
    rcases hp' with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hsegt hd hc h
    · exact hsegt hd ha h
    · exact hsegt hc hb h
  have hpp' : p ≠ p' := by
    rintro rfl
    exact SimplicialComplex.not_mem_claw_and_mem_claw ht ha hb hc hd hab hac had hbc hbd hcd hp hp'
  have hinc : Section34Incident e.1 t := by
    intro z hz
    have hpair : ({p, p'} : Finset Ea) = e.1 := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hpe (Finset.singleton_subset_iff.mpr hp'e))
      (by rw [e.2.2.1, Finset.card_pair hpp'])
    rw [← hpair] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hpt
    · rw [Finset.mem_singleton.mp hz]
      exact hp't
  obtain ⟨x, hx, y, hy, hxy, hconv⟩ :=
    exists_segment_of_incident_section34EdgeIndex hsub hmap ht e hinc
  have hq : ∀ {q : Ea}, q ∈ e.1 → ∀ {u v : Ea}, convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ u v →
      q ∈ segment ℝ u v := fun hq _ _ h => h (subset_convexHull ℝ _ hq)
  have hnot : ∀ {q : Ea},
      (q ∈ segment ℝ a b ∨ (q ∈ segment ℝ a c ∧ q ≠ c) ∨ (q ∈ segment ℝ b d ∧ q ≠ d)) →
      (q ∈ segment ℝ d c ∨ (q ∈ segment ℝ d a ∧ q ≠ a) ∨ (q ∈ segment ℝ c b ∧ q ≠ b)) →
      False := fun h₁ h₂ =>
        SimplicialComplex.not_mem_claw_and_mem_claw ht ha hb hc hd hab hac had hbc hbd hcd h₁ h₂
  have hsab : convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ a b → False := fun h =>
    hnot (Or.inl (hq hp'e h)) hp'
  have hscd : convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ d c → False := fun h =>
    hnot hp (Or.inl (hq hpe h))
  have hsac : convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ c a →
      c ∈ e.1 ∧ convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ c a := by
    intro h
    refine ⟨?_, h⟩
    by_cases hpc : p' = c
    · exact hpc ▸ hp'e
    · have h' : p' ∈ segment ℝ a c := by
        rw [segment_symm]
        exact hq hp'e h
      exact (hnot (Or.inr (Or.inl ⟨h', hpc⟩)) hp').elim
  have hsad : convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ a d →
      a ∈ e.1 ∧ convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ a d := by
    intro h
    refine ⟨?_, h⟩
    by_cases hpa : p = a
    · exact hpa ▸ hpe
    · have h' : p ∈ segment ℝ d a := by
        rw [segment_symm]
        exact hq hpe h
      exact (hnot hp (Or.inr (Or.inl ⟨h', hpa⟩))).elim
  have hsbc : convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ b c →
      b ∈ e.1 ∧ convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ b c := by
    intro h
    refine ⟨?_, h⟩
    by_cases hpb : p = b
    · exact hpb ▸ hpe
    · have h' : p ∈ segment ℝ c b := by
        rw [segment_symm]
        exact hq hpe h
      exact (hnot hp (Or.inr (Or.inr ⟨h', hpb⟩))).elim
  have hsbd : convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ d b →
      d ∈ e.1 ∧ convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ d b := by
    intro h
    refine ⟨?_, h⟩
    by_cases hpd : p' = d
    · exact hpd ▸ hp'e
    · have h' : p' ∈ segment ℝ b d := by
        rw [segment_symm]
        exact hq hp'e h
      exact (hnot (Or.inr (Or.inr ⟨h', hpd⟩)) hp').elim
  have hsw : ∀ {u v : Ea}, convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ u v →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ v u := fun h => by
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

theorem exists_section34VertexIndex_pair_of_mem_edgeIndex
    (e : Section34EdgeIndex 𝒦 𝒦') {u : Ea} (hu : u ∈ e.1) :
    ∃ (w w' : Section34VertexIndex 𝒦 𝒦') (p' : Ea), w.1 = {u} ∧ w'.1 = {p'} ∧
      p' ∈ e.1 ∧ p' ≠ u ∧ w.1 ⊆ e.1 ∧ w'.1 ⊆ e.1 := by
  classical
  have hvert : ∀ {q : Ea}, q ∈ e.1 → ∃ w : Section34VertexIndex 𝒦 𝒦', w.1 = {q} := by
    intro q hq
    have hsub : ({q} : Finset Ea) ⊆ e.1 := Finset.singleton_subset_iff.mpr hq
    refine ⟨⟨{q}, 𝒦'.complex.down_closed e.2.1 hsub (Finset.singleton_nonempty q),
      Finset.card_singleton q, ?_⟩, rfl⟩
    exact (image_mono (convexHull_mono (Finset.coe_subset.mpr hsub))).trans e.2.2.2
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp e.2.2.1
  obtain ⟨p', hp', hp'u⟩ : ∃ p', p' ∈ e.1 ∧ p' ≠ u := by
    have hu' := hu
    rw [he] at hu'
    rcases Finset.mem_insert.mp hu' with rfl | hu'
    · exact ⟨b, he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b), hab.symm⟩
    · have hub := Finset.mem_singleton.mp hu'
      exact ⟨a, he ▸ Finset.mem_insert_self a {b}, fun h => hab (h.trans hub)⟩
  obtain ⟨w, hw⟩ := hvert hu
  obtain ⟨w', hw'⟩ := hvert hp'
  refine ⟨w, w', p', hw, hw', hp', hp'u, ?_, ?_⟩
  · rw [hw]
    exact Finset.singleton_subset_iff.mpr hu
  · rw [hw']
    exact Finset.singleton_subset_iff.mpr hp'

end DifferentialGeometry.Topology.PiecewiseLinear
