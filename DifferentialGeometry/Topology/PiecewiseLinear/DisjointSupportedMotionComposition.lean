/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport

open Function Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem homeomorph_apply_mem_iff_of_eqOn_id_compl {Y : Type*} [TopologicalSpace Y] (φ : Y ≃ₜ Y)
    {K T : Set Y} (hfix : EqOn φ id Kᶜ) (hKT : K ⊆ T) (y : Y) : φ y ∈ T ↔ y ∈ T := by
  by_cases hy : y ∈ K
  · have hφy : φ y ∈ K := by
      by_contra hnot
      have h1 : φ (φ y) = φ y := hfix hnot
      have h2 : φ y = y := φ.injective h1
      rw [h2] at hnot
      exact hnot hy
    exact ⟨fun _ => hKT hy, fun _ => hKT hφy⟩
  · rw [hfix hy, id_eq]

theorem exists_homeomorph_of_finite_disjoint_supported_isPLOn {ι M N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [TopologicalSpace N] [T2Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] (s : Finset ι) (K O : ι → Set N)
    (φ : ι → N ≃ₜ N) (hdis : Pairwise (Disjoint on K)) (hfix : ∀ i ∈ s, EqOn (φ i) id (K i)ᶜ)
    (hK : ∀ i ∈ s, IsClosed (K i)) (hO : ∀ i ∈ s, IsOpen (O i)) (hKO : ∀ i ∈ s, K i ⊆ O i)
    (hφ : ∀ i ∈ s, IsPLOn 3 3 (φ i) (O i)) :
    ∃ Φ : N ≃ₜ N, (∀ i ∈ s, EqOn Φ (φ i) (K i)) ∧ EqOn Φ id (⋃ i ∈ s, K i)ᶜ ∧
      ∀ {d : ℕ} {D Bd : Set M} (f : M → N), IsPLHomeomorphInto 3 f D → IsPLCellOn d D Bd →
        IsPLHomeomorphInto 3 (Φ ∘ f) D := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Homeomorph.refl N, ?_, fun _ _ => rfl, ?_⟩
    · simp
    · intro d D Bd f hf _
      have hcomp : ⇑(Homeomorph.refl N) ∘ f = f := rfl
      rw [hcomp]
      exact hf
  | insert i s hi ih =>
    obtain ⟨Φ, hΦeq, hΦfix, hΦpl⟩ := ih
      (fun j hj => hfix j (Finset.mem_insert_of_mem hj))
      (fun j hj => hK j (Finset.mem_insert_of_mem hj))
      (fun j hj => hO j (Finset.mem_insert_of_mem hj))
      (fun j hj => hKO j (Finset.mem_insert_of_mem hj))
      (fun j hj => hφ j (Finset.mem_insert_of_mem hj))
    refine ⟨Φ.trans (φ i), ?_, ?_, ?_⟩
    · intro j hj x hx
      rcases Finset.mem_insert.mp hj with hji | hj
      · rw [hji] at hx ⊢
        have hxout : x ∉ ⋃ j ∈ s, K j := by
          intro hxU
          obtain ⟨j', hj', hxj'⟩ := mem_iUnion₂.mp hxU
          exact Set.disjoint_left.mp (hdis (show i ≠ j' from fun heq => hi (heq.symm ▸ hj')))
            hx hxj'
        change φ i (Φ x) = φ i x
        rw [hΦfix hxout, id_eq]
      · have hji : j ≠ i := fun heq => hi (heq ▸ hj)
        have hy : φ j x ∈ K j := (homeomorph_apply_mem_iff_of_eqOn_id_compl (φ j)
          (hfix j (Finset.mem_insert_of_mem hj)) Subset.rfl x).mpr hx
        change φ i (Φ x) = φ j x
        rw [hΦeq j hj hx]
        exact hfix i (Finset.mem_insert_self _ _) (Set.disjoint_left.mp (hdis hji) hy)
    · intro x hx
      have hxi : x ∉ K i := fun hxi => hx (mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, hxi⟩)
      have hxs : x ∉ ⋃ j ∈ s, K j := by
        intro hxU
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxU
        exact hx (mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, hxj⟩)
      change φ i (Φ x) = x
      rw [hΦfix hxs, id_eq, hfix i (Finset.mem_insert_self _ _) hxi, id_eq]
    · intro d D Bd f hf hD
      have h2 := (hΦpl f hf hD).postcomp_of_supported_isPLOn hD (φ i)
        (hφ i (Finset.mem_insert_self _ _)) (hO i (Finset.mem_insert_self _ _))
        (hK i (Finset.mem_insert_self _ _)) (hKO i (Finset.mem_insert_self _ _))
        (hfix i (Finset.mem_insert_self _ _))
      have hcomp : ⇑(Φ.trans (φ i)) ∘ f = ⇑(φ i) ∘ (⇑Φ ∘ f) :=
        funext fun x => Homeomorph.trans_apply Φ (φ i) (f x)
      rw [hcomp]
      exact h2

namespace SupportedHomeomorphFamily

variable {ι V Y : Type*} [TopologicalSpace Y] {tgt : ι → V} {K : ι → Set Y} {ψ : ι → Y ≃ₜ Y}
  {Ψ : V → Y ≃ₜ Y}

theorem apply_of_forall_notMem (hΨfix : ∀ v, EqOn (Ψ v) id (⋃ i, ⋃ (_ : tgt i = v), K i)ᶜ)
    {v : V} {y : Y} (hy : ∀ i, tgt i = v → y ∉ K i) : Ψ v y = y :=
  hΨfix v fun hmem => by
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hmem
    exact hy i hi hyi

theorem apply_of_mem_support (hΨeq : ∀ i, EqOn (Ψ (tgt i)) (ψ i) (K i)) {i : ι} {v : V}
    (hi : tgt i = v) {y : Y} (hy : y ∈ K i) : Ψ v y = ψ i y := by
  subst hi
  exact hΨeq i hy

theorem apply_of_forall_notMem_other (hfix : ∀ i, EqOn (ψ i) id (K i)ᶜ)
    (hΨeq : ∀ i, EqOn (Ψ (tgt i)) (ψ i) (K i))
    (hΨfix : ∀ v, EqOn (Ψ v) id (⋃ i, ⋃ (_ : tgt i = v), K i)ᶜ) {i : ι} {y : Y}
    (hy : ∀ j, tgt j = tgt i → j ≠ i → y ∉ K j) : Ψ (tgt i) y = ψ i y := by
  by_cases hyi : y ∈ K i
  · exact hΨeq i hyi
  · rw [apply_of_forall_notMem hΨfix, hfix i hyi, id_eq]
    intro j hj
    by_cases hji : j = i
    · rw [hji]
      exact hyi
    · exact hy j hj hji

theorem apply_mem_iff (hfix : ∀ i, EqOn (ψ i) id (K i)ᶜ)
    (hΨeq : ∀ i, EqOn (Ψ (tgt i)) (ψ i) (K i))
    (hΨfix : ∀ v, EqOn (Ψ v) id (⋃ i, ⋃ (_ : tgt i = v), K i)ᶜ) {v : V} {T : Set Y}
    (hT : ∀ i, tgt i = v → K i ⊆ T ∨ Disjoint (K i) T) (y : Y) : Ψ v y ∈ T ↔ y ∈ T := by
  by_cases hy : ∃ i, tgt i = v ∧ y ∈ K i
  · obtain ⟨i, hi, hyi⟩ := hy
    rw [apply_of_mem_support hΨeq hi hyi]
    have hmem : ψ i y ∈ K i :=
      (homeomorph_apply_mem_iff_of_eqOn_id_compl (ψ i) (hfix i) Subset.rfl y).mpr hyi
    rcases hT i hi with hsub | hdisj
    · exact ⟨fun _ => hsub hyi, fun _ => hsub hmem⟩
    · exact ⟨fun h => (Set.disjoint_left.mp hdisj hmem h).elim,
        fun h => (Set.disjoint_left.mp hdisj hyi h).elim⟩
  · rw [apply_of_forall_notMem hΨfix fun i hi hyi => hy ⟨i, hi, hyi⟩]

theorem image_inter_eq (hfix : ∀ i, EqOn (ψ i) id (K i)ᶜ)
    (hΨeq : ∀ i, EqOn (Ψ (tgt i)) (ψ i) (K i))
    (hΨfix : ∀ v, EqOn (Ψ v) id (⋃ i, ⋃ (_ : tgt i = v), K i)ᶜ) {v : V} {T : Set Y}
    (hT : ∀ i, tgt i = v → Disjoint (K i) T) (A : Set Y) : Ψ v '' A ∩ T = A ∩ T := by
  ext y
  constructor
  · rintro ⟨⟨x, hxA, rfl⟩, hyT⟩
    have hx : ∀ i, tgt i = v → x ∉ K i := by
      intro i hi hxi
      have hmem : Ψ v x ∈ K i := by
        rw [apply_of_mem_support hΨeq hi hxi]
        exact (homeomorph_apply_mem_iff_of_eqOn_id_compl (ψ i) (hfix i) Subset.rfl x).mpr hxi
      exact Set.disjoint_left.mp (hT i hi) hmem hyT
    rw [apply_of_forall_notMem hΨfix hx] at hyT ⊢
    exact ⟨hxA, hyT⟩
  · rintro ⟨hyA, hyT⟩
    have hy : ∀ i, tgt i = v → y ∉ K i := fun i hi hyi => Set.disjoint_left.mp (hT i hi) hyi hyT
    exact ⟨⟨y, hyA, apply_of_forall_notMem hΨfix hy⟩, hyT⟩

theorem image_inter_eq_image_inter (hfix : ∀ i, EqOn (ψ i) id (K i)ᶜ)
    (hdis : ∀ i j, i ≠ j → Disjoint (K i) (K j)) (hΨeq : ∀ i, EqOn (Ψ (tgt i)) (ψ i) (K i))
    (hΨfix : ∀ v, EqOn (Ψ v) id (⋃ i, ⋃ (_ : tgt i = v), K i)ᶜ) {i : ι} {T : Set Y}
    (hT : ∀ j, tgt j = tgt i → j ≠ i → Disjoint (K j) T) (A : Set Y) :
    Ψ (tgt i) '' A ∩ T = ψ i '' A ∩ T := by
  ext y
  constructor
  · rintro ⟨⟨x, hxA, rfl⟩, hyT⟩
    have hx : ∀ j, tgt j = tgt i → j ≠ i → x ∉ K j := by
      intro j hj hji hxj
      have hmem : Ψ (tgt i) x ∈ K j := by
        rw [apply_of_mem_support hΨeq hj hxj]
        exact (homeomorph_apply_mem_iff_of_eqOn_id_compl (ψ j) (hfix j) Subset.rfl x).mpr hxj
      exact Set.disjoint_left.mp (hT j hj hji) hmem hyT
    rw [apply_of_forall_notMem_other hfix hΨeq hΨfix hx] at hyT ⊢
    exact ⟨⟨x, hxA, rfl⟩, hyT⟩
  · rintro ⟨⟨x, hxA, rfl⟩, hyT⟩
    have hx : ∀ j, tgt j = tgt i → j ≠ i → x ∉ K j := by
      intro j hj hji hxj
      have hxi : x ∉ K i := fun hxi => Set.disjoint_left.mp (hdis j i hji) hxj hxi
      have hmem : ψ i x ∈ K j := by
        rw [hfix i hxi, id_eq]
        exact hxj
      exact Set.disjoint_left.mp (hT j hj hji) hmem hyT
    exact ⟨⟨x, hxA, apply_of_forall_notMem_other hfix hΨeq hΨfix hx⟩, hyT⟩

theorem image_subset_union (hfix : ∀ i, EqOn (ψ i) id (K i)ᶜ)
    (hΨeq : ∀ i, EqOn (Ψ (tgt i)) (ψ i) (K i))
    (hΨfix : ∀ v, EqOn (Ψ v) id (⋃ i, ⋃ (_ : tgt i = v), K i)ᶜ) (v : V) (A : Set Y) :
    Ψ v '' A ⊆ A ∪ ⋃ i, ⋃ (_ : tgt i = v), K i := by
  rintro _ ⟨x, hxA, rfl⟩
  by_cases hx : ∃ i, tgt i = v ∧ x ∈ K i
  · obtain ⟨i, hi, hxi⟩ := hx
    rw [apply_of_mem_support hΨeq hi hxi]
    exact Or.inr (mem_iUnion₂.mpr ⟨i, hi,
      (homeomorph_apply_mem_iff_of_eqOn_id_compl (ψ i) (hfix i) Subset.rfl x).mpr hxi⟩)
  · rw [apply_of_forall_notMem hΨfix fun i hi hxi => hx ⟨i, hi, hxi⟩]
    exact Or.inl hxA

end SupportedHomeomorphFamily

end DifferentialGeometry.Topology.PiecewiseLinear
