/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GenericPlacementSteps

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Helpers

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finrank_direction_affineSpan_image_add_one_of_affineIndependent {s : Finset ι}
    {φ : ι → E} (hs : AffineIndependent ℝ (fun u : s => φ u)) (hne : s.Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (φ '' ↑s)).direction + 1 = s.card := by
  obtain ⟨n, hn⟩ : ∃ n, s.card = n + 1 := ⟨s.card - 1, by have := hne.card_pos; omega⟩
  have h := hs.finrank_vectorSpan (n := n) (by rw [Fintype.card_coe]; exact hn)
  have hrange : Set.range (fun u : s => φ u) = φ '' ↑s := by
    ext y
    simp
  rw [hrange] at h
  rw [direction_affineSpan, h, hn]

theorem ne_of_affineIndependent_of_mem {s : Finset ι} {φ : ι → E}
    (hs : AffineIndependent ℝ (fun u : s => φ u)) {a b : ι} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : φ a ≠ φ b := fun h =>
  hab (congrArg Subtype.val (hs.injective
    (show (fun u : s => φ u) ⟨a, ha⟩ = (fun u : s => φ u) ⟨b, hb⟩ from h)))

theorem notMem_affineSpan_pair_of_affineIndependent {s : Finset ι} {φ : ι → E}
    (hs : AffineIndependent ℝ (fun u : s => φ u)) {a₁ a₂ b : ι} (h₁ : a₁ ∈ s) (h₂ : a₂ ∈ s)
    (hb : b ∈ s) (hb₁ : b ≠ a₁) (hb₂ : b ≠ a₂) : φ b ∉ line[ℝ, φ a₁, φ a₂] := by
  have h := hs.notMem_affineSpan_sdiff ⟨b, hb⟩ {⟨a₁, h₁⟩, ⟨a₂, h₂⟩}
  have hdiff : ({⟨a₁, h₁⟩, ⟨a₂, h₂⟩} : Set s) \ {⟨b, hb⟩} = {⟨a₁, h₁⟩, ⟨a₂, h₂⟩} := by
    apply sdiff_singleton_eq_self
    rintro (h | h)
    · exact hb₁ (congrArg Subtype.val h)
    · exact hb₂ (congrArg Subtype.val h)
  rw [hdiff, image_insert_eq, image_singleton] at h
  exact h

theorem finrank_vectorSpan_pair_le_one (p q : E) :
    Module.finrank ℝ (vectorSpan ℝ ({p, q} : Set E)) ≤ 1 := by
  rw [vectorSpan_pair]
  by_cases h : p -ᵥ q = 0
  · rw [h, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
    omega
  · rw [finrank_span_singleton h]

theorem finrank_vectorSpan_triple_le_two (p q r : E) :
    Module.finrank ℝ (vectorSpan ℝ ({p, q, r} : Set E)) ≤ 2 := by
  have h := finrank_vectorSpan_insert_le_set ℝ ({q, r} : Set E) p
  have h' := finrank_vectorSpan_pair_le_one q r
  omega

theorem dimH_coe_le_finrank_direction [FiniteDimensional ℝ E] (A : AffineSubspace ℝ E) :
    dimH (A : Set E) ≤ Module.finrank ℝ A.direction := by
  rcases (A : Set E).eq_empty_or_nonempty with hA | hA
  · rw [hA, dimH_empty]
    exact zero_le
  · rw [Real.Convex.dimH_eq_finrank_vectorSpan A.convex hA,
      ← AffineSubspace.direction_eq_vectorSpan]

theorem dimH_lt_three_of_finrank_direction_le_two
    (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) (h : Module.finrank ℝ A.direction ≤ 2) :
    dimH (A : Set (EuclideanSpace ℝ (Fin 3))) < 3 := by
  calc dimH (A : Set (EuclideanSpace ℝ (Fin 3))) ≤ Module.finrank ℝ A.direction :=
        dimH_coe_le_finrank_direction A
    _ ≤ ((2 : ℕ) : ENNReal) := by exact_mod_cast h
    _ < 3 := by norm_num

theorem dimH_lt_two_of_finrank_direction_le_one
    (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) (h : Module.finrank ℝ A.direction ≤ 1) :
    dimH (A : Set (EuclideanSpace ℝ (Fin 3))) < 2 := by
  calc dimH (A : Set (EuclideanSpace ℝ (Fin 3))) ≤ Module.finrank ℝ A.direction :=
        dimH_coe_le_finrank_direction A
    _ ≤ ((1 : ℕ) : ENNReal) := by exact_mod_cast h
    _ < 2 := by norm_num

theorem dimH_range_lt_three {f : ℝ × ℝ → EuclideanSpace ℝ (Fin 3)} (hf : ContDiff ℝ 1 f) :
    dimH (range f) < 3 := by
  have h := (hf.differentiable one_ne_zero).dimH_range_le
  rw [Module.finrank_prod, Module.finrank_self] at h
  calc dimH (range f) ≤ ((1 + 1 : ℕ) : ENNReal) := h
    _ < 3 := by norm_num

theorem guard_update_of_forall_notMem_affineSpan [DecidableEq ι] {U Vf Bv T : Finset ι}
    {Afz : Set ι} [DecidablePred (· ∈ Afz)] (hVf : ∀ u, u ∈ Vf ↔ u ∈ U ∧ u ∉ Afz) {v : ι}
    (hvV : v ∈ Vf) {φ : ι → E}
    (hguard : ∀ s ⊆ U, (∀ u ∈ s, u ∈ Vf → u ∈ T) → s.card ≤ 4 → (s ∩ Bv).card ≤ 3 →
      AffineIndependent ℝ (fun u : s.filter (· ∈ Afz) => φ u) →
        AffineIndependent ℝ (fun u : s => φ u))
    {x : E} (hx : ∀ s ⊆ U, v ∈ s → (∀ u ∈ s, u ∈ Vf → u ∈ insert v T) → s.card ≤ 4 →
      (s ∩ Bv).card ≤ 3 → x ∉ affineSpan ℝ (φ '' ↑(s.erase v))) :
    ∀ s ⊆ U, (∀ u ∈ s, u ∈ Vf → u ∈ insert v T) → s.card ≤ 4 → (s ∩ Bv).card ≤ 3 →
      AffineIndependent ℝ (fun u : s.filter (· ∈ Afz) => Function.update φ v x u) →
        AffineIndependent ℝ (fun u : s => Function.update φ v x u) := by
  intro s hsU hfree h4 h3 hfrz
  have hvA : v ∉ Afz := ((hVf v).mp hvV).2
  have hfrz' : AffineIndependent ℝ (fun u : s.filter (· ∈ Afz) => φ u) := by
    have heq : (fun u : s.filter (· ∈ Afz) => Function.update φ v x u) =
        fun u : s.filter (· ∈ Afz) => φ u :=
      funext fun u => Function.update_of_ne
        (fun h : (u : ι) = v => hvA (h ▸ (Finset.mem_filter.mp u.2).2)) x φ
    rwa [heq] at hfrz
  by_cases hvs : v ∈ s
  · have hs' : AffineIndependent ℝ (fun u : s.erase v => φ u) := by
      refine hguard (s.erase v) ((Finset.erase_subset v s).trans hsU) (fun u hu huV => ?_)
        (Finset.card_erase_le.trans h4) ((Finset.card_le_card fun u hu =>
          Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp hu).1,
            (Finset.mem_inter.mp hu).2⟩).trans h3) ?_
      · exact (Finset.mem_insert.mp (hfree u (Finset.mem_of_mem_erase hu) huV)).resolve_left
          (Finset.ne_of_mem_erase hu)
      · have hf : (s.erase v).filter (· ∈ Afz) = s.filter (· ∈ Afz) := by
          rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
          intro h
          exact hvA (Finset.mem_filter.mp h).2
        rw [hf]
        exact hfrz'
    exact affineIndependent_update_of_notMem_affineSpan_erase hvs hs' (hx s hsU hvs hfree h4 h3)
  · have hs : AffineIndependent ℝ (fun u : s => φ u) :=
      hguard s hsU (fun u hu huV => (Finset.mem_insert.mp (hfree u hu huV)).resolve_left
        fun h => hvs (h ▸ hu)) h4 h3 hfrz'
    have heq : (fun u : s => Function.update φ v x u) = fun u : s => φ u :=
      funext fun u => Function.update_of_ne (fun h : (u : ι) = v => hvs (h ▸ u.2)) x φ
    rw [heq]
    exact hs

end Helpers

section Clauses

variable {ι : Type*} [DecidableEq ι]

theorem exists_dimH_lt_tri_update {ιS : Type*} [Finite ιS] {Bv T : Finset ι} {v : ι}
    (φ : ι → EuclideanSpace ℝ (Fin 3)) (S : ιS → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hS : ∀ j, Module.finrank ℝ (S j).direction = 1) (hline : ∀ u ∈ T, ∀ j, φ u ∉ S j)
    (htri : ∀ β ⊆ T, β.card = 3 → ¬β ⊆ Bv → ∀ j, ¬S j ≤ affineSpan ℝ (φ '' ↑β)) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)), dimH B < 3 ∧ ∀ x, x ∉ B →
      ∀ β ⊆ insert v T, β.card = 3 → ¬β ⊆ Bv → ∀ j,
        ¬S j ≤ affineSpan ℝ (Function.update φ v x '' ↑β) := by
  have hK : {k : Finset ι × ιS | k.1 ⊆ insert v T}.Finite :=
    ((insert v T).powerset.finite_toSet.prod finite_univ).subset
      fun k hk => ⟨Finset.mem_powerset.mpr hk, mem_univ _⟩
  refine (exists_dimH_inter_lt_forall_of_finite hK univ (c := 3) (by norm_num)
    (fun k x => k.1.card = 3 → ¬k.1 ⊆ Bv →
      ¬S k.2 ≤ affineSpan ℝ (Function.update φ v x '' ↑k.1)) ?_).elim fun B hBB =>
    ⟨B, by simpa using hBB.1, fun x hx β hβ h3 hβB j =>
      hBB.2 x (mem_univ x) hx (β, j) hβ h3 hβB⟩
  rintro ⟨β, j⟩ hβ
  change β ⊆ insert v T at hβ
  by_cases hvβ : v ∈ β
  · by_cases h3 : β.card = 3
    · obtain ⟨b, hb⟩ : (β.erase v).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hvβ, h3]
        norm_num
      have hbT : b ∈ T := (Finset.mem_insert.mp (hβ (Finset.mem_of_mem_erase hb))).resolve_left
        (Finset.ne_of_mem_erase hb)
      obtain ⟨A, hA, hAx⟩ := exists_affineSubspace_not_le_affineSpan_update hvβ
        (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb) h3.le φ (S j) (hS j)
        (hline b hbT j)
      exact ⟨A, by rw [inter_univ]; exact dimH_lt_three_of_finrank_direction_le_two A hA,
        fun x _ hx _ _ => hAx x hx⟩
    · exact ⟨∅, by simp, fun x _ _ h => absurd h h3⟩
  · refine ⟨∅, by simp, fun x _ _ h3 hβB => ?_⟩
    have himg : Function.update φ v x '' ↑β = φ '' ↑β :=
      image_congr fun u hu => Function.update_of_ne (fun h : u = v => hvβ (h ▸ hu)) x φ
    rw [himg]
    exact htri β (fun u hu => (Finset.mem_insert.mp (hβ hu)).resolve_left
      fun h => hvβ (h ▸ hu)) h3 hβB j

theorem exists_dimH_lt_skeleton_update {ιS : Type*} [Finite ιS] {Bv T : Finset ι} {v : ι}
    (hvB : v ∉ Bv) (φ : ι → EuclideanSpace ℝ (Fin 3))
    (S : ιS → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hS : ∀ j, Module.finrank ℝ (S j).direction = 1)
    (hind : ∀ s ⊆ T, s.card ≤ 3 → AffineIndependent ℝ (fun u : s => φ u))
    (hline : ∀ u ∈ T, ∀ j, φ u ∉ S j)
    (htri : ∀ β ⊆ T, β.card = 3 → ¬β ⊆ Bv → ∀ j, ¬S j ≤ affineSpan ℝ (φ '' ↑β))
    (hskel : ∀ α ⊆ T, ∀ β ⊆ T,
      ((α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1) ∨
        (α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2 ∧ Disjoint α β) ∨
        (α.card = 2 ∧ β.card = 2 ∧ α ⊆ Bv ∧ β ⊆ Bv ∧ Disjoint α β)) →
      ∀ j (w w' : ι → ℝ), (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
        ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
          ∑ u ∈ α, w u • φ u ∉ S j) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)), dimH B < 3 ∧ ∀ x, x ∉ B →
      ∀ α ⊆ insert v T, ∀ β ⊆ insert v T,
        ((α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1) ∨
          (α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2 ∧ Disjoint α β) ∨
          (α.card = 2 ∧ β.card = 2 ∧ α ⊆ Bv ∧ β ⊆ Bv ∧ Disjoint α β)) →
        ∀ j (w w' : ι → ℝ), (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
          ∑ u ∈ β, w' u = 1 →
          ∑ u ∈ α, w u • Function.update φ v x u = ∑ u ∈ β, w' u • Function.update φ v x u →
            ∑ u ∈ α, w u • Function.update φ v x u ∉ S j := by
  have hsubT : ∀ γ ⊆ insert v T, v ∉ γ → γ ⊆ T := fun γ hγ hv u hu =>
    (Finset.mem_insert.mp (hγ hu)).resolve_left fun h => hv (h ▸ hu)
  have hsumeq : ∀ (γ : Finset ι), v ∉ γ → ∀ (w : ι → ℝ) (x : EuclideanSpace ℝ (Fin 3)),
      ∑ u ∈ γ, w u • Function.update φ v x u = ∑ u ∈ γ, w u • φ u := fun γ hv w x =>
    Finset.sum_congr rfl fun u hu => by rw [Function.update_of_ne (fun h : u = v => hv (h ▸ hu))]
  have hsub3 : ∀ γ ⊆ T, γ.card = 3 → ¬γ ⊆ Bv → ∀ j,
      ((S j : Set (EuclideanSpace ℝ (Fin 3))) ∩ affineSpan ℝ (φ '' ↑γ)).Subsingleton :=
    fun γ hγ h3 hB j => inter_subsingleton_of_not_le (hS j).le (htri γ hγ h3 hB j)
  have hsub2 : ∀ γ ⊆ T, γ.card = 2 → ∀ j,
      ((S j : Set (EuclideanSpace ℝ (Fin 3))) ∩ affineSpan ℝ (φ '' ↑γ)).Subsingleton := by
    intro γ hγ h2 j
    obtain ⟨b, hb⟩ : γ.Nonempty := by
      rw [← Finset.card_pos, h2]
      norm_num
    have hrank : Module.finrank ℝ (affineSpan ℝ (φ '' ↑γ)).direction ≤ 1 := by
      have := finrank_direction_affineSpan_image_lt_card ⟨b, hb⟩ φ
      omega
    have hnle : ¬affineSpan ℝ (φ '' ↑γ) ≤ S j := fun hle =>
      hline b (hγ hb) j (hle (subset_affineSpan ℝ _ (mem_image_of_mem φ hb)))
    rw [inter_comm]
    exact inter_subsingleton_of_not_le hrank hnle
  have hK : {k : Finset ι × Finset ι × ιS | k.1 ⊆ insert v T ∧ k.2.1 ⊆ insert v T}.Finite :=
    ((insert v T).powerset.finite_toSet.prod
      ((insert v T).powerset.finite_toSet.prod finite_univ)).subset
      fun k hk => ⟨Finset.mem_powerset.mpr hk.1, Finset.mem_powerset.mpr hk.2, mem_univ _⟩
  refine (exists_dimH_inter_lt_forall_of_finite hK univ (c := 3) (by norm_num)
    (fun k x => ((k.1.card = 3 ∧ k.2.1.card = 3 ∧ ¬k.1 ⊆ Bv ∧ ¬k.2.1 ⊆ Bv ∧
        (k.1 ∩ k.2.1).card ≤ 1) ∨
        (k.1.card = 3 ∧ ¬k.1 ⊆ Bv ∧ k.2.1.card = 2 ∧ Disjoint k.1 k.2.1) ∨
        (k.1.card = 2 ∧ k.2.1.card = 2 ∧ k.1 ⊆ Bv ∧ k.2.1 ⊆ Bv ∧ Disjoint k.1 k.2.1)) →
      ∀ (w w' : ι → ℝ), (∀ u ∈ k.1, 0 < w u) → ∑ u ∈ k.1, w u = 1 →
        (∀ u ∈ k.2.1, 0 < w' u) → ∑ u ∈ k.2.1, w' u = 1 →
        ∑ u ∈ k.1, w u • Function.update φ v x u =
          ∑ u ∈ k.2.1, w' u • Function.update φ v x u →
          ∑ u ∈ k.1, w u • Function.update φ v x u ∉ S k.2.2) ?_).elim fun B hBB =>
    ⟨B, by simpa using hBB.1, fun x hx α hα β hβ hk j w w' =>
      hBB.2 x (mem_univ x) hx (α, β, j) ⟨hα, hβ⟩ hk w w'⟩
  rintro ⟨α, β, j⟩ ⟨hα, hβ⟩
  change α ⊆ insert v T at hα
  change β ⊆ insert v T at hβ
  dsimp only
  by_cases hvα : v ∈ α <;> by_cases hvβ : v ∈ β
  · by_cases hTT : α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1
    · obtain ⟨h3α, h3β, -, -, hint⟩ := hTT
      have hαβ : ∀ u ∈ α, u ∈ β → u = v := fun u hu hu' =>
        Finset.card_le_one.mp hint u (Finset.mem_inter.mpr ⟨hu, hu'⟩) v
          (Finset.mem_inter.mpr ⟨hvα, hvβ⟩)
      obtain ⟨a₁, a₂, ha₁₂, hαe⟩ := Finset.card_eq_two.mp
        (by rw [Finset.card_erase_of_mem hvα, h3α] : (α.erase v).card = 2)
      obtain ⟨b₁, b₂, hb₁₂, hβe⟩ := Finset.card_eq_two.mp
        (by rw [Finset.card_erase_of_mem hvβ, h3β] : (β.erase v).card = 2)
      have ha₁ : a₁ ∈ α.erase v := by
        rw [hαe]
        exact Finset.mem_insert_self _ _
      have ha₂ : a₂ ∈ α.erase v := by
        rw [hαe]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hb₁ : b₁ ∈ β.erase v := by
        rw [hβe]
        exact Finset.mem_insert_self _ _
      have hb₂ : b₂ ∈ β.erase v := by
        rw [hβe]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hT : ∀ {γ : Finset ι} {u : ι}, γ ⊆ insert v T → u ∈ γ.erase v → u ∈ T :=
        fun hγ hu => (Finset.mem_insert.mp (hγ (Finset.mem_of_mem_erase hu))).resolve_left
          (Finset.ne_of_mem_erase hu)
      have hb₁α : b₁ ∉ α := fun h =>
        Finset.ne_of_mem_erase hb₁ (hαβ b₁ h (Finset.mem_of_mem_erase hb₁))
      have hb₁a₁ : b₁ ≠ a₁ := fun h => hb₁α (h ▸ Finset.mem_of_mem_erase ha₁)
      have hb₁a₂ : b₁ ≠ a₂ := fun h => hb₁α (h ▸ Finset.mem_of_mem_erase ha₂)
      have hA3 := hind {a₁, a₂, b₁} (by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact hT hα ha₁
        · exact hT hα ha₂
        · exact hT hβ hb₁) Finset.card_le_three
      have hB2 := hind {b₁, b₂} (by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hT hβ hb₁
        · exact hT hβ hb₂) (Finset.card_le_two.trans (by norm_num))
      have hne_a : φ a₁ ≠ φ a₂ := ne_of_affineIndependent_of_mem hA3 (by simp) (by simp) ha₁₂
      have hne_b : φ b₁ ≠ φ b₂ := ne_of_affineIndependent_of_mem hB2 (by simp) (by simp) hb₁₂
      have hline₁ : φ b₁ ∉ line[ℝ, φ a₁, φ a₂] :=
        notMem_affineSpan_pair_of_affineIndependent hA3 (by simp) (by simp) (by simp) hb₁a₁ hb₁a₂
      obtain ⟨f, hf, hfx⟩ := exists_contDiff_sum_smul_notMem_of_shared_vertex hvα hvβ hαe hβe φ
        hne_a hne_b hline₁ (S j) (hS j)
      refine ⟨(line[ℝ, φ a₁, φ a₂] : Set (EuclideanSpace ℝ (Fin 3))) ∪ line[ℝ, φ b₁, φ b₂] ∪
        affineSpan ℝ {φ a₁, φ a₂, φ b₁} ∪ range f, ?_, ?_⟩
      · rw [inter_univ, dimH_union, dimH_union, dimH_union]
        refine max_lt (max_lt (max_lt ?_ ?_) ?_) (dimH_range_lt_three hf)
        · refine dimH_lt_three_of_finrank_direction_le_two _ ?_
          rw [direction_affineSpan]
          exact (finrank_vectorSpan_pair_le_one _ _).trans (by norm_num)
        · refine dimH_lt_three_of_finrank_direction_le_two _ ?_
          rw [direction_affineSpan]
          exact (finrank_vectorSpan_pair_le_one _ _).trans (by norm_num)
        · refine dimH_lt_three_of_finrank_direction_le_two _ ?_
          rw [direction_affineSpan]
          exact finrank_vectorSpan_triple_le_two _ _ _
      · intro x _ hx _ w w' hw hw1 hw' hw'1 heq
        exact hfx x (fun h => hx (Or.inl (Or.inl (Or.inl h))))
          (fun h => hx (Or.inl (Or.inl (Or.inr h)))) (fun h => hx (Or.inl (Or.inr h)))
          (fun h => hx (Or.inr h)) w w' hw hw1 hw' hw'1 heq
    · refine ⟨∅, by simp, fun x _ _ hk => ?_⟩
      rcases hk with h | ⟨_, _, _, hdisj⟩ | ⟨_, _, _, _, hdisj⟩
      · exact absurd h hTT
      · exact absurd hvβ (Finset.disjoint_left.mp hdisj hvα)
      · exact absurd hvβ (Finset.disjoint_left.mp hdisj hvα)
  · have hβT := hsubT β hβ hvβ
    by_cases hk : (α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1) ∨
        (α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2 ∧ Disjoint α β)
    · have hsubs : ((S j : Set (EuclideanSpace ℝ (Fin 3))) ∩
          affineSpan ℝ (φ '' ↑β)).Subsingleton := by
        rcases hk with ⟨_, h3β, _, hβB, _⟩ | ⟨_, _, h2β, _⟩
        · exact hsub3 β hβT h3β hβB j
        · exact hsub2 β hβT h2β j
      obtain ⟨A, hA, hAx⟩ :=
        exists_affineSubspace_sum_smul_notMem_of_inter_subsingleton hvα hvβ φ (S j) hsubs
      have hα3 : α.card ≤ 3 := by
        rcases hk with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      exact ⟨A, by rw [inter_univ]; exact dimH_lt_three_of_finrank_direction_le_two A (by omega),
        fun x _ hx _ w w' hw hw1 _ hw'1 heq => hAx x hx w w' hw hw1 hw'1 heq⟩
    · refine ⟨∅, by simp, fun x _ _ hk' => ?_⟩
      rcases hk' with h | h | ⟨_, _, hαB, _, _⟩
      · exact absurd (Or.inl h) hk
      · exact absurd (Or.inr h) hk
      · exact absurd (hαB hvα) hvB
  · have hαT := hsubT α hα hvα
    by_cases hk : (α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1) ∨
        (α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2 ∧ Disjoint α β)
    · have hsubs : ((S j : Set (EuclideanSpace ℝ (Fin 3))) ∩
          affineSpan ℝ (φ '' ↑α)).Subsingleton := by
        rcases hk with ⟨h3α, _, hαB, _, _⟩ | ⟨h3α, hαB, _, _⟩
        · exact hsub3 α hαT h3α hαB j
        · exact hsub3 α hαT h3α hαB j
      obtain ⟨A, hA, hAx⟩ :=
        exists_affineSubspace_sum_smul_notMem_of_inter_subsingleton hvβ hvα φ (S j) hsubs
      have hβ3 : β.card ≤ 3 := by
        rcases hk with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ <;> omega
      refine ⟨A, by rw [inter_univ]; exact dimH_lt_three_of_finrank_direction_le_two A (by omega),
        fun x _ hx _ w w' _ hw1 hw' hw'1 heq => ?_⟩
      rw [heq]
      exact hAx x hx w' w hw' hw'1 hw1 heq.symm
    · refine ⟨∅, by simp, fun x _ _ hk' => ?_⟩
      rcases hk' with h | h | ⟨_, _, _, hβB, _⟩
      · exact absurd (Or.inl h) hk
      · exact absurd (Or.inr h) hk
      · exact absurd (hβB hvβ) hvB
  · refine ⟨∅, by simp, fun x _ _ hk w w' hw hw1 hw' hw'1 heq => ?_⟩
    rw [hsumeq α hvα w x] at heq ⊢
    rw [hsumeq β hvβ w' x] at heq
    exact hskel α (hsubT α hα hvα) β (hsubT β hβ hvβ) hk j w w' hw hw1 hw' hw'1 heq

theorem exists_dimH_lt_fold_update {ιP : Type*} [Finite ιP] {Bv T : Finset ι} {v : ι}
    (φ : ι → EuclideanSpace ℝ (Fin 3)) (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (P : ιP → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hind : ∀ s ⊆ T, s.card ≤ 3 → AffineIndependent ℝ (fun u : s => φ u))
    (hplane : ∀ u ∈ T, ∀ j, (u ∈ Bv → ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j) → φ u ∉ P j)
    (hfold : ∀ α ⊆ T, ∀ β ⊆ T, α.card = 3 → ¬α ⊆ Bv → β.card = 2 → ¬β ⊆ Bv →
      Disjoint α β → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
        ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
          ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
            ∑ u ∈ α, w u • φ u ∉ P j) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)), dimH B < 3 ∧ ∀ x, x ∉ B →
      ∀ α ⊆ insert v T, ∀ β ⊆ insert v T, α.card = 3 → ¬α ⊆ Bv → β.card = 2 → ¬β ⊆ Bv →
        Disjoint α β → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
          ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
            ∑ u ∈ β, w' u = 1 →
            ∑ u ∈ α, w u • Function.update φ v x u =
              ∑ u ∈ β, w' u • Function.update φ v x u →
              ∑ u ∈ α, w u • Function.update φ v x u ∉ P j := by
  have hsubT : ∀ γ ⊆ insert v T, v ∉ γ → γ ⊆ T := fun γ hγ hv u hu =>
    (Finset.mem_insert.mp (hγ hu)).resolve_left fun h => hv (h ▸ hu)
  have hsumeq : ∀ (γ : Finset ι), v ∉ γ → ∀ (w : ι → ℝ) (x : EuclideanSpace ℝ (Fin 3)),
      ∑ u ∈ γ, w u • Function.update φ v x u = ∑ u ∈ γ, w u • φ u := fun γ hv w x =>
    Finset.sum_congr rfl fun u hu => by rw [Function.update_of_ne (fun h : u = v => hv (h ▸ hu))]
  have hK : {k : Finset ι × Finset ι × ιP | k.1 ⊆ insert v T ∧ k.2.1 ⊆ insert v T}.Finite :=
    ((insert v T).powerset.finite_toSet.prod
      ((insert v T).powerset.finite_toSet.prod finite_univ)).subset
      fun k hk => ⟨Finset.mem_powerset.mpr hk.1, Finset.mem_powerset.mpr hk.2, mem_univ _⟩
  refine (exists_dimH_inter_lt_forall_of_finite hK univ (c := 3) (by norm_num)
    (fun k x => k.1.card = 3 → ¬k.1 ⊆ Bv → k.2.1.card = 2 → ¬k.2.1 ⊆ Bv →
      Disjoint k.1 k.2.1 → ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P k.2.2 →
        ∀ w w' : ι → ℝ, (∀ u ∈ k.1, 0 < w u) → ∑ u ∈ k.1, w u = 1 →
          (∀ u ∈ k.2.1, 0 < w' u) → ∑ u ∈ k.2.1, w' u = 1 →
          ∑ u ∈ k.1, w u • Function.update φ v x u =
            ∑ u ∈ k.2.1, w' u • Function.update φ v x u →
            ∑ u ∈ k.1, w u • Function.update φ v x u ∉ P k.2.2) ?_).elim fun B hBB =>
    ⟨B, by simpa using hBB.1, fun x hx α hα β hβ h3 hαB h2 hβB hd j =>
      hBB.2 x (mem_univ x) hx (α, β, j) ⟨hα, hβ⟩ h3 hαB h2 hβB hd⟩
  rintro ⟨α, β, j⟩ ⟨hα, hβ⟩
  change α ⊆ insert v T at hα
  change β ⊆ insert v T at hβ
  dsimp only
  by_cases hvα : v ∈ α <;> by_cases hvβ : v ∈ β
  · exact ⟨∅, by simp, fun x _ _ _ _ _ _ hd => absurd hvβ (Finset.disjoint_left.mp hd hvα)⟩
  · have hβT := hsubT β hβ hvβ
    by_cases hk : α.card = 3 ∧ β.card = 2 ∧ ¬β ⊆ Bv
    · obtain ⟨h3α, h2β, hβB⟩ := hk
      obtain ⟨b, hbβ, hbB⟩ := Finset.not_subset.mp hβB
      have hbP : φ b ∉ P j := hplane b (hβT hbβ) j fun h => absurd h hbB
      have hrank : Module.finrank ℝ (affineSpan ℝ (φ '' ↑β)).direction ≤ 1 := by
        have := finrank_direction_affineSpan_image_lt_card ⟨b, hbβ⟩ φ
        omega
      have hnle : ¬affineSpan ℝ (φ '' ↑β) ≤ P j := fun hle =>
        hbP (hle (subset_affineSpan ℝ _ (mem_image_of_mem φ hbβ)))
      have hsubs : ((P j : Set (EuclideanSpace ℝ (Fin 3))) ∩
          affineSpan ℝ (φ '' ↑β)).Subsingleton := by
        rw [inter_comm]
        exact inter_subsingleton_of_not_le hrank hnle
      obtain ⟨A, hA, hAx⟩ :=
        exists_affineSubspace_sum_smul_notMem_of_inter_subsingleton hvα hvβ φ (P j) hsubs
      exact ⟨A, by rw [inter_univ]; exact dimH_lt_three_of_finrank_direction_le_two A (by omega),
        fun x _ hx _ _ _ _ _ _ w w' hw hw1 _ hw'1 heq => hAx x hx w w' hw hw1 hw'1 heq⟩
    · exact ⟨∅, by simp, fun x _ _ h3 _ h2 hβB => absurd ⟨h3, h2, hβB⟩ hk⟩
  · have hαT := hsubT α hα hvα
    by_cases hk : α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2
    · obtain ⟨h3α, hαB, h2β⟩ := hk
      obtain ⟨b, hβe⟩ := Finset.card_eq_one.mp
        (by rw [Finset.card_erase_of_mem hvβ, h2β] : (β.erase v).card = 1)
      obtain ⟨a, haα, haB⟩ := Finset.not_subset.mp hαB
      have haP : φ a ∉ P j := hplane a (hαT haα) j fun h => absurd h haB
      have hαind := hind α hαT h3α.le
      have hαrank := finrank_direction_affineSpan_image_add_one_of_affineIndependent hαind
        ⟨a, haα⟩
      have hnle : ¬affineSpan ℝ (φ '' ↑α) ≤ P j := fun hle =>
        haP (hle (subset_affineSpan ℝ _ (mem_image_of_mem φ haα)))
      have hPA : Module.finrank ℝ (P j ⊓ affineSpan ℝ (φ '' ↑α)).direction ≤ 1 := by
        have := finrank_direction_inf_lt_of_not_le (by omega) hnle
        omega
      obtain ⟨A, hA, hAx⟩ :=
        exists_affineSubspace_sum_smul_notMem_of_erase_eq_singleton hvβ hβe hvα φ (P j) hPA
      exact ⟨A, by rw [inter_univ]; exact dimH_lt_three_of_finrank_direction_le_two A hA,
        fun x _ hx _ _ _ _ _ _ w w' _ hw1 hw' hw'1 heq => hAx x hx w w' hw1 hw' hw'1 heq⟩
    · exact ⟨∅, by simp, fun x _ _ h3 hαB h2 => absurd ⟨h3, hαB, h2⟩ hk⟩
  · refine ⟨∅, by simp, fun x _ _ h3 hαB h2 hβB hd hker w w' hw hw1 hw' hw'1 heq => ?_⟩
    rw [hsumeq α hvα w x] at heq ⊢
    rw [hsumeq β hvβ w' x] at heq
    exact hfold α (hsubT α hα hvα) β (hsubT β hβ hvβ) h3 hαB h2 hβB hd j hker w w' hw hw1 hw'
      hw'1 heq

theorem exists_dimH_lt_cross_update {ιP : Type*} [Finite ιP] {Bv T : Finset ι} {v : ι}
    (φ : ι → EuclideanSpace ℝ (Fin 3)) (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (P : ιP → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hind : ∀ s ⊆ T, s.card ≤ 3 → AffineIndependent ℝ (fun u : s => φ u))
    (hplane : ∀ u ∈ T, ∀ j, (u ∈ Bv → ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j) → φ u ∉ P j)
    (hcross : ∀ α ⊆ T, ∀ β ⊆ T, α.card = 3 → β.card = 3 → ¬α ⊆ Bv → ¬β ⊆ Bv →
      Disjoint α β → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
        ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
          ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
            ∑ u ∈ α, w u • φ u ∈ P j →
              ¬affineSpan ℝ (φ '' ↑α) ⊓ affineSpan ℝ (φ '' ↑β) ≤ P j) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)), dimH B < 3 ∧ ∀ x, x ∉ B →
      ∀ α ⊆ insert v T, ∀ β ⊆ insert v T, α.card = 3 → β.card = 3 → ¬α ⊆ Bv → ¬β ⊆ Bv →
        Disjoint α β → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
          ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
            ∑ u ∈ β, w' u = 1 →
            ∑ u ∈ α, w u • Function.update φ v x u =
              ∑ u ∈ β, w' u • Function.update φ v x u →
              ∑ u ∈ α, w u • Function.update φ v x u ∈ P j →
                ¬affineSpan ℝ (Function.update φ v x '' ↑α) ⊓
                  affineSpan ℝ (Function.update φ v x '' ↑β) ≤ P j := by
  have hsubT : ∀ γ ⊆ insert v T, v ∉ γ → γ ⊆ T := fun γ hγ hv u hu =>
    (Finset.mem_insert.mp (hγ hu)).resolve_left fun h => hv (h ▸ hu)
  have hsumeq : ∀ (γ : Finset ι), v ∉ γ → ∀ (w : ι → ℝ) (x : EuclideanSpace ℝ (Fin 3)),
      ∑ u ∈ γ, w u • Function.update φ v x u = ∑ u ∈ γ, w u • φ u := fun γ hv w x =>
    Finset.sum_congr rfl fun u hu => by rw [Function.update_of_ne (fun h : u = v => hv (h ▸ hu))]
  have himgeq : ∀ (γ : Finset ι), v ∉ γ → ∀ x : EuclideanSpace ℝ (Fin 3),
      Function.update φ v x '' ↑γ = φ '' ↑γ := fun γ hv x =>
    image_congr fun u hu => Function.update_of_ne (fun h : u = v => hv (h ▸ hu)) x φ
  have hbad : ∀ γ δ : Finset ι, v ∈ γ → v ∉ δ → γ ⊆ insert v T → δ ⊆ T → γ.card = 3 →
      δ.card = 3 → ¬δ ⊆ Bv → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
      ∃ B : Set (EuclideanSpace ℝ (Fin 3)), dimH B < 3 ∧ ∀ x, x ∉ B →
        ∀ w w' : ι → ℝ, ∑ u ∈ γ, w u = 1 → ∑ u ∈ δ, w' u = 1 →
          ∑ u ∈ γ, w u • Function.update φ v x u =
            ∑ u ∈ δ, w' u • Function.update φ v x u →
            ¬affineSpan ℝ (Function.update φ v x '' ↑γ) ⊓
              affineSpan ℝ (Function.update φ v x '' ↑δ) ≤ P j := by
    intro γ δ hvγ hvδ hγ hδ h3γ h3δ hδB j hker
    obtain ⟨a₁, a₂, ha₁₂, hγe⟩ := Finset.card_eq_two.mp
      (by rw [Finset.card_erase_of_mem hvγ, h3γ] : (γ.erase v).card = 2)
    have hT : ∀ {u : ι}, u ∈ γ.erase v → u ∈ T := fun hu =>
      (Finset.mem_insert.mp (hγ (Finset.mem_of_mem_erase hu))).resolve_left
        (Finset.ne_of_mem_erase hu)
    have ha₁ : a₁ ∈ γ.erase v := by
      rw [hγe]
      exact Finset.mem_insert_self _ _
    have ha₂ : a₂ ∈ γ.erase v := by
      rw [hγe]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hA2 := hind {a₁, a₂} (by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hT ha₁
      · exact hT ha₂) (Finset.card_le_two.trans (by norm_num))
    have hne : φ a₁ ≠ φ a₂ := ne_of_affineIndependent_of_mem hA2 (by simp) (by simp) ha₁₂
    have ha₁P : φ a₁ ∉ P j := hplane a₁ (hT ha₁) j fun _ => hker
    have hδind := hind δ hδ h3δ.le
    obtain ⟨b, hbδ, hbB⟩ := Finset.not_subset.mp hδB
    have hδrank := finrank_direction_affineSpan_image_add_one_of_affineIndependent hδind
      ⟨b, hbδ⟩
    have hbP : φ b ∉ P j := hplane b (hδ hbδ) j fun h => absurd h hbB
    have hnle : ¬affineSpan ℝ (φ '' ↑δ) ≤ P j := fun hle =>
      hbP (hle (subset_affineSpan ℝ _ (mem_image_of_mem φ hbδ)))
    have hδP : Module.finrank ℝ (affineSpan ℝ (φ '' ↑δ) ⊓ P j).direction ≤ 1 := by
      have := finrank_direction_inf_lt_of_not_le (by omega) hnle
      rw [inf_comm]
      omega
    refine ⟨(line[ℝ, φ a₁, φ a₂] : Set (EuclideanSpace ℝ (Fin 3))) ∪
      affineSpan ℝ (insert (φ a₁) ((affineSpan ℝ (φ '' ↑δ) ⊓ P j :
        AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) : Set (EuclideanSpace ℝ (Fin 3)))),
      ?_, ?_⟩
    · rw [dimH_union]
      refine max_lt ?_ ?_
      · refine dimH_lt_three_of_finrank_direction_le_two _ ?_
        rw [direction_affineSpan]
        exact (finrank_vectorSpan_pair_le_one _ _).trans (by norm_num)
      · refine dimH_lt_three_of_finrank_direction_le_two _ ?_
        rw [direction_affineSpan]
        have := finrank_vectorSpan_insert_le (affineSpan ℝ (φ '' ↑δ) ⊓ P j) (φ a₁)
        omega
    · intro x hx w w' hw1 hw'1 heq
      exact not_inf_le_of_notMem_affineSpan_insert_inf hvγ hγe hvδ finrank_euclideanSpace_fin φ
        (P j) hne ha₁P (by omega) hδP (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h)) hw1
        hw'1 heq
  have hK : {k : Finset ι × Finset ι × ιP | k.1 ⊆ insert v T ∧ k.2.1 ⊆ insert v T}.Finite :=
    ((insert v T).powerset.finite_toSet.prod
      ((insert v T).powerset.finite_toSet.prod finite_univ)).subset
      fun k hk => ⟨Finset.mem_powerset.mpr hk.1, Finset.mem_powerset.mpr hk.2, mem_univ _⟩
  refine (exists_dimH_inter_lt_forall_of_finite hK univ (c := 3) (by norm_num)
    (fun k x => k.1.card = 3 → k.2.1.card = 3 → ¬k.1 ⊆ Bv → ¬k.2.1 ⊆ Bv →
      Disjoint k.1 k.2.1 → ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P k.2.2 →
        ∀ w w' : ι → ℝ, (∀ u ∈ k.1, 0 < w u) → ∑ u ∈ k.1, w u = 1 →
          (∀ u ∈ k.2.1, 0 < w' u) → ∑ u ∈ k.2.1, w' u = 1 →
          ∑ u ∈ k.1, w u • Function.update φ v x u =
            ∑ u ∈ k.2.1, w' u • Function.update φ v x u →
            ∑ u ∈ k.1, w u • Function.update φ v x u ∈ P k.2.2 →
              ¬affineSpan ℝ (Function.update φ v x '' ↑k.1) ⊓
                affineSpan ℝ (Function.update φ v x '' ↑k.2.1) ≤ P k.2.2) ?_).elim fun B hBB =>
    ⟨B, by simpa using hBB.1, fun x hx α hα β hβ h3α h3β hαB hβB hd j =>
      hBB.2 x (mem_univ x) hx (α, β, j) ⟨hα, hβ⟩ h3α h3β hαB hβB hd⟩
  rintro ⟨α, β, j⟩ ⟨hα, hβ⟩
  change α ⊆ insert v T at hα
  change β ⊆ insert v T at hβ
  dsimp only
  by_cases hvα : v ∈ α <;> by_cases hvβ : v ∈ β
  · exact ⟨∅, by simp, fun x _ _ _ _ _ _ hd => absurd hvβ (Finset.disjoint_left.mp hd hvα)⟩
  · by_cases hk : α.card = 3 ∧ β.card = 3 ∧ ¬β ⊆ Bv ∧ ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j
    · obtain ⟨h3α, h3β, hβB, hker⟩ := hk
      obtain ⟨A, hA, hAx⟩ := hbad α β hvα hvβ hα (hsubT β hβ hvβ) h3α h3β hβB j hker
      exact ⟨A, by rwa [inter_univ], fun x _ hx _ _ _ _ _ _ w w' _ hw1 _ hw'1 heq _ =>
        hAx x hx w w' hw1 hw'1 heq⟩
    · exact ⟨∅, by simp, fun x _ _ h3α h3β _ hβB _ hker => absurd ⟨h3α, h3β, hβB, hker⟩ hk⟩
  · by_cases hk : α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j
    · obtain ⟨h3α, h3β, hαB, hker⟩ := hk
      obtain ⟨A, hA, hAx⟩ := hbad β α hvβ hvα hβ (hsubT α hα hvα) h3β h3α hαB j hker
      refine ⟨A, by rwa [inter_univ], fun x _ hx _ _ _ _ _ _ w w' _ hw1 _ hw'1 heq _ => ?_⟩
      rw [inf_comm]
      exact hAx x hx w' w hw'1 hw1 heq.symm
    · exact ⟨∅, by simp, fun x _ _ h3α h3β hαB _ _ hker => absurd ⟨h3α, h3β, hαB, hker⟩ hk⟩
  · refine ⟨∅, by simp, fun x _ _ h3α h3β hαB hβB hd hker w w' hw hw1 hw' hw'1 heq hzP => ?_⟩
    rw [himgeq α hvα x, himgeq β hvβ x]
    rw [hsumeq α hvα w x] at heq hzP
    rw [hsumeq β hvβ w' x] at heq
    exact hcross α (hsubT α hα hvα) β (hsubT β hβ hvβ) h3α h3β hαB hβB hd j hker w w' hw hw1
      hw' hw'1 heq hzP

theorem exists_dimH_lt_skeleton_update_boundary {ιS : Type*} [Finite ιS] {Bv T : Finset ι}
    {v : ι} (hvB : v ∈ Bv) (hTB : T ⊆ Bv) (φ : ι → EuclideanSpace ℝ (Fin 3))
    (S : ιS → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hline : ∀ u ∈ T, ∀ j, φ u ∉ S j)
    (hskel : ∀ α ⊆ T, ∀ β ⊆ T,
      ((α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1) ∨
        (α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2 ∧ Disjoint α β) ∨
        (α.card = 2 ∧ β.card = 2 ∧ α ⊆ Bv ∧ β ⊆ Bv ∧ Disjoint α β)) →
      ∀ j (w w' : ι → ℝ), (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
        ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
          ∑ u ∈ α, w u • φ u ∉ S j) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)), dimH B < 2 ∧ ∀ x, x ∉ B →
      ∀ α ⊆ insert v T, ∀ β ⊆ insert v T,
        ((α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1) ∨
          (α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2 ∧ Disjoint α β) ∨
          (α.card = 2 ∧ β.card = 2 ∧ α ⊆ Bv ∧ β ⊆ Bv ∧ Disjoint α β)) →
        ∀ j (w w' : ι → ℝ), (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
          ∑ u ∈ β, w' u = 1 →
          ∑ u ∈ α, w u • Function.update φ v x u = ∑ u ∈ β, w' u • Function.update φ v x u →
            ∑ u ∈ α, w u • Function.update φ v x u ∉ S j := by
  have hsubT : ∀ γ ⊆ insert v T, v ∉ γ → γ ⊆ T := fun γ hγ hv u hu =>
    (Finset.mem_insert.mp (hγ hu)).resolve_left fun h => hv (h ▸ hu)
  have hins : ∀ γ ⊆ insert v T, γ ⊆ Bv := fun γ hγ u hu =>
    (Finset.mem_insert.mp (hγ hu)).elim (fun h => h ▸ hvB) fun h => hTB h
  have hsumeq : ∀ (γ : Finset ι), v ∉ γ → ∀ (w : ι → ℝ) (x : EuclideanSpace ℝ (Fin 3)),
      ∑ u ∈ γ, w u • Function.update φ v x u = ∑ u ∈ γ, w u • φ u := fun γ hv w x =>
    Finset.sum_congr rfl fun u hu => by rw [Function.update_of_ne (fun h : u = v => hv (h ▸ hu))]
  have hsub2 : ∀ γ ⊆ T, γ.card = 2 → ∀ j,
      ((S j : Set (EuclideanSpace ℝ (Fin 3))) ∩ affineSpan ℝ (φ '' ↑γ)).Subsingleton := by
    intro γ hγ h2 j
    obtain ⟨b, hb⟩ : γ.Nonempty := by
      rw [← Finset.card_pos, h2]
      norm_num
    have hrank : Module.finrank ℝ (affineSpan ℝ (φ '' ↑γ)).direction ≤ 1 := by
      have := finrank_direction_affineSpan_image_lt_card ⟨b, hb⟩ φ
      omega
    have hnle : ¬affineSpan ℝ (φ '' ↑γ) ≤ S j := fun hle =>
      hline b (hγ hb) j (hle (subset_affineSpan ℝ _ (mem_image_of_mem φ hb)))
    rw [inter_comm]
    exact inter_subsingleton_of_not_le hrank hnle
  have hK : {k : Finset ι × Finset ι × ιS | k.1 ⊆ insert v T ∧ k.2.1 ⊆ insert v T}.Finite :=
    ((insert v T).powerset.finite_toSet.prod
      ((insert v T).powerset.finite_toSet.prod finite_univ)).subset
      fun k hk => ⟨Finset.mem_powerset.mpr hk.1, Finset.mem_powerset.mpr hk.2, mem_univ _⟩
  refine (exists_dimH_inter_lt_forall_of_finite hK univ (c := 2) (by norm_num)
    (fun k x => ((k.1.card = 3 ∧ k.2.1.card = 3 ∧ ¬k.1 ⊆ Bv ∧ ¬k.2.1 ⊆ Bv ∧
        (k.1 ∩ k.2.1).card ≤ 1) ∨
        (k.1.card = 3 ∧ ¬k.1 ⊆ Bv ∧ k.2.1.card = 2 ∧ Disjoint k.1 k.2.1) ∨
        (k.1.card = 2 ∧ k.2.1.card = 2 ∧ k.1 ⊆ Bv ∧ k.2.1 ⊆ Bv ∧ Disjoint k.1 k.2.1)) →
      ∀ (w w' : ι → ℝ), (∀ u ∈ k.1, 0 < w u) → ∑ u ∈ k.1, w u = 1 →
        (∀ u ∈ k.2.1, 0 < w' u) → ∑ u ∈ k.2.1, w' u = 1 →
        ∑ u ∈ k.1, w u • Function.update φ v x u =
          ∑ u ∈ k.2.1, w' u • Function.update φ v x u →
          ∑ u ∈ k.1, w u • Function.update φ v x u ∉ S k.2.2) ?_).elim fun B hBB =>
    ⟨B, by simpa using hBB.1, fun x hx α hα β hβ hk j w w' =>
      hBB.2 x (mem_univ x) hx (α, β, j) ⟨hα, hβ⟩ hk w w'⟩
  rintro ⟨α, β, j⟩ ⟨hα, hβ⟩
  change α ⊆ insert v T at hα
  change β ⊆ insert v T at hβ
  dsimp only
  have hαB := hins α hα
  have hβB := hins β hβ
  by_cases hk : α.card = 2 ∧ β.card = 2 ∧ Disjoint α β
  · obtain ⟨h2α, h2β, hd⟩ := hk
    by_cases hvα : v ∈ α
    · have hvβ : v ∉ β := fun h => Finset.disjoint_left.mp hd hvα h
      obtain ⟨A, hA, hAx⟩ := exists_affineSubspace_sum_smul_notMem_of_inter_subsingleton hvα hvβ
        φ (S j) (hsub2 β (hsubT β hβ hvβ) h2β j)
      exact ⟨A, by rw [inter_univ]; exact dimH_lt_two_of_finrank_direction_le_one A (by omega),
        fun x _ hx _ w w' hw hw1 _ hw'1 heq => hAx x hx w w' hw hw1 hw'1 heq⟩
    · by_cases hvβ : v ∈ β
      · obtain ⟨A, hA, hAx⟩ := exists_affineSubspace_sum_smul_notMem_of_inter_subsingleton hvβ
          hvα φ (S j) (hsub2 α (hsubT α hα hvα) h2α j)
        refine ⟨A, by rw [inter_univ]; exact dimH_lt_two_of_finrank_direction_le_one A (by omega),
          fun x _ hx _ w w' _ hw1 hw' hw'1 heq => ?_⟩
        rw [heq]
        exact hAx x hx w' w hw' hw'1 hw1 heq.symm
      · refine ⟨∅, by simp, fun x _ _ hk w w' hw hw1 hw' hw'1 heq => ?_⟩
        rw [hsumeq α hvα w x] at heq ⊢
        rw [hsumeq β hvβ w' x] at heq
        exact hskel α (hsubT α hα hvα) β (hsubT β hβ hvβ) hk j w w' hw hw1 hw' hw'1 heq
  · refine ⟨∅, by simp, fun x _ _ hk' => ?_⟩
    rcases hk' with ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨h2α, h2β, _, _, hd⟩
    · exact absurd hαB h
    · exact absurd hαB h
    · exact absurd ⟨h2α, h2β, hd⟩ hk

end Clauses

end DifferentialGeometry.Topology.PiecewiseLinear
