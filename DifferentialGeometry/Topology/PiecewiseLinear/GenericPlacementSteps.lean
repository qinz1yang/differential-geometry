/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArrangementGeneralPositionDimension
import DifferentialGeometry.Topology.PiecewiseLinear.RuledSurfaceOfPlanePencils

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

theorem sum_smul_mem_affineSpan_image {s : Finset ι} {w : ι → ℝ} (hw : ∑ u ∈ s, w u = 1)
    (ψ : ι → E) : ∑ u ∈ s, w u • ψ u ∈ affineSpan ℝ (ψ '' ↑s) := by
  have h := affineCombination_mem_affineSpan_image hw (s' := (s : Set ι))
    (fun i hi hni => (hni hi).elim) ψ
  rwa [Finset.affineCombination_eq_linear_combination s ψ w hw] at h

theorem mem_affineSpan_insert_image_erase_of_sum_smul [DecidableEq ι] {α : Finset ι} {v : ι}
    (hv : v ∈ α) {w : ι → ℝ} (hw : ∑ u ∈ α, w u = 1) (hwv : w v ≠ 0) (ψ : ι → E) :
    ψ v ∈ affineSpan ℝ (insert (∑ u ∈ α, w u • ψ u) (ψ '' ↑(α.erase v))) := by
  set z := ∑ u ∈ α, w u • ψ u with hz
  have hsplit : z = w v • ψ v + ∑ u ∈ α.erase v, w u • ψ u :=
    (Finset.add_sum_erase α (fun u => w u • ψ u) hv).symm
  have hsum : ∑ u ∈ α.erase v, w u = 1 - w v := by
    rw [← hw, ← Finset.add_sum_erase α w hv]
    ring
  have key : ∑ u ∈ α.erase v, w u • (z - ψ u) = w v • (ψ v - z) := by
    rw [Finset.sum_congr rfl (fun u _ => smul_sub (w u) z (ψ u)), Finset.sum_sub_distrib,
      ← Finset.sum_smul, hsum, smul_sub]
    linear_combination (norm := module) hsplit
  have hdir : ψ v -ᵥ z ∈ (affineSpan ℝ (insert z (ψ '' ↑(α.erase v)))).direction := by
    rw [direction_affineSpan, vsub_eq_sub, ← inv_smul_smul₀ hwv (ψ v - z), ← key]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _ ?_)
    exact vsub_mem_vectorSpan ℝ (mem_insert z _) (mem_insert_of_mem z (mem_image_of_mem ψ hu))
  have hz' : z ∈ affineSpan ℝ (insert z (ψ '' ↑(α.erase v))) :=
    subset_affineSpan ℝ _ (mem_insert z _)
  have h := AffineSubspace.vadd_mem_of_mem_direction hdir hz'
  rwa [vsub_vadd] at h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem image_update_eq_insert_image_erase [DecidableEq ι] {α : Finset ι} {v : ι} (hv : v ∈ α)
    (φ : ι → E) (y : E) : Function.update φ v y '' ↑α = insert y (φ '' ↑(α.erase v)) := by
  conv_lhs => rw [← Finset.insert_erase hv]
  rw [Finset.coe_insert, image_insert_eq, Function.update_self]
  congr 1
  exact image_congr fun u hu => Function.update_of_ne (Finset.ne_of_mem_erase hu) y φ

theorem inter_subsingleton_of_not_le [FiniteDimensional ℝ E] {S A : AffineSubspace ℝ E}
    (hS : Module.finrank ℝ S.direction ≤ 1) (h : ¬S ≤ A) : ((S : Set E) ∩ A).Subsingleton := by
  rintro z₁ ⟨hz₁S, hz₁A⟩ z₂ ⟨hz₂S, hz₂A⟩
  by_contra hne
  apply h
  have hle : line[ℝ, z₁, z₂] ≤ S :=
    affineSpan_le.mpr (insert_subset hz₁S (singleton_subset_iff.mpr hz₂S))
  have heq : line[ℝ, z₁, z₂] = S := by
    refine AffineSubspace.eq_of_direction_eq_of_nonempty_of_le ?_
      ⟨z₁, left_mem_affineSpan_pair ℝ _ _⟩ hle
    apply Submodule.eq_of_le_of_finrank_le (AffineSubspace.direction_le hle)
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hne)]
    exact hS
  rw [← heq]
  exact affineSpan_le.mpr (insert_subset hz₁A (singleton_subset_iff.mpr hz₂A))

theorem finrank_direction_inf_lt_of_not_le [FiniteDimensional ℝ E] {A P : AffineSubspace ℝ E}
    (hA : 0 < Module.finrank ℝ A.direction) (h : ¬A ≤ P) :
    Module.finrank ℝ (P ⊓ A).direction < Module.finrank ℝ A.direction := by
  rcases (((P ⊓ A : AffineSubspace ℝ E)) : Set E).eq_empty_or_nonempty with he | ⟨p, hp⟩
  · rw [(AffineSubspace.coe_eq_bot_iff _).mp he, AffineSubspace.direction_bot, finrank_bot]
    exact hA
  · rw [AffineSubspace.direction_inf_of_mem_inf hp]
    refine lt_of_le_of_ne (Submodule.finrank_mono inf_le_right) fun heq => h ?_
    have hdir : P.direction ⊓ A.direction = A.direction :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right heq
    have hle : A.direction ≤ P.direction := by
      rw [← hdir]
      exact inf_le_left
    obtain ⟨hpP, hpA⟩ := (AffineSubspace.mem_inf_iff p P A).mp hp
    intro q hq
    have hqp : q -ᵥ p ∈ P.direction := hle (AffineSubspace.vsub_mem_direction hq hpA)
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hqp hpP
    rwa [vsub_vadd] at hmem

theorem finrank_direction_affineSpan_image_lt_card {s : Finset ι} (hs : s.Nonempty) (ψ : ι → E) :
    Module.finrank ℝ (affineSpan ℝ (ψ '' ↑s)).direction < s.card := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, s.card = n + 1 := ⟨s.card - 1, by have := hs.card_pos; omega⟩
  rw [direction_affineSpan, ← Finset.coe_image]
  have h := finrank_vectorSpan_image_finset_le (k := ℝ) ψ s hn
  omega

theorem eq_of_le_of_finrank_direction_le [FiniteDimensional ℝ E] {A B : AffineSubspace ℝ E}
    (hle : A ≤ B) (hA : (A : Set E).Nonempty)
    (hrank : Module.finrank ℝ B.direction ≤ Module.finrank ℝ A.direction) : A = B :=
  AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_le (AffineSubspace.direction_le hle) hrank) hA hle

end Affine

section Steps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
theorem exists_affineSubspace_sum_smul_notMem_of_inter_subsingleton {α β : Finset ι} {v : ι}
    (hvα : v ∈ α) (hvβ : v ∉ β) (φ : ι → E) (S : AffineSubspace ℝ E)
    (hS : ((S : Set E) ∩ affineSpan ℝ (φ '' ↑β)).Subsingleton) :
    ∃ B : AffineSubspace ℝ E, Module.finrank ℝ B.direction < α.card ∧
      ∀ x, x ∉ B → ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 →
        ∑ u ∈ β, w' u = 1 →
        ∑ u ∈ α, w u • Function.update φ v x u = ∑ u ∈ β, w' u • Function.update φ v x u →
          ∑ u ∈ α, w u • Function.update φ v x u ∉ S := by
  have hβeq : ∀ (x : E) (w' : ι → ℝ),
      ∑ u ∈ β, w' u • Function.update φ v x u = ∑ u ∈ β, w' u • φ u := fun x w' =>
    Finset.sum_congr rfl fun u hu => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hu hvβ)]
  by_cases h : ∃ z₀, z₀ ∈ (S : Set E) ∩ affineSpan ℝ (φ '' ↑β)
  · obtain ⟨z₀, hz₀⟩ := h
    refine ⟨affineSpan ℝ (Function.update φ v z₀ '' ↑α),
      finrank_direction_affineSpan_image_lt_card ⟨v, hvα⟩ _, ?_⟩
    intro x hx w w' hw hw1 hw'1 heq hzS
    apply hx
    have hz : ∑ u ∈ α, w u • Function.update φ v x u = z₀ := by
      refine hS ⟨hzS, ?_⟩ hz₀
      rw [heq, hβeq]
      exact sum_smul_mem_affineSpan_image hw'1 φ
    have hmem := mem_affineSpan_insert_image_erase_of_sum_smul hvα hw1 (hw v hvα).ne'
      (Function.update φ v x)
    rw [hz, Function.update_self] at hmem
    rw [image_update_eq_insert_image_erase hvα]
    have himg : Function.update φ v x '' ↑(α.erase v) = φ '' ↑(α.erase v) :=
      image_congr fun u hu => Function.update_of_ne (Finset.ne_of_mem_erase hu) x φ
    rwa [himg] at hmem
  · refine ⟨⊥, ?_, fun x _ w w' _ _ hw'1 heq hzS => h ⟨_, hzS, ?_⟩⟩
    · rw [AffineSubspace.direction_bot, finrank_bot]
      exact Finset.card_pos.mpr ⟨v, hvα⟩
    · rw [heq, hβeq]
      exact sum_smul_mem_affineSpan_image hw'1 φ

omit [FiniteDimensional ℝ E] in
theorem affineIndependent_update_of_notMem_affineSpan_erase {s : Finset ι} {v : ι} (hv : v ∈ s)
    {φ : ι → E} (hs : AffineIndependent ℝ (fun u : (s.erase v) => φ u)) {x : E}
    (hx : x ∉ affineSpan ℝ (φ '' ↑(s.erase v))) :
    AffineIndependent ℝ (fun u : s => Function.update φ v x u) := by
  classical
  have hold := (affineIndependent_image_iff (s.erase v) φ).mp hs
  have himg : s.image (Function.update φ v x) = insert x ((s.erase v).image φ) := by
    conv_lhs => rw [← Finset.insert_erase hv]
    rw [Finset.image_insert, Function.update_self]
    congr 1
    exact Finset.image_congr fun u hu => Function.update_of_ne (Finset.ne_of_mem_erase hu) x φ
  have hneq : ∀ u ∈ s.erase v, x ≠ φ u := fun u hu h =>
    hx (h ▸ subset_affineSpan ℝ _ (mem_image_of_mem φ hu))
  apply (affineIndependent_image_iff s (Function.update φ v x)).mpr
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    by_cases hav : a = v
    · by_cases hbv : b = v
      · exact hav.trans hbv.symm
      · rw [hav, Function.update_self, Function.update_of_ne hbv] at hab
        exact (hneq b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab).elim
    · by_cases hbv : b = v
      · rw [hbv, Function.update_self, Function.update_of_ne hav] at hab
        exact (hneq a (Finset.mem_erase.mpr ⟨hav, ha⟩) hab.symm).elim
      · rw [Function.update_of_ne hav, Function.update_of_ne hbv] at hab
        exact hold.1 (Finset.mem_erase.mpr ⟨hav, ha⟩) (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab
  · rw [himg]
    refine affineIndependent_insert_of_notMem_affineSpan hold.2 ?_
    rwa [Finset.coe_image]

theorem exists_affineSubspace_not_le_affineSpan_update {β : Finset ι} {v b : ι} (hvβ : v ∈ β)
    (hbβ : b ∈ β) (hbv : b ≠ v) (hβ : β.card ≤ 3) (φ : ι → E) (S : AffineSubspace ℝ E)
    (hS : Module.finrank ℝ S.direction = 1) (hb : φ b ∉ S) :
    ∃ B : AffineSubspace ℝ E, Module.finrank ℝ B.direction ≤ 2 ∧
      ∀ x, x ∉ B → ¬S ≤ affineSpan ℝ (Function.update φ v x '' ↑β) := by
  obtain ⟨s₀, hs₀⟩ : (S : Set E).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, AffineSubspace.coe_eq_bot_iff] at hne
    rw [hne, AffineSubspace.direction_bot, finrank_bot] at hS
    exact zero_ne_one hS
  refine ⟨affineSpan ℝ (insert (φ b) (S : Set E)), ?_, ?_⟩
  · rw [direction_affineSpan]
    have h := finrank_vectorSpan_insert_le S (φ b)
    omega
  · intro x hx hle
    apply hx
    have hbA : φ b ∈ affineSpan ℝ (Function.update φ v x '' ↑β) := by
      refine subset_affineSpan ℝ _ ⟨b, hbβ, ?_⟩
      exact Function.update_of_ne hbv x φ
    have hBle : affineSpan ℝ (insert (φ b) (S : Set E)) ≤
        affineSpan ℝ (Function.update φ v x '' ↑β) :=
      affineSpan_le.mpr (insert_subset hbA hle)
    have hBrank : 2 ≤ Module.finrank ℝ (affineSpan ℝ (insert (φ b) (S : Set E))).direction := by
      rw [AffineSubspace.direction_affineSpan_insert hs₀]
      have hlt : S.direction < Submodule.span ℝ {φ b -ᵥ s₀} ⊔ S.direction := by
        refine lt_of_le_of_ne le_sup_right fun heq => hb ?_
        have hmem : φ b -ᵥ s₀ ∈ S.direction := by
          rw [heq]
          exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
        have h := AffineSubspace.vadd_mem_of_mem_direction hmem hs₀
        rwa [vsub_vadd] at h
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hArank : Module.finrank ℝ (affineSpan ℝ (Function.update φ v x '' ↑β)).direction ≤ 2 := by
      have := finrank_direction_affineSpan_image_lt_card ⟨v, hvβ⟩ (Function.update φ v x)
      omega
    have heq := eq_of_le_of_finrank_direction_le hBle ⟨φ b, subset_affineSpan ℝ _ (mem_insert _ _)⟩
      (hArank.trans hBrank)
    rw [heq]
    exact subset_affineSpan ℝ _ ⟨v, hvβ, Function.update_self v x φ⟩

omit [FiniteDimensional ℝ E] in
theorem exists_affineSubspace_sum_smul_notMem_of_erase_eq_singleton {α β : Finset ι} {v b : ι}
    (hvβ : v ∈ β) (hβ : β.erase v = {b}) (hvα : v ∉ α) (φ : ι → E) (P : AffineSubspace ℝ E)
    (hPA : Module.finrank ℝ (P ⊓ affineSpan ℝ (φ '' ↑α)).direction ≤ 1) :
    ∃ B : AffineSubspace ℝ E, Module.finrank ℝ B.direction ≤ 2 ∧
      ∀ x, x ∉ B → ∀ w w' : ι → ℝ, ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
        ∑ u ∈ β, w' u = 1 →
        ∑ u ∈ α, w u • Function.update φ v x u = ∑ u ∈ β, w' u • Function.update φ v x u →
          ∑ u ∈ α, w u • Function.update φ v x u ∉ P := by
  have hbv : b ≠ v := by
    have hb : b ∈ β.erase v := by
      rw [hβ]
      exact Finset.mem_singleton_self b
    exact Finset.ne_of_mem_erase hb
  refine ⟨affineSpan ℝ (insert (φ b) ((P ⊓ affineSpan ℝ (φ '' ↑α) : AffineSubspace ℝ E) :
    Set E)), ?_, ?_⟩
  · rw [direction_affineSpan]
    have h := finrank_vectorSpan_insert_le (P ⊓ affineSpan ℝ (φ '' ↑α)) (φ b)
    omega
  · intro x hx w w' hw1 hw' hw'1 heq hzP
    apply hx
    have hαeq : ∑ u ∈ α, w u • Function.update φ v x u = ∑ u ∈ α, w u • φ u :=
      Finset.sum_congr rfl fun u hu => by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hu hvα)]
    have hzm : ∑ u ∈ α, w u • Function.update φ v x u ∈ P ⊓ affineSpan ℝ (φ '' ↑α) := by
      refine (AffineSubspace.mem_inf_iff _ _ _).mpr ⟨hzP, ?_⟩
      rw [hαeq]
      exact sum_smul_mem_affineSpan_image hw1 φ
    have hmem := mem_affineSpan_insert_image_erase_of_sum_smul hvβ hw'1 (hw' v hvβ).ne'
      (Function.update φ v x)
    rw [← heq, Function.update_self, hβ, Finset.coe_singleton, image_singleton,
      Function.update_of_ne hbv] at hmem
    refine (affineSpan_le.mpr ?_) hmem
    rintro q (rfl | rfl)
    · exact subset_affineSpan ℝ _ (mem_insert_of_mem _ hzm)
    · exact subset_affineSpan ℝ _ (mem_insert _ _)

theorem not_inf_le_of_notMem_affineSpan_insert_inf {α β : Finset ι} {v a₁ a₂ : ι} (hvα : v ∈ α)
    (hα : α.erase v = {a₁, a₂}) (hvβ : v ∉ β) (hE : Module.finrank ℝ E = 3) (φ : ι → E)
    (P : AffineSubspace ℝ E) (ha : φ a₁ ≠ φ a₂) (ha₁P : φ a₁ ∉ P)
    (hβ2 : 2 ≤ Module.finrank ℝ (affineSpan ℝ (φ '' ↑β)).direction)
    (hβP : Module.finrank ℝ (affineSpan ℝ (φ '' ↑β) ⊓ P).direction ≤ 1) {x : E}
    (hx₁ : x ∉ line[ℝ, φ a₁, φ a₂])
    (hx₂ : x ∉ affineSpan ℝ (insert (φ a₁) ((affineSpan ℝ (φ '' ↑β) ⊓ P :
      AffineSubspace ℝ E) : Set E)))
    {w w' : ι → ℝ} (hw1 : ∑ u ∈ α, w u = 1) (hw'1 : ∑ u ∈ β, w' u = 1)
    (heq : ∑ u ∈ α, w u • Function.update φ v x u = ∑ u ∈ β, w' u • Function.update φ v x u) :
    ¬affineSpan ℝ (Function.update φ v x '' ↑α) ⊓
      affineSpan ℝ (Function.update φ v x '' ↑β) ≤ P := by
  intro hle
  have ha₁ : a₁ ∈ α.erase v := by
    rw [hα]
    exact Finset.mem_insert_self _ _
  have ha₂ : a₂ ∈ α.erase v := by
    rw [hα]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hβimg : Function.update φ v x '' ↑β = φ '' ↑β :=
    image_congr fun u hu => Function.update_of_ne (ne_of_mem_of_not_mem hu hvβ) x φ
  have hαimg : Function.update φ v x '' ↑α = insert x {φ a₁, φ a₂} := by
    rw [image_update_eq_insert_image_erase hvα, hα, Finset.coe_insert, Finset.coe_singleton,
      image_insert_eq, image_singleton]
  rw [hβimg, hαimg] at hle
  set Aα := affineSpan ℝ (insert x ({φ a₁, φ a₂} : Set E)) with hAα
  set Aβ := affineSpan ℝ (φ '' ↑β) with hAβ
  have hAα2 : 2 ≤ Module.finrank ℝ Aα.direction := by
    rw [hAα, ← affineSpan_insert_affineSpan, AffineSubspace.direction_affineSpan_insert
      (left_mem_affineSpan_pair ℝ (φ a₁) (φ a₂))]
    have hline : Module.finrank ℝ (line[ℝ, φ a₁, φ a₂]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr ha)]
    have hlt : (line[ℝ, φ a₁, φ a₂]).direction <
        Submodule.span ℝ {x -ᵥ φ a₁} ⊔ (line[ℝ, φ a₁, φ a₂]).direction := by
      refine lt_of_le_of_ne le_sup_right fun h => hx₁ ?_
      have hmem : x -ᵥ φ a₁ ∈ (line[ℝ, φ a₁, φ a₂]).direction := by
        rw [h]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      have h' := AffineSubspace.vadd_mem_of_mem_direction hmem
        (left_mem_affineSpan_pair ℝ (φ a₁) (φ a₂))
      rwa [vsub_vadd] at h'
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hAαle : Module.finrank ℝ Aα.direction ≤ 2 := by
    rw [hAα, direction_affineSpan]
    have h1 := finrank_vectorSpan_insert_le_set ℝ ({φ a₁, φ a₂} : Set E) x
    rw [vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr ha)] at h1
    omega
  have hzα : ∑ u ∈ α, w u • Function.update φ v x u ∈ Aα := by
    rw [hAα, ← hαimg]
    exact sum_smul_mem_affineSpan_image hw1 _
  have hzβ : ∑ u ∈ α, w u • Function.update φ v x u ∈ Aβ := by
    rw [heq, hAβ, ← hβimg]
    exact sum_smul_mem_affineSpan_image hw'1 _
  have hzL : ∑ u ∈ α, w u • Function.update φ v x u ∈ Aα ⊓ Aβ :=
    (AffineSubspace.mem_inf_iff _ _ _).mpr ⟨hzα, hzβ⟩
  have hLrank : 1 ≤ Module.finrank ℝ (Aα ⊓ Aβ).direction := by
    rw [AffineSubspace.direction_inf_of_mem_inf hzL]
    have h := Submodule.finrank_sup_add_finrank_inf_eq Aα.direction Aβ.direction
    have hsup := Submodule.finrank_le (Aα.direction ⊔ Aβ.direction)
    rw [hE] at hsup
    omega
  have hLm : Aα ⊓ Aβ ≤ Aβ ⊓ P := le_inf inf_le_right hle
  have hLeq : Aα ⊓ Aβ = Aβ ⊓ P :=
    eq_of_le_of_finrank_direction_le hLm ⟨_, hzL⟩ (hβP.trans hLrank)
  have hmle : Aβ ⊓ P ≤ Aα := by
    rw [← hLeq]
    exact inf_le_left
  have hBle : affineSpan ℝ (insert (φ a₁) ((Aβ ⊓ P : AffineSubspace ℝ E) : Set E)) ≤ Aα := by
    refine affineSpan_le.mpr (insert_subset ?_ hmle)
    rw [hAα]
    exact subset_affineSpan ℝ _ (mem_insert_of_mem _ (mem_insert _ _))
  have hmem : ∑ u ∈ α, w u • Function.update φ v x u ∈ Aβ ⊓ P := by
    rw [← hLeq]
    exact hzL
  have hBrank : 2 ≤ Module.finrank ℝ
      (affineSpan ℝ (insert (φ a₁) ((Aβ ⊓ P : AffineSubspace ℝ E) : Set E))).direction := by
    rw [AffineSubspace.direction_affineSpan_insert hmem]
    have hlt : (Aβ ⊓ P).direction <
        Submodule.span ℝ {φ a₁ -ᵥ ∑ u ∈ α, w u • Function.update φ v x u} ⊔
          (Aβ ⊓ P).direction := by
      refine lt_of_le_of_ne le_sup_right fun h => ha₁P ?_
      have hd : φ a₁ -ᵥ ∑ u ∈ α, w u • Function.update φ v x u ∈ (Aβ ⊓ P).direction := by
        rw [h]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      have h' := AffineSubspace.vadd_mem_of_mem_direction hd hmem
      rw [vsub_vadd] at h'
      exact ((AffineSubspace.mem_inf_iff _ _ _).mp h').2
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : 1 ≤ Module.finrank ℝ (Aβ ⊓ P).direction := by
      rw [← hLeq]
      exact hLrank
    omega
  have hfin := eq_of_le_of_finrank_direction_le hBle
    ⟨φ a₁, subset_affineSpan ℝ _ (mem_insert _ _)⟩ (hAαle.trans hBrank)
  apply hx₂
  rw [hfin, hAα]
  exact subset_affineSpan ℝ _ (mem_insert _ _)

end Steps

section Shared

variable {ι : Type*} [DecidableEq ι]

theorem exists_contDiff_sum_smul_notMem_of_shared_vertex {α β : Finset ι} {v a₁ a₂ b₁ b₂ : ι}
    (hvα : v ∈ α) (hvβ : v ∈ β) (hα : α.erase v = {a₁, a₂}) (hβ : β.erase v = {b₁, b₂})
    (φ : ι → EuclideanSpace ℝ (Fin 3)) (ha : φ a₁ ≠ φ a₂) (hb : φ b₁ ≠ φ b₂)
    (hb₁ : φ b₁ ∉ line[ℝ, φ a₁, φ a₂]) (S : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hS : Module.finrank ℝ S.direction = 1) :
    ∃ f : ℝ × ℝ → EuclideanSpace ℝ (Fin 3), ContDiff ℝ 1 f ∧
      ∀ x, x ∉ line[ℝ, φ a₁, φ a₂] → x ∉ line[ℝ, φ b₁, φ b₂] →
        x ∉ affineSpan ℝ {φ a₁, φ a₂, φ b₁} → x ∉ range f →
        ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
          ∑ u ∈ β, w' u = 1 →
          ∑ u ∈ α, w u • Function.update φ v x u = ∑ u ∈ β, w' u • Function.update φ v x u →
            ∑ u ∈ α, w u • Function.update φ v x u ∉ S := by
  obtain ⟨p, hp⟩ : (S : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, AffineSubspace.coe_eq_bot_iff] at hne
    rw [hne, AffineSubspace.direction_bot, finrank_bot] at hS
    exact zero_ne_one hS
  obtain ⟨d₀, -, hd₀⟩ := finrank_eq_one_iff'.mp hS
  obtain ⟨f, hf, hfx⟩ := exists_contDiff_of_mem_affineSpan_triple_inter p
    (d₀ : EuclideanSpace ℝ (Fin 3)) (φ a₁) (φ a₂) (φ b₁) (φ b₂) ha hb hb₁
  refine ⟨f, hf, fun x h₁ h₂ h₃ h₄ w w' hw hw1 hw' hw'1 heq hzS => ?_⟩
  obtain ⟨t, ht⟩ := hd₀ ⟨_ -ᵥ p, AffineSubspace.vsub_mem_direction hzS hp⟩
  have hz : ∑ u ∈ α, w u • Function.update φ v x u = p + t • (d₀ : EuclideanSpace ℝ (Fin 3)) := by
    have h := congrArg Subtype.val ht
    simp only [Submodule.coe_smul] at h
    rw [h, vsub_eq_sub]
    abel
  have himg : ∀ {γ : Finset ι} {c₁ c₂ : ι}, γ.erase v = {c₁, c₂} →
      Function.update φ v x '' ↑(γ.erase v) = {φ c₁, φ c₂} := by
    intro γ c₁ c₂ hγ
    have hc₁ : c₁ ∈ γ.erase v := by
      rw [hγ]
      exact Finset.mem_insert_self _ _
    have hc₂ : c₂ ∈ γ.erase v := by
      rw [hγ]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [hγ, Finset.coe_insert, Finset.coe_singleton, image_insert_eq, image_singleton,
      Function.update_of_ne (Finset.ne_of_mem_erase hc₁),
      Function.update_of_ne (Finset.ne_of_mem_erase hc₂)]
  have hxa := mem_affineSpan_insert_image_erase_of_sum_smul hvα hw1 (hw v hvα).ne'
    (Function.update φ v x)
  have hxb := mem_affineSpan_insert_image_erase_of_sum_smul hvβ hw'1 (hw' v hvβ).ne'
    (Function.update φ v x)
  rw [Function.update_self, himg hα, hz] at hxa
  rw [Function.update_self, himg hβ, ← heq, hz] at hxb
  rcases hfx t x hxa hxb with h | h | h | h
  · exact h₁ h
  · exact h₂ h
  · exact h₃ h
  · exact h₄ h

end Shared

end DifferentialGeometry.Topology.PiecewiseLinear
