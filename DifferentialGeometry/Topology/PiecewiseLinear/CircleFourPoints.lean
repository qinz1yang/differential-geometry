/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Homogeneity
import DifferentialGeometry.Topology.PiecewiseLinear.LateralAnnulusLevels
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isPLHomeomorphOn_one_sub_Icc :
    IsPLHomeomorphOn (fun x : ℝ => 1 - x) (Icc 0 1) (Icc 0 1) := by
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    ((isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.const ℝ ℝ 1 - AffineMap.id ℝ ℝ) isHPolytope_Icc).congr fun x _ => rfl)
    ⟨?_, ?_, ?_⟩
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · intro x _ y _ h
    linarith [show 1 - x = 1 - y from h]
  · intro y hy
    exact ⟨1 - y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by ring⟩

theorem isPLHomeomorphOn_comp_mul_add_Icc {A : Set E} {α : ℝ → E}
    (hα : IsPLHomeomorphOn α (Icc 0 1) A) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    IsPLHomeomorphOn (fun x => α ((b - a) * x + a)) (Icc 0 1) (α '' Icc a b) := by
  have h := isPLHomeomorphOn_mul_add_Icc (sub_pos.mpr hab)
    (show (b - a) * 0 + a = a by ring) (show (b - a) * 1 + a = b by ring)
  exact h.trans (hα.restrict isHPolytope_Icc.isPolyhedron (Icc_subset_Icc ha hb))

theorem isPLHomeomorphOn_comp_one_sub {A : Set E} {α : ℝ → E}
    (hα : IsPLHomeomorphOn α (Icc 0 1) A) :
    IsPLHomeomorphOn (fun x => α (1 - x)) (Icc 0 1) A :=
  isPLHomeomorphOn_one_sub_Icc.trans hα

theorem exists_isPLHomeomorphOn_Icc_concat {A B : Set E} {α β : ℝ → E}
    (hα : IsPLHomeomorphOn α (Icc 0 1) A) (hβ : IsPLHomeomorphOn β (Icc 0 1) B)
    (hβ0 : β 0 = α 1) (hAB : A ∩ B = {α 1}) :
    ∃ l : ℝ → E, IsPLHomeomorphOn l (Icc 0 1) (A ∪ B) ∧ l 0 = α 0 ∧ l (1 / 2) = α 1 ∧
      l 1 = β 1 := by
  have h₁ := isPLHomeomorphOn_mul_add_Icc (two_pos : (0 : ℝ) < 2)
    (show (2 : ℝ) * 0 + 0 = 0 by ring) (show (2 : ℝ) * (1 / 2) + 0 = 1 by ring)
  have h₂ := isPLHomeomorphOn_mul_add_Icc (two_pos : (0 : ℝ) < 2)
    (show (2 : ℝ) * (1 / 2) + -1 = 0 by ring) (show (2 : ℝ) * 1 + -1 = 1 by ring)
  have hf₁ := h₁.trans hα
  have hf₂ := h₂.trans hβ
  have hinter : Icc (0 : ℝ) (1 / 2) ∩ Icc (1 / 2) 1 = {1 / 2} := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨-, h1⟩, h2, -⟩
      exact le_antisymm h1 h2
    · rintro rfl
      norm_num
  obtain ⟨l, hl, hl₁, hl₂⟩ := exists_isPLHomeomorphOn_union isHPolytope_Icc.isPolyhedron
    isHPolytope_Icc.isPolyhedron hf₁ hf₂ (by
      rw [hinter]
      rintro x rfl
      simp only [Function.comp_apply]
      rw [show (2 : ℝ) * (1 / 2) + 0 = 1 by ring, show (2 : ℝ) * (1 / 2) + -1 = 0 by ring, hβ0])
    (by
      rw [hinter, hAB]
      rintro y rfl
      exact ⟨1 / 2, rfl, by simp only [Function.comp_apply]; norm_num⟩)
  rw [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at hl
  refine ⟨l, hl, ?_, ?_, ?_⟩
  · rw [hl₁ ⟨le_rfl, by norm_num⟩]
    simp
  · rw [hl₁ ⟨by norm_num, le_rfl⟩]
    simp only [Function.comp_apply]
    norm_num
  · rw [hl₂ ⟨by norm_num, le_rfl⟩]
    simp only [Function.comp_apply]
    norm_num

theorem exists_isPLHomeomorphOn_arc_map_mid {A : Set E} {A' : Set F} {α : ℝ → E}
    {α' : ℝ → F} (hα : IsPLHomeomorphOn α (Icc 0 1) A) (hα' : IsPLHomeomorphOn α' (Icc 0 1) A')
    {s s' : ℝ} (hs : s ∈ Ioo 0 1) (hs' : s' ∈ Ioo 0 1) :
    ∃ f : E → F, IsPLHomeomorphOn f A A' ∧ f (α 0) = α' 0 ∧ f (α 1) = α' 1 ∧
      f (α s) = α' s' := by
  obtain ⟨φ, hφ, hφ0, hφ1, hφs⟩ := exists_isPLHomeomorphOn_Icc_fixing_endpoints hs hs'
  have hinv : ∀ x ∈ Icc (0 : ℝ) 1, Function.invFunOn α (Icc 0 1) (α x) = x :=
    fun x hx => hα.bijOn.invOn_invFunOn.1 hx
  refine ⟨α' ∘ φ ∘ Function.invFunOn α (Icc 0 1), hα.symm.trans (hφ.trans hα'), ?_, ?_, ?_⟩
  · simp only [Function.comp_apply]
    rw [hinv 0 ⟨le_rfl, zero_le_one⟩, hφ0]
  · simp only [Function.comp_apply]
    rw [hinv 1 ⟨zero_le_one, le_rfl⟩, hφ1]
  · simp only [Function.comp_apply]
    rw [hinv s ⟨hs.1.le, hs.2.le⟩, hφs]

theorem exists_isPLHomeomorphOn_of_arc_pairs {A B : Set E} {A' B' : Set F} {α β : ℝ → E}
    {α' β' : ℝ → F} (hα : IsPLHomeomorphOn α (Icc 0 1) A) (hβ : IsPLHomeomorphOn β (Icc 0 1) B)
    (hα' : IsPLHomeomorphOn α' (Icc 0 1) A') (hβ' : IsPLHomeomorphOn β' (Icc 0 1) B')
    (hβ0 : β 0 = α 0) (hβ1 : β 1 = α 1) (hβ'0 : β' 0 = α' 0) (hβ'1 : β' 1 = α' 1)
    (hAB : A ∩ B = {α 0, α 1}) (hAB' : A' ∩ B' = {α' 0, α' 1}) {s r s' r' : ℝ}
    (hs : s ∈ Ioo 0 1) (hr : r ∈ Ioo 0 1) (hs' : s' ∈ Ioo 0 1) (hr' : r' ∈ Ioo 0 1) :
    ∃ γ : E → F, IsPLHomeomorphOn γ (A ∪ B) (A' ∪ B') ∧ γ (α 0) = α' 0 ∧ γ (α s) = α' s' ∧
      γ (α 1) = α' 1 ∧ γ (β r) = β' r' := by
  obtain ⟨f, hf, hf0, hf1, hfs⟩ := exists_isPLHomeomorphOn_arc_map_mid hα hα' hs hs'
  obtain ⟨g, hg, hg0, hg1, hgr⟩ := exists_isPLHomeomorphOn_arc_map_mid hβ hβ' hr hr'
  have hI : IsPLBall 1 (Icc (0 : ℝ) 1) := isPLBall_Icc zero_lt_one
  obtain ⟨γ, hγ, hγf, hγg⟩ := exists_isPLHomeomorphOn_union
    (hI.of_isPLHomeomorphOn hα).isPolyhedron (hI.of_isPLHomeomorphOn hβ).isPolyhedron hf hg
    (by
      rw [hAB]
      rintro x (rfl | rfl)
      · rw [hf0, ← hβ0, hg0, hβ'0]
      · rw [hf1, ← hβ1, hg1, hβ'1])
    (by
      rw [hAB, hAB']
      rintro y (rfl | rfl)
      · exact ⟨α 0, Or.inl rfl, hf0⟩
      · exact ⟨α 1, Or.inr rfl, hf1⟩)
  have hmemA : ∀ x ∈ Icc (0 : ℝ) 1, α x ∈ A := fun x hx => hα.bijOn.mapsTo hx
  have hmemB : ∀ x ∈ Icc (0 : ℝ) 1, β x ∈ B := fun x hx => hβ.bijOn.mapsTo hx
  refine ⟨γ, hγ, (hγf (hmemA 0 ⟨le_rfl, zero_le_one⟩)).trans hf0,
    (hγf (hmemA s ⟨hs.1.le, hs.2.le⟩)).trans hfs,
    (hγf (hmemA 1 ⟨zero_le_one, le_rfl⟩)).trans hf1,
    (hγg (hmemB r ⟨hr.1.le, hr.2.le⟩)).trans hgr⟩

theorem exists_arc_pair_of_two_interior {A B : Set E} {α β : ℝ → E}
    (hα : IsPLHomeomorphOn α (Icc 0 1) A) (hβ : IsPLHomeomorphOn β (Icc 0 1) B)
    (hβ0 : β 0 = α 0) (hβ1 : β 1 = α 1) (hAB : A ∩ B = {α 0, α 1}) {s₁ s₂ : ℝ}
    (hs₁ : 0 < s₁) (h₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) :
    ∃ (A₂ B₂ : Set E) (α₂ β₂ : ℝ → E), IsPLHomeomorphOn α₂ (Icc 0 1) A₂ ∧
      IsPLHomeomorphOn β₂ (Icc 0 1) B₂ ∧ α₂ 0 = α 0 ∧ α₂ 1 = α s₂ ∧ β₂ 0 = α 0 ∧
        β₂ 1 = α s₂ ∧ α₂ (s₁ / s₂) = α s₁ ∧ β₂ (1 / 2) = α 1 ∧ A₂ ∪ B₂ = A ∪ B ∧
          A₂ ∩ B₂ = {α 0, α s₂} ∧ s₁ / s₂ ∈ Ioo 0 1 := by
  have hs₂pos : 0 < s₂ := hs₁.trans h₁₂
  have hsub := isPLHomeomorphOn_comp_mul_add_Icc hα le_rfl hs₂pos hs₂.le
  simp only [sub_zero, add_zero] at hsub
  have hrev := isPLHomeomorphOn_comp_mul_add_Icc (isPLHomeomorphOn_comp_one_sub hα)
    le_rfl (sub_pos.mpr hs₂) (sub_le_self 1 hs₂pos.le)
  simp only [sub_zero, add_zero] at hrev
  have hrevimg : (fun x => α (1 - x)) '' Icc 0 (1 - s₂) = α '' Icc s₂ 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by simp⟩
  rw [hrevimg] at hrev
  have hinj := hα.bijOn.injOn
  have hB1 : α 1 ∈ B := hβ1 ▸ hβ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hmeet : B ∩ α '' Icc s₂ 1 = {α 1} := by
    ext z
    constructor
    · rintro ⟨hzB, x, hx, rfl⟩
      have hzA : α x ∈ A ∩ B := ⟨hα.bijOn.mapsTo ⟨hs₂pos.le.trans hx.1, hx.2⟩, hzB⟩
      rw [hAB] at hzA
      rcases hzA with h | h
      · exfalso
        have := hinj ⟨hs₂pos.le.trans hx.1, hx.2⟩ ⟨le_rfl, zero_le_one⟩ h
        linarith [hx.1]
      · exact h
    · rintro rfl
      exact ⟨hB1, 1, ⟨hs₂.le, le_rfl⟩, rfl⟩
  obtain ⟨l, hl, hl0, hlhalf, hl1⟩ := exists_isPLHomeomorphOn_Icc_concat hβ hrev
    (by simp [hβ1]) (by rw [hβ1]; exact hmeet)
  refine ⟨α '' Icc 0 s₂, B ∪ α '' Icc s₂ 1, fun x => α (s₂ * x), l, hsub, hl, by simp,
    by simp, hl0.trans hβ0, ?_, ?_, hlhalf.trans hβ1, ?_, ?_,
    ⟨div_pos hs₁ hs₂pos, (div_lt_one hs₂pos).mpr h₁₂⟩⟩
  · rw [hl1]
    simp
  · simp only
    rw [mul_div_cancel₀ s₁ hs₂pos.ne']
  · rw [← union_assoc, union_comm (α '' Icc 0 s₂) B, union_assoc, ← image_union,
      Icc_union_Icc_eq_Icc hs₂pos.le hs₂.le, hα.image_eq, union_comm]
  · have hA0 : α 0 ∈ B := hβ0 ▸ hβ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hzB | ⟨y, hy, hyx⟩⟩
      · have hzA : α x ∈ A ∩ B := ⟨hα.bijOn.mapsTo ⟨hx.1, hx.2.trans hs₂.le⟩, hzB⟩
        rw [hAB] at hzA
        rcases hzA with h | h
        · exact Or.inl h
        · exfalso
          have := hinj ⟨hx.1, hx.2.trans hs₂.le⟩ ⟨zero_le_one, le_rfl⟩ h
          linarith [hx.2]
      · have hxy := hinj ⟨hs₂pos.le.trans hy.1, hy.2⟩ ⟨hx.1, hx.2.trans hs₂.le⟩ hyx
        right
        rw [← hyx, show y = s₂ by linarith [hy.1, hx.2, hxy]]
        exact mem_singleton _
    · rintro (rfl | rfl)
      · exact ⟨⟨0, ⟨le_rfl, hs₂pos.le⟩, rfl⟩, Or.inl hA0⟩
      · exact ⟨⟨s₂, ⟨hs₂pos.le, le_rfl⟩, rfl⟩, Or.inr ⟨s₂, ⟨le_rfl, hs₂.le⟩, rfl⟩⟩

theorem exists_isPLHomeomorphOn_circle_four_points {A B : Set E} {α β : ℝ → E}
    (hα : IsPLHomeomorphOn α (Icc 0 1) A) (hβ : IsPLHomeomorphOn β (Icc 0 1) B)
    (hβ0 : β 0 = α 0) (hβ1 : β 1 = α 1) (hAB : A ∩ B = {α 0, α 1}) {s r : ℝ}
    (hs : s ∈ Ioo 0 1) (hr : r ∈ Ioo 0 1) {S' : Set F} (hS' : IsPLSphere 1 S')
    {w : Fin 4 → F} (hw : ∀ i, w i ∈ S') (hwinj : Function.Injective w) :
    ∃ (π : Equiv.Perm (Fin 4)) (γ : E → F), IsPLHomeomorphOn γ (A ∪ B) S' ∧
      γ (α 0) = w (π 0) ∧ γ (α s) = w (π 1) ∧ γ (α 1) = w (π 2) ∧ γ (β r) = w (π 3) := by
  obtain ⟨A', B', α', β', hα', hβ', hα'0, hα'1, hβ'0, hβ'1, hU, hI⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS' (hw 0) (hw 2) (hwinj.ne (by decide))
  have finish : ∀ (π : Equiv.Perm (Fin 4)) (A₂ B₂ : Set F) (α₂ β₂ : ℝ → F) (s₂ r₂ : ℝ),
      IsPLHomeomorphOn α₂ (Icc 0 1) A₂ → IsPLHomeomorphOn β₂ (Icc 0 1) B₂ → β₂ 0 = α₂ 0 →
        β₂ 1 = α₂ 1 → A₂ ∩ B₂ = {α₂ 0, α₂ 1} → A₂ ∪ B₂ = S' → s₂ ∈ Ioo 0 1 →
          r₂ ∈ Ioo 0 1 → α₂ 0 = w (π 0) → α₂ s₂ = w (π 1) → α₂ 1 = w (π 2) →
            β₂ r₂ = w (π 3) →
              ∃ (π : Equiv.Perm (Fin 4)) (γ : E → F), IsPLHomeomorphOn γ (A ∪ B) S' ∧
                γ (α 0) = w (π 0) ∧ γ (α s) = w (π 1) ∧ γ (α 1) = w (π 2) ∧
                  γ (β r) = w (π 3) := by
    intro π A₂ B₂ α₂ β₂ s₂ r₂ hα₂ hβ₂ hβ₂0 hβ₂1 hI₂ hU₂ hs₂ hr₂ e0 e1 e2 e3
    obtain ⟨γ, hγ, h0, h1, h2, h3⟩ := exists_isPLHomeomorphOn_of_arc_pairs hα hβ hα₂ hβ₂ hβ0
      hβ1 hβ₂0 hβ₂1 hAB hI₂ hs hr hs₂ hr₂
    exact ⟨π, γ, hU₂ ▸ hγ, h0.trans e0, h1.trans e1, h2.trans e2, h3.trans e3⟩
  have hloc : ∀ i : Fin 4, i ≠ 0 → i ≠ 2 →
      (∃ x ∈ Ioo (0 : ℝ) 1, α' x = w i) ∨ (∃ x ∈ Ioo (0 : ℝ) 1, β' x = w i) := by
    intro i hi0 hi2
    have hmem : w i ∈ A' ∪ B' := hU.symm ▸ hw i
    have hne : w i ∉ ({w 0, w 2} : Set F) := by
      rintro (h | h)
      · exact hi0 (hwinj h)
      · exact hi2 (hwinj h)
    rcases hmem with h | h
    · left
      have hmem' : w i ∈ A' \ {α' 0, α' 1} := ⟨h, by rwa [hα'0, hα'1]⟩
      rw [← hα'.image_Ioo_eq_sdiff_endpoints zero_lt_one] at hmem'
      obtain ⟨x, hx, hxw⟩ := hmem'
      exact ⟨x, hx, hxw⟩
    · right
      have hmem' : w i ∈ B' \ {β' 0, β' 1} := ⟨h, by rwa [hβ'0, hβ'1]⟩
      rw [← hβ'.image_Ioo_eq_sdiff_endpoints zero_lt_one] at hmem'
      obtain ⟨x, hx, hxw⟩ := hmem'
      exact ⟨x, hx, hxw⟩
  have h13 : w 1 ≠ w 3 := hwinj.ne (by decide)
  have hβ'0' : β' 0 = α' 0 := hβ'0.trans hα'0.symm
  have hβ'1' : β' 1 = α' 1 := hβ'1.trans hα'1.symm
  have hI' : A' ∩ B' = {α' 0, α' 1} := by rw [hI, hα'0, hα'1]
  have hIsymm : B' ∩ A' = {β' 0, β' 1} := by rw [inter_comm, hI, hβ'0, hβ'1]
  have p23 : (Equiv.swap (2 : Fin 4) 3) 0 = 0 ∧ (Equiv.swap (2 : Fin 4) 3) 1 = 1 ∧
      (Equiv.swap (2 : Fin 4) 3) 2 = 3 ∧ (Equiv.swap (2 : Fin 4) 3) 3 = 2 := by decide
  have p13 : (Equiv.swap (1 : Fin 4) 3) 0 = 0 ∧ (Equiv.swap (1 : Fin 4) 3) 1 = 3 ∧
      (Equiv.swap (1 : Fin 4) 3) 2 = 2 ∧ (Equiv.swap (1 : Fin 4) 3) 3 = 1 := by decide
  have pc : ((Equiv.swap (2 : Fin 4) 3).trans (Equiv.swap 1 3)) 0 = 0 ∧
      ((Equiv.swap (2 : Fin 4) 3).trans (Equiv.swap 1 3)) 1 = 3 ∧
      ((Equiv.swap (2 : Fin 4) 3).trans (Equiv.swap 1 3)) 2 = 1 ∧
      ((Equiv.swap (2 : Fin 4) 3).trans (Equiv.swap 1 3)) 3 = 2 := by decide
  rcases hloc 1 (by decide) (by decide) with ⟨s₁, hs₁, h1⟩ | ⟨r₁, hr₁, h1⟩ <;>
    rcases hloc 3 (by decide) (by decide) with ⟨s₃, hs₃, h3⟩ | ⟨r₃, hr₃, h3⟩
  · rcases lt_trichotomy s₁ s₃ with hlt | heq | hgt
    · obtain ⟨A₂, B₂, α₂, β₂, hα₂, hβ₂, e0, e1, f0, f1, em, fm, hU₂, hI₂, hm⟩ :=
        exists_arc_pair_of_two_interior hα' hβ' hβ'0' hβ'1' hI' hs₁.1 hlt hs₃.2
      refine finish (Equiv.swap (2 : Fin 4) 3) A₂ B₂ α₂ β₂ _ (1 / 2) hα₂ hβ₂ (f0.trans e0.symm)
          (f1.trans e1.symm)
        (by rw [hI₂, e0, e1]) (hU₂.trans (hU)) hm ⟨by norm_num, by norm_num⟩ ?_ ?_ ?_ ?_
      · rw [p23.1, e0, hα'0]
      · rw [p23.2.1, em, h1]
      · rw [p23.2.2.1, e1, h3]
      · rw [p23.2.2.2, fm, hα'1]
    · exact absurd (h1.symm.trans (heq ▸ h3)) h13
    · obtain ⟨A₂, B₂, α₂, β₂, hα₂, hβ₂, e0, e1, f0, f1, em, fm, hU₂, hI₂, hm⟩ :=
        exists_arc_pair_of_two_interior hα' hβ' hβ'0' hβ'1' hI' hs₃.1 hgt hs₁.2
      refine finish ((Equiv.swap (2 : Fin 4) 3).trans (Equiv.swap 1 3)) A₂ B₂ α₂ β₂ _ (1 / 2) hα₂
          hβ₂ (f0.trans e0.symm) (f1.trans e1.symm)
        (by rw [hI₂, e0, e1]) (hU₂.trans (hU)) hm ⟨by norm_num, by norm_num⟩ ?_ ?_ ?_ ?_
      · rw [pc.1, e0, hα'0]
      · rw [pc.2.1, em, h3]
      · rw [pc.2.2.1, e1, h1]
      · rw [pc.2.2.2, fm, hα'1]
  · refine finish (Equiv.refl _) A' B' α' β' s₁ r₃ hα' hβ' hβ'0' hβ'1' hI' hU hs₁ hr₃ ?_ ?_ ?_ ?_
    · exact hα'0
    · exact h1
    · exact hα'1
    · exact h3
  · refine finish (Equiv.swap (1 : Fin 4) 3) A' B' α' β' s₃ r₁ hα' hβ' hβ'0' hβ'1' hI' hU hs₃ hr₁
        ?_ ?_ ?_ ?_
    · rw [p13.1]
      exact hα'0
    · rw [p13.2.1]
      exact h3
    · rw [p13.2.2.1]
      exact hα'1
    · rw [p13.2.2.2]
      exact h1
  · rcases lt_trichotomy r₁ r₃ with hlt | heq | hgt
    · obtain ⟨A₂, B₂, α₂, β₂, hα₂, hβ₂, e0, e1, f0, f1, em, fm, hU₂, hI₂, hm⟩ :=
        exists_arc_pair_of_two_interior hβ' hα' hβ'0'.symm hβ'1'.symm hIsymm hr₁.1 hlt hr₃.2
      refine finish (Equiv.swap (2 : Fin 4) 3) A₂ B₂ α₂ β₂ _ (1 / 2) hα₂ hβ₂ (f0.trans e0.symm)
          (f1.trans e1.symm)
        (by rw [hI₂, e0, e1]) (hU₂.trans (by rw [union_comm, hU])) hm ⟨by norm_num, by norm_num⟩
        ?_ ?_ ?_ ?_
      · rw [p23.1, e0, hβ'0]
      · rw [p23.2.1, em, h1]
      · rw [p23.2.2.1, e1, h3]
      · rw [p23.2.2.2, fm, hβ'1]
    · exact absurd (h1.symm.trans (heq ▸ h3)) h13
    · obtain ⟨A₂, B₂, α₂, β₂, hα₂, hβ₂, e0, e1, f0, f1, em, fm, hU₂, hI₂, hm⟩ :=
        exists_arc_pair_of_two_interior hβ' hα' hβ'0'.symm hβ'1'.symm hIsymm hr₃.1 hgt hr₁.2
      refine finish ((Equiv.swap (2 : Fin 4) 3).trans (Equiv.swap 1 3)) A₂ B₂ α₂ β₂ _ (1 / 2) hα₂
          hβ₂ (f0.trans e0.symm) (f1.trans e1.symm)
        (by rw [hI₂, e0, e1]) (hU₂.trans (by rw [union_comm, hU])) hm ⟨by norm_num, by norm_num⟩
        ?_ ?_ ?_ ?_
      · rw [pc.1, e0, hβ'0]
      · rw [pc.2.1, em, h3]
      · rw [pc.2.2.1, e1, h1]
      · rw [pc.2.2.2, fm, hβ'1]

end DifferentialGeometry.Topology.PiecewiseLinear
