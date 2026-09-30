import DifferentialGeometry.Topology.LoopSpace.AffineLift
import Mathlib.Tactic.Linarith
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber

noncomputable section

open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

def IsWeaklyMonotoneOnce (σ : C(loopCircle, loopCircle)) : Prop :=
  ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧
    ((Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1) ∨
      (Antitone ψ ∧ ∀ t, ψ (t + 1) = ψ t - 1))



open Function in
theorem IsWeaklyMonotoneOnce.comp
    {σ δ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ)
    (hδ : IsWeaklyMonotoneOnce δ) : IsWeaklyMonotoneOnce (σ.comp δ) := by
  obtain ⟨ψ, hψc, hψσ, hψsign⟩ := hσ
  obtain ⟨f, hfc, hfδ, hfsign⟩ := hδ
  refine ⟨ψ ∘ f, hψc.comp hfc, ?_, ?_⟩
  · intro s
    change (ψ (f s) : loopCircle) = σ (δ (s : loopCircle))
    rw [hψσ, hfδ]
  · rcases hψsign with ⟨hψm, hψp⟩ | ⟨hψm, hψp⟩
    · rcases hfsign with ⟨hfm, hfp⟩ | ⟨hfm, hfp⟩
      · exact Or.inl ⟨hψm.comp hfm, fun s => by simp only [Function.comp_apply, hfp, hψp]⟩
      · refine Or.inr ⟨hψm.comp_antitone hfm, fun s => ?_⟩
        dsimp only [Function.comp_apply]
        rw [hfp]
        have h := hψp (f s - 1)
        rw [sub_add_cancel] at h
        linarith
    · rcases hfsign with ⟨hfm, hfp⟩ | ⟨hfm, hfp⟩
      · exact Or.inr ⟨hψm.comp_monotone hfm, fun s => by simp only [Function.comp_apply, hfp, hψp]⟩
      · refine Or.inl ⟨hψm.comp hfm, fun s => ?_⟩
        dsimp only [Function.comp_apply]
        rw [hfp]
        have h := hψp (f s - 1)
        rw [sub_add_cancel] at h
        linarith

open Function in
theorem isWeaklyMonotoneOnce_symm_of_monotone_lift
    (δ : loopCircle ≃ₜ loopCircle) (e : ℝ ≃ₜ ℝ)
    (hlift : ∀ s : ℝ, δ (s : loopCircle) = (e s : loopCircle))
    (hmono : Monotone e) (hperiod : ∀ s, e (s + 1) = e s + 1) :
    IsWeaklyMonotoneOnce
      (⟨δ.symm, δ.symm.continuous⟩ : C(loopCircle, loopCircle)) := by
  have hstrict : StrictMono e := hmono.strictMono_of_injective e.injective
  have hinv : Monotone e.symm := by
    intro x y hxy
    apply hstrict.le_iff_le.mp
    simpa only [e.apply_symm_apply] using hxy
  refine ⟨e.symm, e.symm.continuous, ?_,
    Or.inl ⟨hinv, inverse_affinePeriodic e hperiod⟩⟩
  intro s
  apply δ.injective
  change δ ((e.symm s : ℝ) : loopCircle) = δ (δ.symm (s : loopCircle))
  rw [hlift, e.apply_symm_apply, δ.apply_symm_apply]

end DifferentialGeometry.Geometry

end

section

namespace CircleDeg1Lift

theorem sub_le_two_thirds_of_map_thirds
    (f : CircleDeg1Lift)
    (h₁ : f (1 / 3 : ℝ) = f 0 + 1 / 3)
    (h₂ : f (2 / 3 : ℝ) = f 0 + 2 / 3)
    {a b : ℝ} (hΔ : b - a ≤ 1 / 3) :
    f b - f a ≤ 2 / 3 := by
  let x : ℝ := Int.fract a
  let n : ℤ := ⌊a⌋
  let t : ℝ := b - a
  have hx0 : 0 ≤ x := Int.fract_nonneg a
  have hx1 : x < 1 := Int.fract_lt_one a
  have ht : t ≤ 1 / 3 := hΔ
  have ha : a = x + (n : ℝ) := (Int.fract_add_floor a).symm
  have hb : b = (x + t) + (n : ℝ) := by
    dsimp [t]
    rw [ha]
    ring
  have hred : f b - f a = f (x + t) - f x := by
    rw [hb, ha, f.map_add_int, f.map_add_int]
    ring
  rw [hred]
  by_cases hxthird : x ≤ 1 / 3
  · have hupper : f (x + t) ≤ f (2 / 3 : ℝ) := f.monotone (by linarith)
    have hlower : f 0 ≤ f x := f.monotone hx0
    rw [h₂] at hupper
    linarith
  · have hxthird' : 1 / 3 < x := lt_of_not_ge hxthird
    by_cases hxtwo : x ≤ 2 / 3
    · have hupper : f (x + t) ≤ f 1 := f.monotone (by linarith)
      have hlower : f (1 / 3 : ℝ) ≤ f x := f.monotone hxthird'.le
      have hperiod : f 1 = f 0 + 1 := by simpa using f.map_add_one 0
      rw [h₁] at hlower
      rw [hperiod] at hupper
      linarith
    · have hxtwo' : 2 / 3 < x := lt_of_not_ge hxtwo
      have hupper : f (x + t) ≤ f ((1 / 3 : ℝ) + 1) := f.monotone (by linarith)
      have hlower : f (2 / 3 : ℝ) ≤ f x := f.monotone hxtwo'.le
      rw [f.map_add_one, h₁] at hupper
      rw [h₂] at hlower
      linarith

end CircleDeg1Lift

end

noncomputable section

open Set
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

private theorem real_eq_of_mem_unit_interval_of_coe_eq
    {x a : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha0 : 0 < a) (ha1 : a < 1)
    (h : (x : loopCircle) = (a : loopCircle)) : x = a := by
  have ha : a ∈ Ico (0 : ℝ) (0 + 1) := ⟨ha0.le, by linarith⟩
  have hz : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
  have ha_ne : (a : loopCircle) ≠ 0 := by
    intro heq
    have heq' : (a : loopCircle) = ((0 : ℝ) : loopCircle) := by
      simpa only [AddCircle.coe_zero] using heq
    have hzero := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) ha hz).mp heq'
    exact ha0.ne' hzero
  have hx1 : x < 1 := by
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · exact hlt
    · exact False.elim (ha_ne (h.symm.trans (heq ▸ AddCircle.coe_period (1 : ℝ))))
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ))
    ⟨hx.1, by linarith⟩ ha).mp h

private theorem real_eq_sub_one_of_mem_neg_unit_interval_of_coe_eq
    {x a : ℝ} (hx : x ∈ Icc (-1 : ℝ) 0) (ha0 : 0 < a) (ha1 : a < 1)
    (h : (x : loopCircle) = (a : loopCircle)) : x = a - 1 := by
  have hx' : x + 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h' : ((x + 1 : ℝ) : loopCircle) = (a : loopCircle) :=
    (AddCircle.coe_add_period (1 : ℝ) x).trans h
  have := real_eq_of_mem_unit_interval_of_coe_eq hx' ha0 ha1 h'
  linarith

theorem IsWeaklyMonotoneOnce.exists_monotone_lift_of_three_fixed_points
    {σ : C(loopCircle, loopCircle)}
    (hσ : IsWeaklyMonotoneOnce σ) {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1)
    (h0 : σ (0 : loopCircle) = 0)
    (ha : σ (a : loopCircle) = (a : loopCircle))
    (hb : σ (b : loopCircle) = (b : loopCircle)) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧
      Monotone ψ ∧ (∀ t, ψ (t + 1) = ψ t + 1) ∧
      ψ 0 = 0 ∧ ψ a = a ∧ ψ b = b := by
  obtain ⟨ψ, hψc, hψl, hdir⟩ := hσ
  have hz : (ψ 0 : loopCircle) = 0 := by
    simpa only [AddCircle.coe_zero] using (hψl 0).trans h0
  let φ : ℝ → ℝ := fun t => ψ t - ψ 0
  have hφc : Continuous φ := hψc.sub continuous_const
  have hφl : ∀ t : ℝ, (φ t : loopCircle) = σ (t : loopCircle) := by
    intro t
    rw [show φ t = ψ t - ψ 0 by rfl, AddCircle.coe_sub, hψl, hz, sub_zero]
  have hφ0 : φ 0 = 0 := by simp [φ]
  rcases hdir with ⟨hmono, hper⟩ | ⟨hanti, hper⟩
  · have hφmono : Monotone φ := by
      intro x y hxy
      exact sub_le_sub_right (hmono hxy) (ψ 0)
    have hφper : ∀ t, φ (t + 1) = φ t + 1 := by
      intro t
      dsimp [φ]
      rw [hper t]
      ring
    have hφ1 : φ 1 = 1 := by simpa only [zero_add, hφ0] using hφper 0
    have hφa : φ a = a := by
      apply real_eq_of_mem_unit_interval_of_coe_eq ?_ ha0 (hab.trans hb1)
        ((hφl a).trans ha)
      constructor
      · simpa only [hφ0] using hφmono ha0.le
      · simpa only [hφ1] using hφmono (hab.trans hb1).le
    have hφb : φ b = b := by
      apply real_eq_of_mem_unit_interval_of_coe_eq ?_ (ha0.trans hab) hb1
        ((hφl b).trans hb)
      constructor
      · simpa only [hφ0] using hφmono (ha0.trans hab).le
      · simpa only [hφ1] using hφmono hb1.le
    exact ⟨φ, hφc, hφl, hφmono, hφper, hφ0, hφa, hφb⟩
  · have hφanti : Antitone φ := by
      intro x y hxy
      exact sub_le_sub_right (hanti hxy) (ψ 0)
    have hφper : ∀ t, φ (t + 1) = φ t - 1 := by
      intro t
      dsimp [φ]
      rw [hper t]
      ring
    have hφ1 : φ 1 = -1 := by
      simpa only [zero_add, hφ0, zero_sub] using hφper 0
    have hφa : φ a = a - 1 := by
      apply real_eq_sub_one_of_mem_neg_unit_interval_of_coe_eq ?_ ha0 (hab.trans hb1)
        ((hφl a).trans ha)
      constructor
      · simpa only [hφ1] using hφanti (hab.trans hb1).le
      · simpa only [hφ0] using hφanti ha0.le
    have hφb : φ b = b - 1 := by
      apply real_eq_sub_one_of_mem_neg_unit_interval_of_coe_eq ?_ (ha0.trans hab) hb1
        ((hφl b).trans hb)
      constructor
      · simpa only [hφ1] using hφanti hb1.le
      · simpa only [hφ0] using hφanti (ha0.trans hab).le
    have := hφanti hab.le
    linarith

end DifferentialGeometry.Geometry

end
