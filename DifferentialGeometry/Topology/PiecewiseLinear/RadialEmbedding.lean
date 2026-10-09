/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Cone
import Mathlib.Data.Set.Card
import Mathlib.Topology.Order.IntermediateValue

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem eq_of_real_embedding_on_radial_intervals
    {p x y : E} {S U : Set E} (hS : IsRadiallyInjective p S)
    (hx : x ∈ S) (hy : y ∈ S) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {f : E → ℝ} (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hxU : ∀ t ∈ Icc 0 a, p + t • (x - p) ∈ U)
    (hyU : ∀ t ∈ Icc 0 b, p + t • (y - p) ∈ U)
    (hxpos : f p < f (p + a • (x - p)))
    (hypos : f p < f (p + b • (y - p))) : x = y := by
  let c : ℝ := (f p + min (f (p + a • (x - p))) (f (p + b • (y - p)))) / 2
  have hc : f p < c := by
    have hm := lt_min hxpos hypos
    dsimp [c]
    linarith
  have hcx : c ≤ f (p + a • (x - p)) := by
    have hm := min_le_left (f (p + a • (x - p))) (f (p + b • (y - p)))
    dsimp [c]
    linarith
  have hcy : c ≤ f (p + b • (y - p)) := by
    have hm := min_le_right (f (p + a • (x - p))) (f (p + b • (y - p)))
    dsimp [c]
    linarith
  have hcontx : ContinuousOn (fun t : ℝ => f (p + t • (x - p))) (Icc 0 a) :=
    hf.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hxU
  have hconty : ContinuousOn (fun t : ℝ => f (p + t • (y - p))) (Icc 0 b) :=
    hf.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hyU
  obtain ⟨s, hs, hfs⟩ := isPreconnected_Icc.intermediate_value
    (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, ha.le⟩)
    (show a ∈ Icc 0 a from ⟨ha.le, le_rfl⟩) hcontx
    (show c ∈ Icc (f (p + 0 • (x - p))) (f (p + a • (x - p))) by
      simpa only [zero_smul, add_zero, mem_Icc] using And.intro hc.le hcx)
  obtain ⟨t, ht, hft⟩ := isPreconnected_Icc.intermediate_value
    (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb.le⟩)
    (show b ∈ Icc 0 b from ⟨hb.le, le_rfl⟩) hconty
    (show c ∈ Icc (f (p + 0 • (y - p))) (f (p + b • (y - p))) by
      simpa only [zero_smul, add_zero, mem_Icc] using And.intro hc.le hcy)
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (by
    intro heq
    have hfc : f p = c := by simpa only [← heq, zero_smul, add_zero] using hfs
    exact hc.ne hfc)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    have hfc : f p = c := by simpa only [← heq, zero_smul, add_zero] using hft
    exact hc.ne hfc)
  exact hS.eq_of_add_smul_eq hx hy hspos htpos
    (hinj (hxU s hs) (hyU t ht) (hfs.trans hft.symm))

theorem IsRadiallyInjective.encard_le_two_of_real_embedding
    {p : E} {S U : Set E} (hS : IsRadiallyInjective p S) (hp : p ∉ S)
    {f : E → ℝ} (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hsegments : ∀ q ∈ S, ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Icc 0 a, p + t • (q - p) ∈ U) :
    S.encard ≤ 2 := by
  classical
  choose a ha hU using fun q : S => hsegments q q.property
  have hne : ∀ q : S, f (p + a q • ((q : E) - p)) ≠ f p := by
    intro q heq
    have hpU : p ∈ U := by simpa only [zero_smul, add_zero] using hU q 0 ⟨le_rfl, (ha q).le⟩
    have hpoint := hinj (hU q (a q) ⟨(ha q).le, le_rfl⟩) hpU heq
    have hsmul : a q • ((q : E) - p) = 0 := by simpa only [add_eq_left] using hpoint
    have hqp : (q : E) = p := sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_left (ha q).ne')
    exact hp (hqp ▸ q.property)
  let d : S → Bool := fun q => decide (f p < f (p + a q • ((q : E) - p)))
  have hd : Function.Injective d := by
    intro x y hxy
    have hsign : (f p < f (p + a x • ((x : E) - p))) ↔
        (f p < f (p + a y • ((y : E) - p))) := by
      exact decide_eq_decide.mp hxy
    apply Subtype.ext
    by_cases hxpos : f p < f (p + a x • ((x : E) - p))
    · exact eq_of_real_embedding_on_radial_intervals hS x.property y.property (ha x) (ha y)
        hf hinj (hU x) (hU y) hxpos (hsign.mp hxpos)
    · have hypos := mt hsign.mpr hxpos
      have hxneg := lt_of_le_of_ne (le_of_not_gt hxpos) (hne x)
      have hyneg := lt_of_le_of_ne (le_of_not_gt hypos) (hne y)
      exact eq_of_real_embedding_on_radial_intervals hS x.property y.property (ha x) (ha y)
        hf.neg (neg_injective.comp_injOn hinj) (hU x) (hU y)
        (neg_lt_neg hxneg) (neg_lt_neg hyneg)
  have hcard := ENat.card_le_card_of_injective hd
  simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_bool, Nat.cast_ofNat,
      ENat.card_coe_set_eq] using hcard

end DifferentialGeometry.Topology.PiecewiseLinear
