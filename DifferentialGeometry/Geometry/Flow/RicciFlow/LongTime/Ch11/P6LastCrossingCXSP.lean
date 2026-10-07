import DifferentialGeometry.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# CX-SPINE G1：last threshold 的 greatest 与 closed-tail 读法

复用 ContinuousOn.exists_eq_and_forall_gt，不重证 compact-level-set / IVT。
闭尾段只能给 Q ≤ f；去掉等高起点后给 Q < f。所有参数均在同一 compact interval。
本文件是纯 order-topology 层，不宣称 Claim 2 或 hspine 已闭合。
-/

open Set

namespace GC.LongTime.Ch11

/-- 连续函数从低于 Q 到高于 Q，存在 greatest 等高参数；其后 strict high。 -/
theorem exists_last_threshold_CXSP {f : ℝ → ℝ} {a b Q : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) (ha : f a < Q) (hb : Q < f b) :
    ∃ s ∈ Ioo a b, f s = Q ∧
      (∀ u ∈ Icc a b, f u = Q → u ≤ s) ∧
      (∀ u ∈ Icc s b, Q ≤ f u) ∧
      ∀ u ∈ Ioc s b, Q < f u := by
  obtain ⟨s, hs, hQ, htail⟩ := hf.exists_eq_and_forall_gt hab ha.le hb
  have has : a < s := lt_of_le_of_ne hs.1 (by
    intro h
    have hfa : f a = Q := by simpa only [← h] using hQ
    exact ha.ne hfa)
  refine ⟨s, ⟨has, hs.2⟩, hQ, ?_, ?_, htail⟩
  · intro u hu huQ
    by_contra h
    have hsu : s < u := lt_of_not_ge h
    exact (htail u ⟨hsu, hu.2⟩).ne' huQ
  · intro u hu
    rcases eq_or_lt_of_le hu.1 with hsu | hsu
    · simpa only [← hsu, hQ] using (le_refl Q)
    · exact (htail u ⟨hsu, hu.2⟩).le

/-- 同一 last crossing 的 affine tail：长度 b-s>0，起点等高，正参数 strict high。 -/
theorem exists_last_threshold_tail_CXSP {f : ℝ → ℝ} {a b Q : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) (ha : f a < Q) (hb : Q < f b) :
    ∃ s ∈ Ioo a b, f s = Q ∧
      (∀ u ∈ Icc a b, f u = Q → u ≤ s) ∧
      0 < b - s ∧
      (∀ v ∈ Icc (0 : ℝ) (b - s), Q ≤ f (s + v)) ∧
      ∀ v ∈ Ioc (0 : ℝ) (b - s), Q < f (s + v) := by
  obtain ⟨s, hs, hQ, hlast, hclosed, hopen⟩ := exists_last_threshold_CXSP hf hab ha hb
  refine ⟨s, hs, hQ, hlast, sub_pos.mpr hs.2, ?_, ?_⟩
  · intro v hv
    exact hclosed (s + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩
  · intro v hv
    exact hopen (s + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩

end GC.LongTime.Ch11
