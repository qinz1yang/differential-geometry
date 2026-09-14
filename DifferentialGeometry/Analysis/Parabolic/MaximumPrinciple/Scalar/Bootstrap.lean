import Mathlib.Algebra.Field.Periodic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic.Push

open Set

namespace DifferentialGeometry.Analysis

variable {X : Type*} [TopologicalSpace X]

theorem lt_on_compact_slab_of_strict_improvement {S : Set X} (hS : IsCompact S)
    {f : ℝ → X → ℝ} {s u K : ℝ}
    (hf : ContinuousOn (fun p : ℝ × X => f p.1 p.2) (Icc s u ×ˢ S))
    (hinit : ∀ x ∈ S, f s x < K)
    (himp : ∀ t ∈ Ioc s u, (∀ τ ∈ Icc s t, ∀ x ∈ S, f τ x ≤ K) → ∀ x ∈ S, f t x < K) :
    ∀ t ∈ Icc s u, ∀ x ∈ S, f t x < K := by
  by_contra h
  push Not at h
  obtain ⟨t, ht, x, hx, hfx⟩ := h
  let bad := (Icc s u ×ˢ S) ∩ (fun p : ℝ × X => f p.1 p.2) ⁻¹' Ici K
  have hbad : IsCompact bad := hf.upperSemicontinuousOn.isCompact_inter_preimage_Ici (isCompact_Icc.prod hS) K
  have hbadne : bad.Nonempty := ⟨(t, x), ⟨⟨ht, hx⟩, hfx⟩⟩
  obtain ⟨⟨τ, y⟩, hτy, hmin⟩ := hbad.exists_isMinOn hbadne continuous_fst.continuousOn
  have hτ : τ ∈ Icc s u := hτy.1.1
  have hy : y ∈ S := hτy.1.2
  have hcontact : K ≤ f τ y := hτy.2
  have hsτ : s < τ := by
    apply lt_of_le_of_ne hτ.1
    intro heq
    exact (not_le_of_gt (hinit y hy)) (heq ▸ hcontact)
  have hprior : ∀ v ∈ Icc s τ, ∀ z ∈ S, f v z ≤ K := by
    intro v hv z hz
    by_contra hnot
    have hfv : K < f v z := lt_of_not_ge hnot
    have htime : ContinuousOn (fun w => f w z) (Icc s v) :=
      hf.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun w hw => ⟨⟨hw.1, hw.2.trans (hv.2.trans hτ.2)⟩, hz⟩)
    obtain ⟨w, hw, hwf⟩ := intermediate_value_Icc hv.1 htime ⟨(hinit z hz).le, hfv.le⟩
    have hwv : w < v := by
      apply lt_of_le_of_ne hw.2
      intro heq
      exact (ne_of_lt hfv) (by simpa only [heq] using hwf.symm)
    have hwbad : (w, z) ∈ bad := ⟨⟨⟨hw.1, hw.2.trans (hv.2.trans hτ.2)⟩, hz⟩, hwf.ge⟩
    have hh : τ ≤ w := hmin hwbad
    exact (not_lt_of_ge hv.2) (hh.trans_lt hwv)
  exact (not_le_of_gt (himp τ ⟨hsτ, hτ.2⟩ hprior y hy)) hcontact

theorem periodic_le_div_time_of_strict_improvement
    {k : ℝ → ℝ → ℝ} {s u K period : ℝ} (hsu : s < u) (hK : 0 < K) (hperiod : 0 < period)
    (hk : ContinuousOn (fun p : ℝ × ℝ => k p.1 p.2) (univ ×ˢ Icc s u))
    (hper : ∀ τ ∈ Icc s u, Function.Periodic (fun x => k x τ) period)
    (himp : ∀ v ∈ Ioc s u, (∀ y τ, τ ∈ Ioc s v → k y τ ≤ K / (τ - s)) →
      ∀ x, k x v < K / (v - s)) : ∀ x, k x u ≤ K / (u - s) := by
  let f := fun τ x => (τ - s) * k x τ
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc s u ×ˢ Icc 0 period) :=
    (continuousOn_fst.sub continuousOn_const).mul
      (hk.comp continuous_swap.continuousOn (fun p hp => ⟨mem_univ p.2, hp.1⟩))
  have hbound : ∀ τ ∈ Icc s u, ∀ x ∈ Icc (0 : ℝ) period, f τ x < K := by
    apply lt_on_compact_slab_of_strict_improvement isCompact_Icc hf
    · intro x hx
      simpa only [f, sub_self, zero_mul] using hK
    · intro v hv hprior x hx
      have hboot : ∀ y τ, τ ∈ Ioc s v → k y τ ≤ K / (τ - s) := by
        intro y τ hτ
        obtain ⟨z, hz, heq⟩ := (hper τ ⟨hτ.1.le, hτ.2.trans hv.2⟩).exists_mem_Ico₀ hperiod y
        rw [heq]
        apply (le_div_iff₀ (sub_pos.mpr hτ.1)).mpr
        have hh := hprior τ ⟨hτ.1.le, hτ.2⟩ z ⟨hz.1, hz.2.le⟩
        exact (mul_comm _ _).trans_le hh
      have hh := (lt_div_iff₀ (sub_pos.mpr hv.1)).mp (himp v hv hboot x)
      exact (mul_comm _ _).trans_lt hh
  intro x
  obtain ⟨z, hz, heq⟩ := (hper u ⟨hsu.le, le_rfl⟩).exists_mem_Ico₀ hperiod x
  rw [heq]
  apply (le_div_iff₀ (sub_pos.mpr hsu)).mpr
  exact ((mul_comm _ _).trans_lt (hbound u ⟨hsu.le, le_rfl⟩ z ⟨hz.1, hz.2.le⟩)).le

end DifferentialGeometry.Analysis
