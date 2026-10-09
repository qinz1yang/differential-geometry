/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem extend_interval_homeomorph {a b c d e f : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b < c) (hde : d ≤ e) (hef : e < f)
    (hg : IsPLHomeomorphOn g (Icc a b) (Icc d e)) (hgb : g b = e) :
    ∃ h : ℝ → ℝ, IsPLHomeomorphOn h (Icc a c) (Icc d f) ∧
      EqOn h g (Icc a b) ∧ h c = f := by
  obtain ⟨q, hq, hqb, hqc⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints hbc hef
  have hcompat : EqOn g q (Icc a b ∩ Icc b c) := by
    intro x hx
    have hxb : x = b := le_antisymm hx.1.2 hx.2.1
    rw [hxb, hgb, hqb]
  have hmeet : SurjOn g (Icc a b ∩ Icc b c) (Icc d e ∩ Icc e f) := by
    intro y hy
    have hye : y = e := le_antisymm hy.1.2 hy.2.1
    exact ⟨b, ⟨⟨hab, le_rfl⟩, ⟨le_rfl, hbc.le⟩⟩, hgb.trans hye.symm⟩
  obtain ⟨h, hh, hhg, hhq⟩ := exists_isPLHomeomorphOn_union
    isHPolytope_Icc.isPolyhedron isHPolytope_Icc.isPolyhedron hg hq hcompat hmeet
  rw [Icc_union_Icc_eq_Icc hab hbc.le, Icc_union_Icc_eq_Icc hde hef.le] at hh
  exact ⟨h, hh, hhg, (hhq ⟨hbc.le, le_rfl⟩).trans hqc⟩

theorem exists_isPLHomeomorphOn_Icc_map_three_points
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : ℝ}
    (ha₀ : a₀ < a₁) (ha₁ : a₁ < a₂) (ha₂ : a₂ < a₃) (ha₃ : a₃ < a₄)
    (hb₀ : b₀ < b₁) (hb₁ : b₁ < b₂) (hb₂ : b₂ < b₃) (hb₃ : b₃ < b₄) :
    ∃ f : ℝ → ℝ, IsPLHomeomorphOn f (Icc a₀ a₄) (Icc b₀ b₄) ∧
      f a₀ = b₀ ∧ f a₁ = b₁ ∧ f a₂ = b₂ ∧ f a₃ = b₃ ∧ f a₄ = b₄ := by
  obtain ⟨f₀, hf₀, hf₀l, hf₀r⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints ha₀ hb₀
  obtain ⟨f₁, hf₁, h₁₀, hf₁r⟩ :=
    extend_interval_homeomorph ha₀.le ha₁ hb₀.le hb₁ hf₀ hf₀r
  obtain ⟨f₂, hf₂, h₂₁, hf₂r⟩ := extend_interval_homeomorph
    (ha₀.le.trans ha₁.le) ha₂ (hb₀.le.trans hb₁.le) hb₂ hf₁ hf₁r
  obtain ⟨f₃, hf₃, h₃₂, hf₃r⟩ := extend_interval_homeomorph
    (ha₀.le.trans (ha₁.le.trans ha₂.le)) ha₃
    (hb₀.le.trans (hb₁.le.trans hb₂.le)) hb₃ hf₂ hf₂r
  refine ⟨f₃, hf₃, ?_, ?_, ?_, ?_, hf₃r⟩
  · exact (h₃₂ ⟨le_rfl, ha₀.le.trans (ha₁.le.trans ha₂.le)⟩).trans
      ((h₂₁ ⟨le_rfl, ha₀.le.trans ha₁.le⟩).trans
        ((h₁₀ ⟨le_rfl, ha₀.le⟩).trans hf₀l))
  · exact (h₃₂ ⟨ha₀.le, ha₁.le.trans ha₂.le⟩).trans
      ((h₂₁ ⟨ha₀.le, ha₁.le⟩).trans ((h₁₀ ⟨ha₀.le, le_rfl⟩).trans hf₀r))
  · exact (h₃₂ ⟨ha₀.le.trans ha₁.le, ha₂.le⟩).trans
      ((h₂₁ ⟨ha₀.le.trans ha₁.le, le_rfl⟩).trans hf₁r)
  · exact (h₃₂ ⟨ha₀.le.trans (ha₁.le.trans ha₂.le), le_rfl⟩).trans hf₂r

theorem IsPLHomeomorphOn.exists_parametrization_three_points
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {γ : ℝ → E} {T : Set E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) T)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c < 1) :
    ∃ δ : ℝ → E, IsPLHomeomorphOn δ (Icc 0 1) T ∧
      δ 0 = γ 0 ∧ δ (1 / 4) = γ a ∧ δ (1 / 2) = γ b ∧
      δ (3 / 4) = γ c ∧ δ 1 = γ 1 := by
  obtain ⟨f, hf, hf₀, hf₁, hf₂, hf₃, hf₄⟩ :=
    exists_isPLHomeomorphOn_Icc_map_three_points
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 : ℝ) / 4 < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 3 / 4) (by norm_num : (3 : ℝ) / 4 < 1)
      ha hab hbc hc
  exact ⟨γ ∘ f, hf.trans hγ, congrArg γ hf₀, congrArg γ hf₁, congrArg γ hf₂,
    congrArg γ hf₃, congrArg γ hf₄⟩

end DifferentialGeometry.Topology.PiecewiseLinear
