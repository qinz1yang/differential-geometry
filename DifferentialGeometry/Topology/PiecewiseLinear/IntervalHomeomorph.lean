/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import Mathlib.Topology.Order.IntermediateValue

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_Icc_map_endpoints {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) :
    ∃ f : ℝ → ℝ, IsPLHomeomorphOn f (Icc a b) (Icc c d) ∧ f a = c ∧ f b = d := by
  let q := (d - c) / (b - a)
  let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ c +
    q • (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ a)
  have hA (x : ℝ) : A x = c + q * (x - a) := rfl
  have hq : 0 < q := div_pos (sub_pos.mpr hcd) (sub_pos.mpr hab)
  have hleft : A a = c := by rw [hA]; ring
  have hright : A b = d := by
    rw [hA, div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
    ring
  have hmono : StrictMono A := by
    intro x y hxy
    rw [hA, hA]
    exact add_lt_add_right (mul_lt_mul_of_pos_left (sub_lt_sub_right hxy a) hq) c
  have himage : A '' Icc a b = Icc c d := by
    rw [A.continuous_of_finiteDimensional.image_Icc_of_strictMono hmono, hleft, hright]
  refine ⟨A, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope A isHPolytope_Icc) ?_, hleft, hright⟩
  exact himage ▸ hmono.injective.injOn.bijOn_image

theorem exists_isPLHomeomorphOn_Icc_map_Icc
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ}
    (ha₀ : a₀ < a₁) (ha₁ : a₁ < a₂) (ha₂ : a₂ < a₃)
    (hb₀ : b₀ < b₁) (hb₁ : b₁ < b₂) (hb₂ : b₂ < b₃) :
    ∃ f : ℝ → ℝ, IsPLHomeomorphOn f (Icc a₀ a₃) (Icc b₀ b₃) ∧
      f a₀ = b₀ ∧ f a₃ = b₃ ∧ f '' Icc a₁ a₂ = Icc b₁ b₂ := by
  obtain ⟨f₀, hf₀, hf₀l, hf₀r⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints ha₀ hb₀
  obtain ⟨f₁, hf₁, hf₁l, hf₁r⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints ha₁ hb₁
  obtain ⟨f₂, hf₂, hf₂l, hf₂r⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints ha₂ hb₂
  have hcompat₀ : EqOn f₀ f₁ (Icc a₀ a₁ ∩ Icc a₁ a₂) := by
    intro x hx
    have hx₁ : x = a₁ := le_antisymm hx.1.2 hx.2.1
    rw [hx₁, hf₀r, hf₁l]
  have hmeet₀ : SurjOn f₀ (Icc a₀ a₁ ∩ Icc a₁ a₂) (Icc b₀ b₁ ∩ Icc b₁ b₂) := by
    intro y hy
    have hy₁ : y = b₁ := le_antisymm hy.1.2 hy.2.1
    exact ⟨a₁, ⟨⟨ha₀.le, le_rfl⟩, ⟨le_rfl, ha₁.le⟩⟩, hf₀r.trans hy₁.symm⟩
  obtain ⟨g, hg, hgf₀, hgf₁⟩ := exists_isPLHomeomorphOn_union
    isHPolytope_Icc.isPolyhedron isHPolytope_Icc.isPolyhedron hf₀ hf₁ hcompat₀ hmeet₀
  rw [Icc_union_Icc_eq_Icc ha₀.le ha₁.le, Icc_union_Icc_eq_Icc hb₀.le hb₁.le] at hg
  have hgl : g a₀ = b₀ := (hgf₀ ⟨le_rfl, ha₀.le⟩).trans hf₀l
  have hgr : g a₂ = b₂ := (hgf₁ ⟨ha₁.le, le_rfl⟩).trans hf₁r
  have hcompat₁ : EqOn g f₂ (Icc a₀ a₂ ∩ Icc a₂ a₃) := by
    intro x hx
    have hx₂ : x = a₂ := le_antisymm hx.1.2 hx.2.1
    rw [hx₂, hgr, hf₂l]
  have hmeet₁ : SurjOn g (Icc a₀ a₂ ∩ Icc a₂ a₃) (Icc b₀ b₂ ∩ Icc b₂ b₃) := by
    intro y hy
    have hy₂ : y = b₂ := le_antisymm hy.1.2 hy.2.1
    exact ⟨a₂, ⟨⟨ha₀.le.trans ha₁.le, le_rfl⟩, ⟨le_rfl, ha₂.le⟩⟩,
      hgr.trans hy₂.symm⟩
  obtain ⟨f, hf, hfg, hff₂⟩ := exists_isPLHomeomorphOn_union
    isHPolytope_Icc.isPolyhedron isHPolytope_Icc.isPolyhedron hg hf₂ hcompat₁ hmeet₁
  rw [Icc_union_Icc_eq_Icc (ha₀.le.trans ha₁.le) ha₂.le,
    Icc_union_Icc_eq_Icc (hb₀.le.trans hb₁.le) hb₂.le] at hf
  refine ⟨f, hf, (hfg ⟨le_rfl, ha₀.le.trans ha₁.le⟩).trans hgl,
    (hff₂ ⟨ha₂.le, le_rfl⟩).trans hf₂r, ?_⟩
  exact ((hfg.mono (Icc_subset_Icc ha₀.le le_rfl)).trans hgf₁).image_eq.trans hf₁.image_eq

theorem exists_isPLHomeomorphOn_Icc_map_compact_subset {A B : Set ℝ}
    (hA : IsCompact A) (hAconn : IsConnected A) (hAne : A.Nontrivial) (hAsub : A ⊆ Ioo 0 1)
    (hB : IsCompact B) (hBconn : IsConnected B) (hBne : B.Nontrivial) (hBsub : B ⊆ Ioo 0 1) :
    ∃ f : ℝ → ℝ, IsPLHomeomorphOn f (Icc 0 1) (Icc 0 1) ∧
      f 0 = 0 ∧ f 1 = 1 ∧ f '' A = B := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, A = Icc a b :=
    ⟨_, _, eq_Icc_of_connected_compact hAconn hA⟩
  obtain ⟨c, d, rfl⟩ : ∃ c d : ℝ, B = Icc c d :=
    ⟨_, _, eq_Icc_of_connected_compact hBconn hB⟩
  have hab : a < b := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hAne
    by_contra! hba
    exact hxy (le_antisymm (by linarith [hx.2, hy.1]) (by linarith [hy.2, hx.1]))
  have hcd : c < d := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hBne
    by_contra! hdc
    exact hxy (le_antisymm (by linarith [hx.2, hy.1]) (by linarith [hy.2, hx.1]))
  exact exists_isPLHomeomorphOn_Icc_map_Icc
    (hAsub ⟨le_rfl, hab.le⟩).1 hab (hAsub ⟨hab.le, le_rfl⟩).2
    (hBsub ⟨le_rfl, hcd.le⟩).1 hcd (hBsub ⟨hcd.le, le_rfl⟩).2

end DifferentialGeometry.Topology.PiecewiseLinear
