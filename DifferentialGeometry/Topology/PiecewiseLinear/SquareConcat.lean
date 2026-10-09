/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLHomeomorphOn_squareLowerHalf :
    IsPLHomeomorphOn (fun p : ℝ × ℝ => (p.1, 2 * p.2)) (Icc 0 1 ×ˢ Icc 0 (1 / 2))
      (Icc 0 1 ×ˢ Icc 0 1) := by
  let L : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ := (LinearMap.fst ℝ ℝ ℝ).prod ((2 : ℝ) • LinearMap.snd ℝ ℝ ℝ)
  have hL : ∀ p : ℝ × ℝ, L p = (p.1, 2 * p.2) := fun p => Prod.ext rfl (smul_eq_mul _ _)
  have hpl : IsPiecewiseAffineOn (fun p : ℝ × ℝ => (p.1, 2 * p.2))
      (Icc 0 1 ×ˢ Icc 0 (1 / 2)) :=
    (isPiecewiseAffineOn_of_affine_of_isHPolytope L.toAffineMap
      (isHPolytope_Icc.prod isHPolytope_Icc)).congr fun p _ => (hL p).symm
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron hpl ⟨?_, ?_, ?_⟩
  · rintro p ⟨hp1, hp2⟩
    exact ⟨hp1, by constructor <;> linarith [hp2.1, hp2.2]⟩
  · rintro p - q - hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (by linarith [hpq.2])
  · rintro q ⟨hq1, hq2⟩
    refine ⟨(q.1, q.2 / 2), ⟨hq1, by constructor <;> linarith [hq2.1, hq2.2]⟩, ?_⟩
    exact Prod.ext rfl (by change 2 * (q.2 / 2) = q.2; ring)

theorem isPLHomeomorphOn_squareUpperHalf :
    IsPLHomeomorphOn (fun p : ℝ × ℝ => (p.1, 2 * p.2 - 1)) (Icc 0 1 ×ˢ Icc (1 / 2) 1)
      (Icc 0 1 ×ˢ Icc 0 1) := by
  let L : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ := (LinearMap.fst ℝ ℝ ℝ).prod ((2 : ℝ) • LinearMap.snd ℝ ℝ ℝ)
  let A : ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ :=
    { toFun := fun p => L p + ((0 : ℝ), (-1 : ℝ))
      linear := L
      map_vadd' := fun p v => by
        simp only [vadd_eq_add, map_add]
        abel }
  have hA : ∀ p : ℝ × ℝ, A p = (p.1, 2 * p.2 - 1) := fun p =>
    Prod.ext (add_zero p.1) (by
      change (2 : ℝ) • p.2 + -1 = 2 * p.2 - 1
      rw [smul_eq_mul, sub_eq_add_neg])
  have hpl : IsPiecewiseAffineOn (fun p : ℝ × ℝ => (p.1, 2 * p.2 - 1))
      (Icc 0 1 ×ˢ Icc (1 / 2) 1) :=
    (isPiecewiseAffineOn_of_affine_of_isHPolytope A
      (isHPolytope_Icc.prod isHPolytope_Icc)).congr fun p _ => (hA p).symm
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron hpl ⟨?_, ?_, ?_⟩
  · rintro p ⟨hp1, hp2⟩
    exact ⟨hp1, by constructor <;> linarith [hp2.1, hp2.2]⟩
  · rintro p - q - hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (by linarith [hpq.2])
  · rintro q ⟨hq1, hq2⟩
    refine ⟨(q.1, (q.2 + 1) / 2), ⟨hq1, by constructor <;> linarith [hq2.1, hq2.2]⟩, ?_⟩
    exact Prod.ext rfl (by change 2 * ((q.2 + 1) / 2) - 1 = q.2; ring)

theorem exists_isPLHomeomorphOn_square_concat {σ₁ σ₂ : ℝ × ℝ → E}
    (h₁ : IsPLHomeomorphOn σ₁ (Icc 0 1 ×ˢ Icc 0 1) (σ₁ '' (Icc 0 1 ×ˢ Icc 0 1)))
    (h₂ : IsPLHomeomorphOn σ₂ (Icc 0 1 ×ˢ Icc 0 1) (σ₂ '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hjoin : ∀ t ∈ Icc (0 : ℝ) 1, σ₁ (t, 1) = σ₂ (t, 0))
    (hmeet : σ₁ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ σ₂ '' (Icc 0 1 ×ˢ Icc 0 1) ⊆
      σ₁ '' (Icc 0 1 ×ˢ {1})) :
    ∃ σ : ℝ × ℝ → E,
      IsPLHomeomorphOn σ (Icc 0 1 ×ˢ Icc 0 1)
        (σ₁ '' (Icc 0 1 ×ˢ Icc 0 1) ∪ σ₂ '' (Icc 0 1 ×ˢ Icc 0 1)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, σ (t, 0) = σ₁ (t, 0)) ∧ (∀ t ∈ Icc (0 : ℝ) 1, σ (t, 1) = σ₂ (t, 1)) ∧
      (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2), σ p = σ₁ (p.1, 2 * p.2)) ∧
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (1 / 2 : ℝ) 1, σ p = σ₂ (p.1, 2 * p.2 - 1) := by
  have hf := isPLHomeomorphOn_squareLowerHalf.trans h₁
  have hg := isPLHomeomorphOn_squareUpperHalf.trans h₂
  have hP : IsPolyhedron (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2)) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hQ : IsPolyhedron (Icc (0 : ℝ) 1 ×ˢ Icc (1 / 2 : ℝ) 1) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hPQ : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2) ∩ Icc (0 : ℝ) 1 ×ˢ Icc (1 / 2 : ℝ) 1 =
      Icc (0 : ℝ) 1 ×ˢ {1 / 2} := by
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, -, h4, -⟩
      exact ⟨h1, le_antisymm h3 h4⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by rw [h2]; norm_num, by rw [h2]⟩, h1, by rw [h2], by rw [h2]; norm_num⟩
  have hfg : EqOn (σ₁ ∘ fun p : ℝ × ℝ => (p.1, 2 * p.2))
      (σ₂ ∘ fun p : ℝ × ℝ => (p.1, 2 * p.2 - 1))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2) ∩ Icc (0 : ℝ) 1 ×ˢ Icc (1 / 2 : ℝ) 1) := by
    rw [hPQ]
    rintro p ⟨hp1, hp2⟩
    have hp2' : p.2 = 1 / 2 := hp2
    simp only [Function.comp_apply, hp2']
    norm_num
    exact hjoin p.1 hp1
  have hsurj : SurjOn (σ₁ ∘ fun p : ℝ × ℝ => (p.1, 2 * p.2))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2) ∩ Icc (0 : ℝ) 1 ×ˢ Icc (1 / 2 : ℝ) 1)
      (σ₁ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ σ₂ '' (Icc 0 1 ×ˢ Icc 0 1)) := by
    rw [hPQ]
    intro y hy
    obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hmeet hy
    have hq2' : q.2 = 1 := hq2
    refine ⟨(q.1, 1 / 2), ⟨hq1, rfl⟩, ?_⟩
    simp only [Function.comp_apply]
    norm_num
    rw [← hq2']
  obtain ⟨σ, hσ, hσf, hσg⟩ := exists_isPLHomeomorphOn_union hP hQ hf hg hfg hsurj
  have hcover : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2) ∪ Icc (0 : ℝ) 1 ×ˢ Icc (1 / 2 : ℝ) 1 =
      Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    ext p
    simp only [mem_union, mem_prod, mem_Icc]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, h2, by linarith⟩
      · exact ⟨h1, by linarith, h3⟩
    · rintro ⟨h1, h2, h3⟩
      by_cases h : p.2 ≤ 1 / 2
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, by linarith, h3⟩
  rw [hcover] at hσ
  refine ⟨σ, hσ, fun t ht => ?_, fun t ht => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [hσf ⟨ht, by norm_num, by norm_num⟩]
    simp
  · rw [hσg ⟨ht, by norm_num, by norm_num⟩]
    simp only [Function.comp_apply]
    norm_num
  · exact hσf hp
  · exact hσg hp

end DifferentialGeometry.Topology.PiecewiseLinear
