/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.LateralAnnulusLevels

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_prism_stack {P : Set E} (hP : IsPolyhedron P)
    {Φ Ψ : E × ℝ → F} {A B : Set F}
    (hΦ : IsPLHomeomorphOn Φ (P ×ˢ Icc (0 : ℝ) 1) A)
    (hΨ : IsPLHomeomorphOn Ψ (P ×ˢ Icc (0 : ℝ) 1) B)
    (hΦΨ : ∀ x ∈ P, Φ (x, 1) = Ψ (x, 0))
    (hAB : A ∩ B = Φ '' (P ×ˢ ({1} : Set ℝ))) :
    ∃ Θ : E × ℝ → F, IsPLHomeomorphOn Θ (P ×ˢ Icc (0 : ℝ) 1) (A ∪ B) ∧
      (∀ x ∈ P, Θ (x, 0) = Φ (x, 0)) ∧ (∀ x ∈ P, Θ (x, 1) = Ψ (x, 1)) ∧
      ∀ X ⊆ P, Θ '' (X ×ˢ Icc (0 : ℝ) 1) =
        Φ '' (X ×ˢ Icc (0 : ℝ) 1) ∪ Ψ '' (X ×ˢ Icc (0 : ℝ) 1) := by
  have hs₀ : IsPLHomeomorphOn (fun t : ℝ => 2 * t + 0) (Icc 0 (1 / 2)) (Icc 0 1) :=
    isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num) (by norm_num)
  have hs₁ : IsPLHomeomorphOn (fun t : ℝ => 2 * t + -1) (Icc (1 / 2) 1) (Icc 0 1) :=
    isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num) (by norm_num)
  have hf := (hP.isPLHomeomorphOn_id.prodMap hs₀).trans hΦ
  have hg := (hP.isPLHomeomorphOn_id.prodMap hs₁).trans hΨ
  obtain ⟨Θ, hΘ, hΘf, hΘg⟩ := exists_isPLHomeomorphOn_union
    (hP.prod isHPolytope_Icc.isPolyhedron) (hP.prod isHPolytope_Icc.isPolyhedron) hf hg
    (by
      rintro ⟨x, t⟩ ⟨⟨hx, -, ht1⟩, -, ht2, -⟩
      obtain rfl : t = 1 / 2 := le_antisymm ht1 ht2
      simp only [Function.comp_apply, Prod.map_apply, id_eq]
      rw [show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num,
        show (2 : ℝ) * (1 / 2) + -1 = 0 by norm_num]
      exact hΦΨ x hx)
    (by
      rintro y ⟨hyA, hyB⟩
      have hy : y ∈ Φ '' (P ×ˢ ({1} : Set ℝ)) := hAB ▸ ⟨hyA, hyB⟩
      obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hy
      obtain rfl : t = 1 := ht
      refine ⟨(x, 1 / 2), ⟨⟨hx, by norm_num, le_rfl⟩, hx, le_rfl, by norm_num⟩, ?_⟩
      simp only [Function.comp_apply, Prod.map_apply, id_eq]
      rw [show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num])
  have hPQ : P ×ˢ Icc (0 : ℝ) (1 / 2) ∪ P ×ˢ Icc (1 / 2 : ℝ) 1 =
      P ×ˢ Icc (0 : ℝ) 1 := by
    rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  rw [hPQ] at hΘ
  refine ⟨Θ, hΘ, fun x hx => ?_, fun x hx => ?_, fun X hX => ?_⟩
  · rw [hΘf ⟨hx, le_rfl, by norm_num⟩]
    simp only [Function.comp_apply, Prod.map_apply, id_eq, mul_zero, add_zero]
  · rw [hΘg ⟨hx, by norm_num, le_rfl⟩]
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    rw [show (2 : ℝ) * 1 + -1 = 1 by norm_num]
  · have hXs : X ×ˢ Icc (0 : ℝ) 1 =
        X ×ˢ Icc (0 : ℝ) (1 / 2) ∪ X ×ˢ Icc (1 / 2 : ℝ) 1 := by
      rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
    conv_lhs => rw [hXs, image_union]
    rw [(hΘf.mono (prod_mono hX subset_rfl)).image_eq,
      (hΘg.mono (prod_mono hX subset_rfl)).image_eq]
    simp only [image_comp, prodMap_image_prod, image_id, hs₀.image_eq, hs₁.image_eq]

theorem exists_isPLHomeomorphOn_prism_chain {P : Set E} (hP : IsPolyhedron P)
    {a : E} (ha : a ∈ P) {C D J : ℕ → Set F} {z : ℕ → F} {g₀ : E → F}
    (hg₀ : IsPLHomeomorphOn g₀ P (D 0)) (hg₀a : g₀ a = z 0) (m : ℕ)
    (hproduce : ∀ k ≤ m, ∀ g : E → F, IsPLHomeomorphOn g P (D k) → g a = z k →
      ∃ G : E × ℝ → F, IsPLHomeomorphOn G (P ×ˢ Icc (0 : ℝ) 1) (C k) ∧
        (∀ x ∈ P, G (x, 0) = g x) ∧ G '' (P ×ˢ ({1} : Set ℝ)) = D (k + 1) ∧
        G (a, 1) = z (k + 1) ∧ G '' ({a} ×ˢ Icc (0 : ℝ) 1) = J k)
    (hadj : ∀ k < m, C k ∩ C (k + 1) = D (k + 1))
    (hfar : ∀ i k, i + 1 < k → k ≤ m → Disjoint (C i) (C k)) :
    ∃ Φ : E × ℝ → F, IsPLHomeomorphOn Φ (P ×ˢ Icc (0 : ℝ) 1) (⋃ k ≤ m, C k) ∧
      (∀ x ∈ P, Φ (x, 0) = g₀ x) ∧ Φ '' (P ×ˢ ({1} : Set ℝ)) = D (m + 1) ∧
      Φ (a, 1) = z (m + 1) ∧ Φ '' ({a} ×ˢ Icc (0 : ℝ) 1) = ⋃ k ≤ m, J k := by
  induction m with
  | zero =>
      obtain ⟨G, hG, hG0, hG1, hGa, hGaxis⟩ := hproduce 0 le_rfl g₀ hg₀ hg₀a
      refine ⟨G, ?_, hG0, hG1, hGa, ?_⟩
      · simpa only [Nat.le_zero, iUnion_iUnion_eq_left] using hG
      · simpa only [Nat.le_zero, iUnion_iUnion_eq_left] using hGaxis
  | succ m ih =>
      obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦa, hΦaxis⟩ := ih
        (fun k hk => hproduce k (hk.trans (Nat.le_succ m)))
        (fun k hk => hadj k (hk.trans (Nat.lt_succ_self m)))
        (fun i k hik hk => hfar i k hik (hk.trans (Nat.le_succ m)))
      have htop : IsPLHomeomorphOn Φ (P ×ˢ ({1} : Set ℝ)) (D (m + 1)) := by
        have h := hΦ.restrict (by
            rw [← Icc_self (1 : ℝ)]
            exact hP.prod isHPolytope_Icc.isPolyhedron)
          (prod_mono subset_rfl (singleton_subset_iff.mpr ⟨zero_le_one, le_rfl⟩))
        rwa [hΦ1] at h
      have hcap := (hP.isPLHomeomorphOn_prod_const 1).trans htop
      obtain ⟨Ψ, hΨ, hΨ0, hΨ1, hΨa, hΨaxis⟩ :=
        hproduce (m + 1) le_rfl (fun x => Φ (x, 1)) hcap hΦa
      have hmeet : (⋃ k ≤ m, C k) ∩ C (m + 1) = Φ '' (P ×ˢ ({1} : Set ℝ)) := by
        rw [hΦ1, ← hadj m (Nat.lt_succ_self m)]
        refine Subset.antisymm ?_ ?_
        · rintro x ⟨hx, hx'⟩
          obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
          rcases hk.lt_or_eq with hk | rfl
          · exact False.elim (disjoint_left.mp (hfar k (m + 1) (by omega) le_rfl) hxk hx')
          · exact ⟨hxk, hx'⟩
        · rintro x ⟨hx, hx'⟩
          exact ⟨mem_iUnion₂.mpr ⟨m, le_rfl, hx⟩, hx'⟩
      obtain ⟨Θ, hΘ, hΘ0, hΘ1, hΘaxis⟩ := exists_isPLHomeomorphOn_prism_stack hP hΦ hΨ
        (fun x hx => (hΨ0 x hx).symm) hmeet
      have htopEq : EqOn Θ Ψ (P ×ˢ ({1} : Set ℝ)) := by
        rintro ⟨x, t⟩ ⟨hx, ht⟩
        obtain rfl : t = 1 := ht
        exact hΘ1 x hx
      refine ⟨Θ, ?_, fun x hx => (hΘ0 x hx).trans (hΦ0 x hx),
        htopEq.image_eq.trans hΨ1, (hΘ1 a ha).trans hΨa, ?_⟩
      · rwa [biUnion_le_succ]
      · rw [hΘaxis {a} (singleton_subset_iff.mpr ha), hΦaxis, hΨaxis, biUnion_le_succ]

theorem exists_cylindricalDiagram_of_prism_pair_marked {P : Set E} (hP : IsPolyhedron P)
    {Φ Ψ : E × ℝ → F} {A B : Set F}
    (hΦ : IsPLHomeomorphOn Φ (P ×ˢ Icc (0 : ℝ) 1) A)
    (hΨ : IsPLHomeomorphOn Ψ (P ×ˢ Icc (0 : ℝ) 1) B)
    (hjoin : ∀ x ∈ P, Φ (x, 1) = Ψ (x, 0))
    (hends : Ψ '' (P ×ˢ ({1} : Set ℝ)) = Φ '' (P ×ˢ ({0} : Set ℝ)))
    (hmeet : A ∩ B = Φ '' (P ×ˢ ({0} : Set ℝ)) ∪ Φ '' (P ×ˢ ({1} : Set ℝ))) :
    ∃ φ : E × ℝ → F, IsCylindricalDiagram φ P (A ∪ B) ∧
      (∀ x ∈ P, φ (x, 0) = Φ (x, 0)) ∧ (∀ x ∈ P, φ (x, 1) = Ψ (x, 1)) ∧
      ∀ X ⊆ P, φ '' (X ×ˢ Icc (0 : ℝ) 1) =
        Φ '' (X ×ˢ Icc (0 : ℝ) 1) ∪ Ψ '' (X ×ˢ Icc (0 : ℝ) 1) := by
  classical
  have hs₀ : IsPLHomeomorphOn (fun t : ℝ => 2 * t + 0) (Icc 0 (1 / 2)) (Icc 0 1) :=
    isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num) (by norm_num)
  have hs₁ : IsPLHomeomorphOn (fun t : ℝ => 2 * t + -1) (Icc (1 / 2) 1) (Icc 0 1) :=
    isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num) (by norm_num)
  let f := Φ ∘ Prod.map id (fun t : ℝ => 2 * t + 0)
  let g := Ψ ∘ Prod.map id (fun t : ℝ => 2 * t + -1)
  have hf : IsPLHomeomorphOn f (P ×ˢ Icc (0 : ℝ) (1 / 2)) A :=
    (hP.isPLHomeomorphOn_id.prodMap hs₀).trans hΦ
  have hg : IsPLHomeomorphOn g (P ×ˢ Icc (1 / 2 : ℝ) 1) B :=
    (hP.isPLHomeomorphOn_id.prodMap hs₁).trans hΨ
  have hf0 : f '' (P ×ˢ ({0} : Set ℝ)) = Φ '' (P ×ˢ ({0} : Set ℝ)) := by
    simp only [f, image_comp, prodMap_image_prod, image_id, image_singleton, mul_zero, add_zero]
  have hgm : g '' (P ×ˢ ({1} : Set ℝ)) = Φ '' (P ×ˢ ({0} : Set ℝ)) := by
    simpa only [g, image_comp, prodMap_image_prod, image_id, image_singleton,
      show (2 : ℝ) * 1 + -1 = 1 by norm_num] using hends
  have hfm : f '' (P ×ˢ ({1 / 2} : Set ℝ)) = Φ '' (P ×ˢ ({1} : Set ℝ)) := by
    simp only [f, image_comp, prodMap_image_prod, image_id, image_singleton,
      show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num]
  have hfg : EqOn f g (P ×ˢ ({1 / 2} : Set ℝ)) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    obtain rfl : t = 1 / 2 := ht
    simpa only [f, g, Function.comp_apply, Prod.map_apply, id_eq,
      show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num,
      show (2 : ℝ) * (1 / 2) + -1 = 0 by norm_num] using hjoin x hx
  let φ := (P ×ˢ Icc (0 : ℝ) (1 / 2)).piecewise f g
  have hφf : EqOn φ f (P ×ˢ Icc (0 : ℝ) (1 / 2)) :=
    (P ×ˢ Icc (0 : ℝ) (1 / 2)).piecewise_eqOn f g
  have hφg : EqOn φ g (P ×ˢ Icc (1 / 2 : ℝ) 1) := by
    intro x hx
    by_cases hx0 : x ∈ P ×ˢ Icc (0 : ℝ) (1 / 2)
    · exact (hφf hx0).trans (hfg ⟨hx.1, le_antisymm hx0.2.2 hx.2.1⟩)
    · exact (P ×ˢ Icc (0 : ℝ) (1 / 2)).piecewise_eq_of_notMem f g hx0
  refine ⟨φ, isCylindricalDiagram_piecewise hP hf hg hf0 hgm hfm hfg hmeet,
    fun x hx => ?_, fun x hx => ?_, fun X hX => ?_⟩
  · rw [hφf ⟨hx, le_rfl, by norm_num⟩]
    simp only [f, Function.comp_apply, Prod.map_apply, id_eq, mul_zero, add_zero]
  · rw [hφg ⟨hx, by norm_num, le_rfl⟩]
    simp only [g, Function.comp_apply, Prod.map_apply, id_eq,
      show (2 : ℝ) * 1 + -1 = 1 by norm_num]
  · have hXs : X ×ˢ Icc (0 : ℝ) 1 =
        X ×ˢ Icc (0 : ℝ) (1 / 2) ∪ X ×ˢ Icc (1 / 2 : ℝ) 1 := by
      rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
    conv_lhs => rw [hXs, image_union]
    rw [(hφf.mono (prod_mono hX subset_rfl)).image_eq,
      (hφg.mono (prod_mono hX subset_rfl)).image_eq]
    simp only [f, g, image_comp, prodMap_image_prod, image_id, hs₀.image_eq, hs₁.image_eq]

theorem exists_cylindricalDiagram_of_prism_cycle_marked {P : Set E} (hP : IsPolyhedron P)
    {a : E} (ha : a ∈ P) {C D J : ℕ → Set F} {z : ℕ → F} {g₀ : E → F}
    (hg₀ : IsPLHomeomorphOn g₀ P (D 0)) (hg₀a : g₀ a = z 0) (m : ℕ)
    (hproduce : ∀ k ≤ m + 1, ∀ g : E → F, IsPLHomeomorphOn g P (D k) → g a = z k →
      ∃ G : E × ℝ → F, IsPLHomeomorphOn G (P ×ˢ Icc (0 : ℝ) 1) (C k) ∧
        (∀ x ∈ P, G (x, 0) = g x) ∧ G '' (P ×ˢ ({1} : Set ℝ)) = D (k + 1) ∧
        G (a, 1) = z (k + 1) ∧ G '' ({a} ×ˢ Icc (0 : ℝ) 1) = J k)
    (hadj : ∀ k < m, C k ∩ C (k + 1) = D (k + 1))
    (hfar : ∀ i k, i + 1 < k → k ≤ m → Disjoint (C i) (C k))
    (hfinal : (⋃ k ≤ m, C k) ∩ C (m + 1) = D 0 ∪ D (m + 1))
    (hDclose : D (m + 2) = D 0) (hzclose : z (m + 2) = z 0) :
    ∃ φ : E × ℝ → F, IsCylindricalDiagram φ P (⋃ k ≤ m + 1, C k) ∧
      φ (a, 0) = φ (a, 1) ∧ φ '' ({a} ×ˢ Icc (0 : ℝ) 1) = ⋃ k ≤ m + 1, J k := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦa, hΦaxis⟩ := exists_isPLHomeomorphOn_prism_chain
    hP ha hg₀ hg₀a m (fun k hk => hproduce k (hk.trans (Nat.le_succ m))) hadj hfar
  have htop : IsPLHomeomorphOn Φ (P ×ˢ ({1} : Set ℝ)) (D (m + 1)) := by
    have h := hΦ.restrict (by
        rw [← Icc_self (1 : ℝ)]
        exact hP.prod isHPolytope_Icc.isPolyhedron)
      (prod_mono subset_rfl (singleton_subset_iff.mpr ⟨zero_le_one, le_rfl⟩))
    rwa [hΦ1] at h
  have hcap := (hP.isPLHomeomorphOn_prod_const 1).trans htop
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1, hΨa, hΨaxis⟩ :=
    hproduce (m + 1) le_rfl (fun x => Φ (x, 1)) hcap hΦa
  have hbot : Φ '' (P ×ˢ ({0} : Set ℝ)) = D 0 := by
    rw [← (hP.isPLHomeomorphOn_prod_const 0).image_eq, image_image]
    exact (show EqOn (Φ ∘ fun x => (x, (0 : ℝ))) g₀ P from hΦ0).image_eq.trans hg₀.image_eq
  obtain ⟨φ, hφ, hφ0, hφ1, hφaxis⟩ := exists_cylindricalDiagram_of_prism_pair_marked
    hP hΦ hΨ (fun x hx => (hΨ0 x hx).symm)
    (by rw [hΨ1, hDclose, hbot]) (by rw [hbot, hΦ1]; exact hfinal)
  refine ⟨φ, ?_, ?_, ?_⟩
  · rwa [biUnion_le_succ]
  · rw [hφ0 a ha, hφ1 a ha, hΦ0 a ha, hΨa, hzclose, hg₀a]
  · rw [hφaxis {a} (singleton_subset_iff.mpr ha), hΦaxis, hΨaxis, biUnion_le_succ]

end DifferentialGeometry.Topology.PiecewiseLinear
