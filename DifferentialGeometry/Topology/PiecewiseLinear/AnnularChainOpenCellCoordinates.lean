/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainLocalPolyhedral
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Product

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.union {X Y J₀ J₁ J₂ : Set E3}
    (hX : IsPLAnnulusWithEnds X J₀ J₁) (hY : IsPLAnnulusWithEnds Y J₁ J₂)
    (hXY : X ∩ Y = J₁) : IsPLAnnulusWithEnds (X ∪ Y) J₀ J₂ := by
  obtain ⟨J, f, hJ, hf, hJ₀, hJ₁⟩ := hX
  obtain ⟨K, g, hK, hg, hK₀, hK₁⟩ := hY
  have hprodJ (t : ℝ) : IsPolyhedron (J ×ˢ {t}) := by
    rw [← Icc_self]
    exact hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  have hprodK (t : ℝ) : IsPolyhedron (K ×ˢ {t}) := by
    rw [← Icc_self]
    exact hK.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  have hf₁ : IsPLHomeomorphOn (fun x => f (x, 1)) J J₁ := by
    rw [hJ₁]
    exact (hJ.isPolyhedron.isPLHomeomorphOn_prod_const 1).trans
      (hf.restrict (hprodJ 1) (by rintro ⟨x, t⟩ ⟨hx, rfl⟩; exact ⟨hx, by norm_num⟩))
  have hg₀ : IsPLHomeomorphOn (fun x => g (x, 0)) K J₁ := by
    rw [hK₀]
    exact (hK.isPolyhedron.isPLHomeomorphOn_prod_const 0).trans
      (hg.restrict (hprodK 0) (by rintro ⟨x, t⟩ ⟨hx, rfl⟩; exact ⟨hx, by norm_num⟩))
  let τ : E3 → E3 := Function.invFunOn (fun x => g (x, 0)) K ∘ fun x => f (x, 1)
  have hτ : IsPLHomeomorphOn τ J K := hf₁.trans hg₀.symm
  have hseam (x : E3) (hx : x ∈ J) : g (τ x, 0) = f (x, 1) :=
    hg₀.bijOn.invOn_invFunOn.2 (hf₁.bijOn.mapsTo hx)
  obtain ⟨α, hα, hα₀, hα₁⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨β, hβ, hβ₀, hβ₁⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints
    (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  let f' : E3 × ℝ → E3 := f ∘ Prod.map id α
  let g' : E3 × ℝ → E3 := g ∘ Prod.map τ β
  have hf' : IsPLHomeomorphOn f' (J ×ˢ Icc (0 : ℝ) (1 / 2)) X :=
    (hJ.isPolyhedron.isPLHomeomorphOn_id.prodMap hα).trans hf
  have hg' : IsPLHomeomorphOn g' (J ×ˢ Icc (1 / 2 : ℝ) 1) Y :=
    (hτ.prodMap hβ).trans hg
  have hagree : EqOn f' g'
      ((J ×ˢ Icc (0 : ℝ) (1 / 2)) ∩ (J ×ˢ Icc (1 / 2 : ℝ) 1)) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have heq : t = 1 / 2 := le_antisymm hx.2.2 ht.2.1
    subst t
    simpa only [f', g', Function.comp_apply, Prod.map_apply, id_eq, hα₁, hβ₀] using
      (hseam x hx.1).symm
  have hsurj : SurjOn f'
      ((J ×ˢ Icc (0 : ℝ) (1 / 2)) ∩ (J ×ˢ Icc (1 / 2 : ℝ) 1)) (X ∩ Y) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hf₁.bijOn.surjOn (hXY ▸ hy)
    refine ⟨(x, 1 / 2), ⟨⟨hx, by norm_num⟩, ⟨hx, by norm_num⟩⟩, ?_⟩
    simpa only [f', Function.comp_apply, Prod.map_apply, id_eq, hα₁] using hxy
  obtain ⟨ρ, hρ, hleft, hright⟩ := exists_isPLHomeomorphOn_union
    (hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
    (hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron) hf' hg' hagree hsurj
  have hunion : (J ×ˢ Icc (0 : ℝ) (1 / 2)) ∪ (J ×ˢ Icc (1 / 2 : ℝ) 1) =
      J ×ˢ Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro (⟨hx, h₀, h₁⟩ | ⟨hx, h₀, h₁⟩) <;> exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      rcases le_total x.2 (1 / 2) with h | h
      · exact Or.inl ⟨hx, h₀, h⟩
      · exact Or.inr ⟨hx, h, h₁⟩
  refine ⟨J, ρ, hJ, hunion ▸ hρ, ?_, ?_⟩
  · rw [hJ₀]
    apply image_congr
    rintro ⟨x, t⟩ ⟨hx, rfl⟩
    symm
    simpa only [f', Function.comp_apply, Prod.map_apply, id_eq, hα₀] using
      hleft (show (x, (0 : ℝ)) ∈ J ×ˢ Icc (0 : ℝ) (1 / 2) from ⟨hx, by norm_num⟩)
  · rw [hK₁]
    apply Subset.antisymm
    · rintro y ⟨⟨x, t⟩, ⟨hx, rfl⟩, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hτ.bijOn.surjOn hx
      refine ⟨(z, 1), ⟨hz, rfl⟩, ?_⟩
      simpa only [g', Function.comp_apply, Prod.map_apply, hβ₁] using
        hright (show (z, (1 : ℝ)) ∈ J ×ˢ Icc (1 / 2 : ℝ) 1 from ⟨hz, by norm_num⟩)
    · rintro y ⟨⟨x, t⟩, ⟨hx, rfl⟩, rfl⟩
      refine ⟨(τ x, 1), ⟨hτ.bijOn.mapsTo hx, rfl⟩, ?_⟩
      symm
      simpa only [g', Function.comp_apply, Prod.map_apply, hβ₁] using
        hright (show (x, (1 : ℝ)) ∈ J ×ˢ Icc (1 / 2 : ℝ) 1 from ⟨hx, by norm_num⟩)

theorem IsPLAnnulusWithEnds.exists_homeomorph {X J₀ J₁ : Set E3}
    (hX : IsPLAnnulusWithEnds X J₀ J₁) :
    ∃ e : (stdSimplexBoundary 2 × unitInterval) ≃ₜ X,
      range (fun x => (e (x, 0) : E3)) = J₀ ∧
      range (fun x => (e (x, 1) : E3)) = J₁ := by
  obtain ⟨J, ρ, ⟨q, hq⟩, hρ, h₀, h₁⟩ := hX
  let e : (stdSimplexBoundary 2 × unitInterval) ≃ₜ X :=
    (hq.homeomorph.prodCongr (Homeomorph.refl unitInterval)).trans
      ((Homeomorph.Set.prod J (Icc (0 : ℝ) 1)).symm.trans hρ.homeomorph)
  have he (x : stdSimplexBoundary 2) (t : unitInterval) :
      (e (x, t) : E3) = ρ (q x, t) := rfl
  have hrange (t : unitInterval) :
      range (fun x => (e (x, t) : E3)) = ρ '' (J ×ˢ {(t : ℝ)}) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(q x, t), ⟨hq.bijOn.mapsTo x.property, rfl⟩, (he x t).symm⟩
    · rintro ⟨⟨x, s⟩, ⟨hx, rfl⟩, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hq.bijOn.surjOn hx
      exact ⟨⟨z, hz⟩, he ⟨z, hz⟩ t⟩
  exact ⟨e, (hrange 0).trans h₀.symm, (hrange 1).trans h₁.symm⟩

section CompatibleCoordinates

variable {R X : Type*} [TopologicalSpace R] [TopologicalSpace X]

private noncomputable def endRangeHomeomorph {A : Set X}
    (e : (R × unitInterval) ≃ₜ A) (t : unitInterval) :
    R ≃ₜ range (fun x => (e (x, t) : X)) :=
  (IsEmbedding.subtypeVal.comp (e.isEmbedding.comp (isEmbedding_prodMkLeft t))).toHomeomorph

private theorem exists_homeomorph_sequence (τ : ℤ → (R ≃ₜ R)) :
    ∃ q : ℤ → (R ≃ₜ R), ∀ i, q (i + 1) = (q i).trans (τ i) := by
  let q : ℤ → (R ≃ₜ R) := fun i =>
    i.inductionOn' 0 (Homeomorph.refl R)
      (fun j _ e => e.trans (τ j)) (fun j _ e => e.trans (τ (j - 1)).symm)
  refine ⟨q, fun i => ?_⟩
  by_cases hi : 0 ≤ i
  · exact Int.inductionOn'_add_one hi
  · have hi' : i + 1 ≤ 0 := by omega
    have hrec : q i = (q (i + 1)).trans (τ i).symm := by
      have h := Int.inductionOn'_sub_one (motive := fun _ : ℤ => R ≃ₜ R)
        (zero := Homeomorph.refl R)
        (succ := fun j _ e => e.trans (τ j))
        (pred := fun j _ e => e.trans (τ (j - 1)).symm) hi'
      simpa only [q, add_sub_cancel_right] using h
    rw [hrec]
    ext x
    simp

theorem exists_compatible_annulus_homeomorphs {A : ℤ → Set X}
    (e : ∀ i, (R × unitInterval) ≃ₜ A i)
    (hseam : ∀ i, range (fun x => (e i (x, 1) : X)) =
      range (fun x => (e (i + 1) (x, 0) : X))) :
    ∃ e' : ∀ i, (R × unitInterval) ≃ₜ A i,
      (∀ i x, (e' i (x, 1) : X) = e' (i + 1) (x, 0)) ∧
      ∀ i t, range (fun x => (e' i (x, t) : X)) = range (fun x => (e i (x, t) : X)) := by
  let τ : ℤ → (R ≃ₜ R) := fun i =>
    (endRangeHomeomorph (e i) 1).trans
      ((Homeomorph.setCongr (hseam i)).trans (endRangeHomeomorph (e (i + 1)) 0).symm)
  have hτ (i : ℤ) (x : R) : (e (i + 1) (τ i x, 0) : X) = e i (x, 1) := by
    let y := endRangeHomeomorph (e i) 1 x
    have h := (endRangeHomeomorph (e (i + 1)) 0).apply_symm_apply
      ((Homeomorph.setCongr (hseam i)) y)
    exact congrArg Subtype.val h
  obtain ⟨q, hq⟩ := exists_homeomorph_sequence τ
  let e' : ∀ i, (R × unitInterval) ≃ₜ A i := fun i =>
    ((q i).prodCongr (Homeomorph.refl unitInterval)).trans (e i)
  refine ⟨e', ?_, ?_⟩
  · intro i x
    change (e i (q i x, 1) : X) = e (i + 1) (q (i + 1) x, 0)
    rw [hq]
    exact (hτ i (q i x)).symm
  · intro i t
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨q i x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨(q i).symm x, ?_⟩
      change (e i (q i ((q i).symm x), t) : X) = e i (x, t)
      rw [(q i).apply_symm_apply]

end CompatibleCoordinates

end DifferentialGeometry.Topology.PiecewiseLinear
