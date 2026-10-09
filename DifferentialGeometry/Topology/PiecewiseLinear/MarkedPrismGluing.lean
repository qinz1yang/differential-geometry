/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem exists_prism_cap_transition
    {P : Set E} (hP : IsPolyhedron P) {A B : Set F} {f g : E × ℝ → F}
    (hf : IsPLHomeomorphOn f (P ×ˢ Icc (0 : ℝ) 1) A)
    (hg : IsPLHomeomorphOn g (P ×ˢ Icc (0 : ℝ) 1) B)
    (hcap : f '' (P ×ˢ {(1 : ℝ)}) = g '' (P ×ˢ {(0 : ℝ)}))
    {p : E} (hp : p ∈ P) (hmark : f (p, 1) = g (p, 0)) :
    ∃ τ : E → E, IsPLHomeomorphOn τ P P ∧ τ p = p ∧
      ∀ x ∈ P, g (τ x, 0) = f (x, 1) := by
  have hprod (t : ℝ) : IsPolyhedron (P ×ˢ {t}) := by
    rw [← Icc_self]
    exact hP.prod isHPolytope_Icc.isPolyhedron
  have hf₁ : IsPLHomeomorphOn (fun x => f (x, 1)) P (f '' (P ×ˢ {(1 : ℝ)})) :=
    (hP.isPLHomeomorphOn_prod_const 1).trans
      (hf.restrict (hprod 1) (by rintro ⟨x, t⟩ ⟨hx, rfl⟩; exact ⟨hx, by norm_num⟩))
  have hg₀ : IsPLHomeomorphOn (fun x => g (x, 0)) P (f '' (P ×ˢ {(1 : ℝ)})) := by
    rw [hcap]
    exact (hP.isPLHomeomorphOn_prod_const 0).trans
      (hg.restrict (hprod 0) (by rintro ⟨x, t⟩ ⟨hx, rfl⟩; exact ⟨hx, by norm_num⟩))
  let τ := Function.invFunOn (fun x => g (x, 0)) P ∘ fun x => f (x, 1)
  have hτ : IsPLHomeomorphOn τ P P := hf₁.trans hg₀.symm
  have hseam (x : E) (hx : x ∈ P) : g (τ x, 0) = f (x, 1) :=
    hg₀.bijOn.invOn_invFunOn.2 (hf₁.bijOn.mapsTo hx)
  refine ⟨τ, hτ, ?_, hseam⟩
  exact hg₀.bijOn.injOn (hτ.bijOn.mapsTo hp) hp ((hseam p hp).trans hmark)

private theorem exists_marked_half_prisms
    {P : Set E} (hP : IsPolyhedron P) {A B : Set F} {f g : E × ℝ → F}
    (hf : IsPLHomeomorphOn f (P ×ˢ Icc (0 : ℝ) 1) A)
    (hg : IsPLHomeomorphOn g (P ×ˢ Icc (0 : ℝ) 1) B)
    (hcap : f '' (P ×ˢ {(1 : ℝ)}) = g '' (P ×ˢ {(0 : ℝ)}))
    {p : E} (hp : p ∈ P) (hmark : f (p, 1) = g (p, 0)) :
    ∃ f' g' : E × ℝ → F,
      IsPLHomeomorphOn f' (P ×ˢ Icc (0 : ℝ) (1 / 2)) A ∧
      IsPLHomeomorphOn g' (P ×ˢ Icc (1 / 2 : ℝ) 1) B ∧
      (∀ x ∈ P, f' (x, 0) = f (x, 0)) ∧
      g' '' (P ×ˢ {(1 : ℝ)}) = g '' (P ×ˢ {(1 : ℝ)}) ∧
      (∀ x ∈ P, f' (x, 1 / 2) = f (x, 1)) ∧
      EqOn f' g' (P ×ˢ {(1 / 2 : ℝ)}) ∧
      g' (p, 1) = g (p, 1) ∧
      f' '' ({p} ×ˢ Icc (0 : ℝ) (1 / 2)) = f '' ({p} ×ˢ Icc (0 : ℝ) 1) ∧
      g' '' ({p} ×ˢ Icc (1 / 2 : ℝ) 1) = g '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨τ, hτ, hτp, hseam⟩ := exists_prism_cap_transition hP hf hg hcap hp hmark
  obtain ⟨α, hα, hα₀, hα₁⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨β, hβ, hβ₀, hβ₁⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints
    (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  let f' : E × ℝ → F := f ∘ Prod.map id α
  let g' : E × ℝ → F := g ∘ Prod.map τ β
  refine ⟨f', g', (hP.isPLHomeomorphOn_id.prodMap hα).trans hf,
    (hτ.prodMap hβ).trans hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [f', Function.comp_apply, Prod.map_apply, id_eq, hα₀]
  · ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, rfl⟩, rfl⟩
      exact ⟨(τ x, 1), ⟨hτ.bijOn.mapsTo hx, rfl⟩,
        by simp only [g', Function.comp_apply, Prod.map_apply, hβ₁]⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, rfl⟩, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hτ.bijOn.surjOn hx
      exact ⟨(z, 1), ⟨hz, rfl⟩,
        by simp only [g', Function.comp_apply, Prod.map_apply, hβ₁]⟩
  · intro x hx
    simp only [f', Function.comp_apply, Prod.map_apply, id_eq, hα₁]
  · rintro ⟨x, t⟩ ⟨hx, rfl⟩
    simpa only [f', g', Function.comp_apply, Prod.map_apply, id_eq, hα₁, hβ₀] using
      (hseam x hx).symm
  · simp only [g', Function.comp_apply, Prod.map_apply, hτp, hβ₁]
  · change (f ∘ Prod.map id α) '' _ = _
    rw [image_comp, prodMap_image_prod, image_id, hα.image_eq]
  · change (g ∘ Prod.map τ β) '' _ = _
    rw [image_comp, prodMap_image_prod, image_singleton, hτp, hβ.image_eq]

theorem exists_isPLHomeomorphOn_prism_union_of_marked_cap
    {P : Set E} (hP : IsPolyhedron P) {A B : Set F} {f g : E × ℝ → F}
    (hf : IsPLHomeomorphOn f (P ×ˢ Icc (0 : ℝ) 1) A)
    (hg : IsPLHomeomorphOn g (P ×ˢ Icc (0 : ℝ) 1) B)
    (hcap : f '' (P ×ˢ {(1 : ℝ)}) = g '' (P ×ˢ {(0 : ℝ)}))
    (hinter : A ∩ B = f '' (P ×ˢ {(1 : ℝ)}))
    {p : E} (hp : p ∈ P) (hmark : f (p, 1) = g (p, 0)) :
    ∃ ρ : E × ℝ → F, IsPLHomeomorphOn ρ (P ×ˢ Icc (0 : ℝ) 1) (A ∪ B) ∧
      (∀ x ∈ P, ρ (x, 0) = f (x, 0)) ∧
      ρ '' (P ×ˢ {(1 : ℝ)}) = g '' (P ×ˢ {(1 : ℝ)}) ∧
      ρ (p, 1) = g (p, 1) ∧
      ρ '' ({p} ×ˢ Icc (0 : ℝ) 1) =
        f '' ({p} ×ˢ Icc (0 : ℝ) 1) ∪ g '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨f', g', hf', hg', hzero, hone, hmid, hseam, hg'p, haxisf, haxisg⟩ :=
    exists_marked_half_prisms hP hf hg hcap hp hmark
  have hagree : EqOn f' g'
      ((P ×ˢ Icc (0 : ℝ) (1 / 2)) ∩ (P ×ˢ Icc (1 / 2 : ℝ) 1)) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact hseam ⟨hx.1, le_antisymm hx.2.2 ht.2.1⟩
  have hsurj : SurjOn f'
      ((P ×ˢ Icc (0 : ℝ) (1 / 2)) ∩ (P ×ˢ Icc (1 / 2 : ℝ) 1)) (A ∩ B) := by
    intro y hy
    obtain ⟨⟨x, t⟩, ⟨hx, rfl⟩, hxy⟩ := hinter ▸ hy
    exact ⟨(x, 1 / 2), ⟨⟨hx, by norm_num⟩, ⟨hx, by norm_num⟩⟩,
      (hmid x hx).trans hxy⟩
  obtain ⟨ρ, hρ, hleft, hright⟩ := exists_isPLHomeomorphOn_union
    (hP.prod isHPolytope_Icc.isPolyhedron) (hP.prod isHPolytope_Icc.isPolyhedron)
    hf' hg' hagree hsurj
  have hunion (Q : Set E) : (Q ×ˢ Icc (0 : ℝ) (1 / 2)) ∪
      (Q ×ˢ Icc (1 / 2 : ℝ) 1) = Q ×ˢ Icc (0 : ℝ) 1 := by
    rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  refine ⟨ρ, hunion P ▸ hρ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hleft ⟨hx, by norm_num⟩).trans (hzero x hx)
  · have htop : P ×ˢ {(1 : ℝ)} ⊆ P ×ˢ Icc (1 / 2 : ℝ) 1 := by
      rintro ⟨x, t⟩ ⟨hx, rfl⟩
      exact ⟨hx, by norm_num⟩
    exact (hright.mono htop).image_eq.trans hone
  · exact (hright ⟨hp, by norm_num⟩).trans hg'p
  · conv_lhs => rw [← hunion {p}, image_union]
    have hleft' := hleft.mono (prod_mono (singleton_subset_iff.mpr hp) Subset.rfl)
    have hright' := hright.mono (prod_mono (singleton_subset_iff.mpr hp) Subset.rfl)
    rw [hleft'.image_eq, hright'.image_eq, haxisf, haxisg]

theorem exists_cylindricalDiagram_of_marked_prism_pair
    {P : Set E} (hP : IsPolyhedron P) {A B : Set F} {f g : E × ℝ → F}
    (hf : IsPLHomeomorphOn f (P ×ˢ Icc (0 : ℝ) 1) A)
    (hg : IsPLHomeomorphOn g (P ×ˢ Icc (0 : ℝ) 1) B)
    (hcap : f '' (P ×ˢ {(1 : ℝ)}) = g '' (P ×ˢ {(0 : ℝ)}))
    (hclose : g '' (P ×ˢ {(1 : ℝ)}) = f '' (P ×ˢ {(0 : ℝ)}))
    (hinter : A ∩ B = f '' (P ×ˢ {(0 : ℝ)}) ∪ f '' (P ×ˢ {(1 : ℝ)}))
    {p : E} (hp : p ∈ P) (hmark : f (p, 1) = g (p, 0))
    (hclosed : g (p, 1) = f (p, 0)) :
    ∃ ρ : E × ℝ → F, IsCylindricalDiagram ρ P (A ∪ B) ∧
      ρ (p, 0) = ρ (p, 1) ∧
      ρ '' ({p} ×ˢ Icc (0 : ℝ) 1) =
        f '' ({p} ×ˢ Icc (0 : ℝ) 1) ∪ g '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨f', g', hf', hg', hzero, hone, hmid, hseam, hg'p, haxisf, haxisg⟩ :=
    exists_marked_half_prisms hP hf hg hcap hp hmark
  have hzero' : f' '' (P ×ˢ {(0 : ℝ)}) = f '' (P ×ˢ {(0 : ℝ)}) := by
    apply image_congr
    rintro ⟨x, t⟩ ⟨hx, rfl⟩
    exact hzero x hx
  have hmid' : f' '' (P ×ˢ {(1 / 2 : ℝ)}) = f '' (P ×ˢ {(1 : ℝ)}) := by
    have h₁ : (fun x : E => (x, (1 / 2 : ℝ))) '' P = P ×ˢ {(1 / 2 : ℝ)} :=
      (hP.isPLHomeomorphOn_prod_const (1 / 2)).image_eq
    have h₂ : (fun x : E => (x, (1 : ℝ))) '' P = P ×ˢ {(1 : ℝ)} :=
      (hP.isPLHomeomorphOn_prod_const 1).image_eq
    rw [← h₁, ← h₂, image_image, image_image]
    exact (show EqOn (fun x => f' (x, 1 / 2)) (fun x => f (x, 1)) P from hmid).image_eq
  let ρ := (P ×ˢ Icc (0 : ℝ) (1 / 2)).piecewise f' g'
  have hleft : EqOn ρ f' (P ×ˢ Icc (0 : ℝ) (1 / 2)) :=
    (P ×ˢ Icc (0 : ℝ) (1 / 2)).piecewise_eqOn f' g'
  have hright : EqOn ρ g' (P ×ˢ Icc (1 / 2 : ℝ) 1) := by
    intro x hx
    by_cases hx' : x ∈ P ×ˢ Icc (0 : ℝ) (1 / 2)
    · exact (hleft hx').trans (hseam ⟨hx.1, le_antisymm hx'.2.2 hx.2.1⟩)
    · exact (P ×ˢ Icc (0 : ℝ) (1 / 2)).piecewise_eq_of_notMem f' g' hx'
  refine ⟨ρ, isCylindricalDiagram_piecewise hP hf' hg' hzero'
    (hone.trans hclose) hmid' hseam hinter, ?_, ?_⟩
  · exact ((hleft ⟨hp, by norm_num⟩).trans (hzero p hp)).trans
      (((hright ⟨hp, by norm_num⟩).trans hg'p).trans hclosed).symm
  · have hunion : ({p} ×ˢ Icc (0 : ℝ) (1 / 2)) ∪
        ({p} ×ˢ Icc (1 / 2 : ℝ) 1) = {p} ×ˢ Icc (0 : ℝ) 1 := by
      rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
    conv_lhs => rw [← hunion, image_union]
    have hleft' := hleft.mono (prod_mono (singleton_subset_iff.mpr hp) Subset.rfl)
    have hright' := hright.mono (prod_mono (singleton_subset_iff.mpr hp) Subset.rfl)
    rw [hleft'.image_eq, hright'.image_eq, haxisf, haxisg]

end DifferentialGeometry.Topology.PiecewiseLinear
