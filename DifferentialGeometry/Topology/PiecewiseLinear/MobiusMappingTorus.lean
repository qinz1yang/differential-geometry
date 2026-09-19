/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePrismComparison
import DifferentialGeometry.Topology.PiecewiseLinear.CircleReflection
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusSquareMap

/-! Embedded Moebius bands in PL mapping tori with reversing circle monodromy. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPiecewiseAffineOn_square_flip_of_not_isPLCirclePositive
    {S : Set E} (hS : IsPLSphere 1 S) {T : Set F} {f : E × ℝ → F}
    (hf : IsCylindricalDiagram f S T) {v : E → E} (hv : IsPLHomeomorphOn v S S)
    (hnv : ¬ IsPLCirclePositive S v) (hfv : ∀ x ∈ S, f (x, 1) = f (v x, 0)) :
    ∃ g : ℝ × ℝ → F, IsPiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      g '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ T ∧
      (∀ s ∈ Icc (0 : ℝ) 1, g (s, 1) = g (1 - s, 0)) ∧
      ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ∀ y ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g x = g y →
          x = y ∨ (x.2 = 0 ∧ y.2 = 1 ∧ x.1 = 1 - y.1) ∨
            (x.2 = 1 ∧ y.2 = 0 ∧ x.1 = 1 - y.1) := by
  obtain ⟨r, A, γ, hr, hnr, -, hγ, hAS, hrflip⟩ :=
    exists_isPLHomeomorphOn_reflection_arc hS
  let vi := Function.invFunOn v S
  have hvi : IsPLHomeomorphOn vi S S := hv.symm
  have hnvi : ¬ IsPLCirclePositive S vi := by
    intro hpos
    exact hnv (hpos.of_leftInverse hvi.bijOn hv.bijOn.mapsTo
      fun x hx => hv.bijOn.invOn_invFunOn.2 hx)
  let w := vi ∘ r
  have hw : IsPLHomeomorphOn w S S := hr.trans hvi
  have hwpos : IsPLCirclePositive S w :=
    isPLCirclePositive_comp_of_not_isPLCirclePositive hS hvi hr hnvi hnr
  have hid : IsPLHomeomorphOn (id : E → E) S S := hS.isPolyhedron.isPLHomeomorphOn_id
  have horient : IsPLCirclePositive S (id : E → E) ↔ IsPLCirclePositive S w :=
    ⟨fun _ => hwpos, fun _ => isPLCirclePositive_id hS⟩
  obtain ⟨D, β, hβ, hD, hβ0, hβ1, hβzero, hβone⟩ :=
    exists_isPLHomeomorphOn_arc_prod_of_isPLCirclePositive_iff hS hγ hAS hid hw horient
  have hflip {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 1 - s ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hbottom (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : β (s, 0) = (γ s, 0) := hβ0 s hs
  have htop (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      β (s, 1) = (vi (γ (1 - s)), 1) := by
    rw [hβ1 s hs]
    change (vi (r (γ s)), (1 : ℝ)) = (vi (γ (1 - s)), 1)
    rw [hrflip s hs]
  have hβmaps : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ⊆ β ⁻¹' (S ×ˢ Icc 0 1) :=
    fun z hz => hD (hβ.bijOn.mapsTo hz)
  let g := f ∘ β
  have hg : IsPiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    have hcomp := hf.isPiecewiseAffineOn.comp hβ.isPiecewiseAffineOn
    rwa [inter_eq_left.mpr hβmaps] at hcomp
  have hseam (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : g (s, 1) = g (1 - s, 0) := by
    have hγs : γ (1 - s) ∈ S := hAS (hγ.bijOn.mapsTo (hflip hs))
    have hvis : vi (γ (1 - s)) ∈ S := hvi.bijOn.mapsTo hγs
    change f (β (s, 1)) = f (β (1 - s, 0))
    rw [htop s hs, hbottom (1 - s) (hflip hs), hfv (vi (γ (1 - s))) hvis]
    change f (v (Function.invFunOn v S (γ (1 - s))), 0) = f (γ (1 - s), 0)
    rw [hv.bijOn.invOn_invFunOn.2 hγs]
  have hbotinj : InjOn (fun s : ℝ => g (s, 0)) (Icc (0 : ℝ) 1) := by
    intro a ha b hb hab
    change f (β (a, 0)) = f (β (b, 0)) at hab
    rw [hbottom a ha, hbottom b hb] at hab
    have hga : (γ a, (0 : ℝ)) ∈ S ×ˢ {0} := ⟨hAS (hγ.bijOn.mapsTo ha), rfl⟩
    have hgb : (γ b, (0 : ℝ)) ∈ S ×ˢ {0} := ⟨hAS (hγ.bijOn.mapsTo hb), rfl⟩
    have heq : (γ a, (0 : ℝ)) = (γ b, 0) :=
      (hf.isPLHomeomorphOn_bottom hS.isPolyhedron).bijOn.injOn hga hgb hab
    exact hγ.bijOn.injOn ha hb (congrArg Prod.fst heq)
  have hflip_of_ends {x y : ℝ × ℝ}
      (hx : x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (hy : y ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (hxy : g x = g y) (hx0 : x.2 = 0) (hy1 : y.2 = 1) : x.1 = 1 - y.1 := by
    have hxs : x = (x.1, 0) := Prod.ext rfl hx0
    have hys : y = (y.1, 1) := Prod.ext rfl hy1
    apply hbotinj hx.1 (hflip hy.1)
    calc
      g (x.1, 0) = g x := congrArg g hxs.symm
      _ = g y := hxy
      _ = g (y.1, 1) := congrArg g hys
      _ = g (1 - y.1, 0) := hseam y.1 hy.1
  refine ⟨g, hg, ?_, hseam, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    rw [← hf.image_eq]
    exact ⟨β z, hβmaps hz, rfl⟩
  · intro x hx y hy hxy
    have hxy' : f (β x) = f (β y) := hxy
    rcases hf.eq_or_endpoints (β x) (hβmaps hx) (β y) (hβmaps hy) hxy' with
      heq | hends | hends
    · exact Or.inl (hβ.bijOn.injOn hx hy heq)
    · have hx0 : x.2 = 0 := (hβzero x hx).mp hends.1
      have hy1 : y.2 = 1 := (hβone y hy).mp hends.2
      exact Or.inr (Or.inl ⟨hx0, hy1, hflip_of_ends hx hy hxy hx0 hy1⟩)
    · have hx1 : x.2 = 1 := (hβone x hx).mp hends.1
      have hy0 : y.2 = 0 := (hβzero y hy).mp hends.2
      have hparam := hflip_of_ends hy hx hxy.symm hy0 hx1
      exact Or.inr (Or.inr ⟨hx1, hy0, by linarith⟩)

theorem exists_isPLHomeomorphOn_mobiusComplex_of_not_isPLCirclePositive
    {S : Set E} (hS : IsPLSphere 1 S) {T : Set F} {f : E × ℝ → F}
    (hf : IsCylindricalDiagram f S T) {v : E → E} (hv : IsPLHomeomorphOn v S S)
    (hnv : ¬ IsPLCirclePositive S v) (hfv : ∀ x ∈ S, f (x, 1) = f (v x, 0)) :
    ∃ (Q : Set F) (j : (Fin 5 → ℝ) → F),
      IsPLHomeomorphOn j mobiusComplex.space Q ∧ Q ⊆ T := by
  obtain ⟨g, hg, hgT, hseam, hfiber⟩ :=
    exists_isPiecewiseAffineOn_square_flip_of_not_isPLCirclePositive hS hf hv hnv hfv
  obtain ⟨j, hj⟩ := exists_isPLHomeomorphOn_mobiusComplex_of_square hg hseam hfiber
  exact ⟨_, j, hj, hgT⟩

end DifferentialGeometry.Topology.PiecewiseLinear
