/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderComparison

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem isPolyhedron_prod_singleton {P : Set E} (hP : IsPolyhedron P) (a : ℝ) :
    IsPolyhedron (P ×ˢ ({a} : Set ℝ)) := by
  rw [← Icc_self a]
  exact hP.prod isHPolytope_Icc.isPolyhedron

namespace IsCylindricalDiagram

variable {f : E × ℝ → F} {P : Set E} {S : Set F}

theorem isPLHomeomorphOn_bottom [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : IsCylindricalDiagram f P S) (hP : IsPolyhedron P) :
    IsPLHomeomorphOn f (P ×ˢ ({0} : Set ℝ)) (f '' (P ×ˢ ({0} : Set ℝ))) := by
  refine (h.isPLHomeomorphOn_strip hP le_rfl (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (Or.inr (by norm_num))).restrict (isPolyhedron_prod_singleton hP 0) ?_
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  exact ⟨hx, ht.symm ▸ ⟨le_rfl, by norm_num⟩⟩

theorem isPLHomeomorphOn_top [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : IsCylindricalDiagram f P S) (hP : IsPolyhedron P) :
    IsPLHomeomorphOn f (P ×ˢ ({1} : Set ℝ)) (f '' (P ×ˢ ({1} : Set ℝ))) := by
  refine (h.isPLHomeomorphOn_strip hP (by norm_num : (0 : ℝ) ≤ 1 / 2) le_rfl
    (Or.inl (by norm_num))).restrict (isPolyhedron_prod_singleton hP 1) ?_
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  exact ⟨hx, ht.symm ▸ ⟨by norm_num, le_rfl⟩⟩

theorem eq_of_eq_top (h : IsCylindricalDiagram f P S) {x y : E} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : f (x, 1) = f (y, 1)) : x = y := by
  rcases h.eq_or_endpoints (x, 1) ⟨hx, by norm_num⟩ (y, 1) ⟨hy, by norm_num⟩ hxy with
    heq | hends | hends
  · exact congrArg Prod.fst heq
  · norm_num at hends
  · norm_num at hends

theorem exists_isPLHomeomorphOn_endMap [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : IsCylindricalDiagram f P S) (hP : IsPolyhedron P) :
    ∃ u : E → E, IsPLHomeomorphOn u P P ∧ ∀ x ∈ P, f (x, 0) = f (u x, 1) := by
  have hbot := h.isPLHomeomorphOn_bottom hP
  have htop := h.isPLHomeomorphOn_top hP
  have himg : f '' (P ×ˢ ({0} : Set ℝ)) = f '' (P ×ˢ ({1} : Set ℝ)) :=
    h.image_top_eq_bottom.symm
  have htop' : IsPLHomeomorphOn (Function.invFunOn f (P ×ˢ ({1} : Set ℝ)))
      (f '' (P ×ˢ ({0} : Set ℝ))) (P ×ˢ ({1} : Set ℝ)) := by
    rw [himg]
    exact htop.symm
  refine ⟨Prod.fst ∘ Function.invFunOn f (P ×ˢ ({1} : Set ℝ)) ∘ f ∘ fun x : E => (x, (0 : ℝ)),
    (((hP.isPLHomeomorphOn_prod_const 0).trans hbot).trans htop').trans
      (hP.isPLHomeomorphOn_fst_prod_const 1), fun x hx => ?_⟩
  have hmem : f (x, 0) ∈ f '' (P ×ˢ ({0} : Set ℝ)) := ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
  have hw2 : (Function.invFunOn f (P ×ˢ ({1} : Set ℝ)) (f (x, 0))).2 = 1 :=
    (htop'.bijOn.mapsTo hmem).2
  have hfw : f (Function.invFunOn f (P ×ˢ ({1} : Set ℝ)) (f (x, 0))) = f (x, 0) :=
    htop.bijOn.invOn_invFunOn.2 (himg ▸ hmem)
  exact hfw.symm.trans (congrArg f (Prod.ext rfl hw2))

theorem endMap_eq_iff
    (h : IsCylindricalDiagram f P S) {u : E → E} (hu : IsPLHomeomorphOn u P P)
    (hfu : ∀ x ∈ P, f (x, 0) = f (u x, 1)) {x y : E} (hx : x ∈ P) (hy : y ∈ P) :
    f (x, 0) = f (y, 1) ↔ y = u x := by
  refine ⟨fun hxy => ?_, fun hxy => hxy ▸ hfu x hx⟩
  exact h.eq_of_eq_top hy (hu.bijOn.mapsTo hx) (hxy.symm.trans (hfu x hx))

end IsCylindricalDiagram

theorem exists_isPLHomeomorphOn_of_eq_endMap [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G] {P : Set E} (hP : IsPolyhedron P) {S : Set F} {T : Set G}
    {f : E × ℝ → F} {g : E × ℝ → G}
    (hf : IsCylindricalDiagram f P S) (hg : IsCylindricalDiagram g P T)
    {u : E → E} (hu : IsPLHomeomorphOn u P P)
    (hfu : ∀ x ∈ P, f (x, 0) = f (u x, 1)) (hgu : ∀ x ∈ P, g (x, 0) = g (u x, 1)) :
    ∃ H : F → G, IsPLHomeomorphOn H S T ∧ ∀ x ∈ P ×ˢ Icc 0 1, H (f x) = g x :=
  hf.exists_isPLHomeomorphOn_of_end_identification hP hg fun _x hx _y hy =>
    (hf.endMap_eq_iff hu hfu hx hy).trans (hg.endMap_eq_iff hu hgu hx hy).symm

end DifferentialGeometry.Topology.PiecewiseLinear
