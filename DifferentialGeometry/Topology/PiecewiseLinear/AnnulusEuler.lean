/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.EulerUnion
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitEuler
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem eulerChar_eq_of_annulus_complement
    (K A R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces] [Finite R.faces]
    {J : Set F} (hJ : IsPLSphere 1 J) {a b : ℝ} (hab : a < b) {ρ : F × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc a b) A.space)
    (hcover : A.space ∪ R.space = K.space)
    (htrace : A.space ∩ R.space = ρ '' (J ×ˢ {a, b})) : eulerChar R = eulerChar K := by
  obtain ⟨L, hLfin, hLspace⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLSphere 1 L.space := hLspace.symm ▸ hJ
  have hmap : IsPLHomeomorphOn ρ (L.space ×ˢ Icc a b) A.space := hLspace.symm ▸ hρ
  have hAχ := eulerChar_eq_zero_of_isPLHomeomorphOn_prod_Icc L A hL hab.le hmap
  have hleft : J ×ˢ {a} ⊆ J ×ˢ Icc a b := fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, hab.le⟩⟩
  have hright : J ×ˢ {b} ⊆ J ×ˢ Icc a b := fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨hab.le, le_rfl⟩⟩
  have hJ₀ : IsPLSphere 1 (ρ '' (J ×ˢ {a})) := hJ.of_isPLHomeomorphOn
    ((hJ.isPolyhedron.isPLHomeomorphOn_prod_const a).trans
      (hρ.restrict (isPolyhedron_prod_singleton hJ.isPolyhedron a) hleft))
  have hJ₁ : IsPLSphere 1 (ρ '' (J ×ˢ {b})) := hJ.of_isPLHomeomorphOn
    ((hJ.isPolyhedron.isPLHomeomorphOn_prod_const b).trans
      (hρ.restrict (isPolyhedron_prod_singleton hJ.isPolyhedron b) hright))
  have hdis : Disjoint (ρ '' (J ×ˢ {a})) (ρ '' (J ×ˢ {b})) := by
    apply disjoint_left.mpr
    rintro x ⟨u, hu, hux⟩ ⟨v, hv, hvx⟩
    have heq := hρ.bijOn.injOn (hleft hu) (hright hv) (hux.trans hvx.symm)
    exact hab.ne (hu.2.symm.trans ((congrArg Prod.snd heq).trans hv.2))
  obtain ⟨B, hBfin, hBspace⟩ := hJ₀.isPolyhedron.exists_simplicialComplex
  obtain ⟨C, hCfin, hCspace⟩ := hJ₁.isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  let _ : Finite C.faces := hCfin.to_subtype
  have hBχ := eulerChar_of_isPLSphere_one B (hBspace.symm ▸ hJ₀)
  have hCχ := eulerChar_of_isPLSphere_one C (hCspace.symm ▸ hJ₁)
  have hends : B.space ∪ C.space = ρ '' (J ×ˢ {a, b}) := by
    rw [hBspace, hCspace, ← image_union, ← prod_union, singleton_union]
  have hχends : Homology.eulerChar ℚ (TopCat.of ↥(ρ '' (J ×ˢ {a, b}))) = 0 := by
    rw [← hends, (isPolyhedron_space B).eulerChar_union_of_disjoint (isPolyhedron_space C)
      (by rwa [hBspace, hCspace]) ℚ, ← eulerChar_eq_singular B ℚ, ← eulerChar_eq_singular C ℚ,
      hBχ, hCχ, add_zero]
  have hχ := (isPolyhedron_space A).eulerChar_union_add_inter (isPolyhedron_space R) ℚ
  rw [hcover, htrace, hχends, ← eulerChar_eq_singular K ℚ,
    ← eulerChar_eq_singular A ℚ, ← eulerChar_eq_singular R ℚ, hAχ] at hχ
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
