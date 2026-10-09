/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexCapLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem geometricLink_section_subsingleton_of_supporting_fiber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 3) {q : E} (hq : q ∈ convexHull ℝ (T : Set E))
    (M : Geometry.SimplicialComplex ℝ E)
    (hspace : M.space = convexHull ℝ (T : Set E))
    (f : E →L[ℝ] ℝ) (hfinj : InjOn f (T : Set E))
    (m : E →ₗ[ℝ] ℝ)
    (hsupport : ∀ x ∈ convexHull ℝ (T : Set E), m q ≤ m x)
    (hunique : ∀ x ∈ convexHull ℝ (T : Set E), f x = f q → m x = m q → x = q) :
    ((SimplicialComplex.geometricLink M {q}).space ∩ {x | f x = f q}).Subsingleton := by
  classical
  let P := vectorSpan ℝ (T : Set E)
  have hinf : Module.finrank ℝ (P ⊓ LinearMap.ker f.toLinearMap : Submodule ℝ E) = 1 :=
    finrank_vectorSpan_inf_ker_eq_one_of_affineIndependent_card_three
      T hT hcard f hfinj
  rintro a ⟨haL, haf⟩ b ⟨hbL, hbf⟩
  change f a = f q at haf
  change f b = f q at hbf
  have haM : a ∈ M.space :=
    space_mono_of_faces_subset (SimplicialComplex.geometricLink_le M {q}) haL
  have hbM : b ∈ M.space :=
    space_mono_of_faces_subset (SimplicialComplex.geometricLink_le M {q}) hbL
  have haC : a ∈ convexHull ℝ (T : Set E) := hspace ▸ haM
  have hbC : b ∈ convexHull ℝ (T : Set E) := hspace ▸ hbM
  have haq : a ≠ q := ne_of_mem_of_not_mem haL (notMem_geometricLink_space M)
  have hbq : b ≠ q := ne_of_mem_of_not_mem hbL (notMem_geometricLink_space M)
  have haP : a - q ∈ P := by
    change a - q ∈ vectorSpan ℝ (T : Set E)
    have h := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (k := ℝ) (s := (T : Set E))
      (convexHull_subset_affineSpan (T : Set E) haC)
      (convexHull_subset_affineSpan (T : Set E) hq)
    simpa only [vsub_eq_sub] using h
  have hbP : b - q ∈ P := by
    change b - q ∈ vectorSpan ℝ (T : Set E)
    have h := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (k := ℝ) (s := (T : Set E))
      (convexHull_subset_affineSpan (T : Set E) hbC)
      (convexHull_subset_affineSpan (T : Set E) hq)
    simpa only [vsub_eq_sub] using h
  have haK : a - q ∈ LinearMap.ker f.toLinearMap := by
    have haf' : f.toLinearMap a = f.toLinearMap q := by
      simpa only [ContinuousLinearMap.coe_coe] using haf
    rw [LinearMap.mem_ker, map_sub, haf', sub_self]
  have hbK : b - q ∈ LinearMap.ker f.toLinearMap := by
    have hbf' : f.toLinearMap b = f.toLinearMap q := by
      simpa only [ContinuousLinearMap.coe_coe] using hbf
    rw [LinearMap.mem_ker, map_sub, hbf', sub_self]
  have haI : a - q ∈ P ⊓ LinearMap.ker f.toLinearMap := ⟨haP, haK⟩
  have hbI : b - q ∈ P ⊓ LinearMap.ker f.toLinearMap := ⟨hbP, hbK⟩
  have hspan : P ⊓ LinearMap.ker f.toLinearMap = Submodule.span ℝ ({a - q} : Set E) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hinf haI (sub_ne_zero.mpr haq)
  rw [hspan] at hbI
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbI
  have hma0 : 0 ≤ m (a - q) := by
    rw [map_sub]
    exact sub_nonneg.mpr (hsupport a haC)
  have hmb0 : 0 ≤ m (b - q) := by
    rw [map_sub]
    exact sub_nonneg.mpr (hsupport b hbC)
  have hma : 0 < m (a - q) := by
    refine lt_of_le_of_ne hma0 (Ne.symm ?_)
    intro hzero
    apply haq
    apply hunique a haC haf
    simpa only [map_sub, sub_eq_zero] using hzero
  have hmb : 0 < m (b - q) := by
    refine lt_of_le_of_ne hmb0 (Ne.symm ?_)
    intro hzero
    apply hbq
    apply hunique b hbC hbf
    simpa only [map_sub, sub_eq_zero] using hzero
  have hmc := congrArg m hc
  simp only [map_smul, smul_eq_mul] at hmc
  have hcpos : 0 < c := by nlinarith
  have hbeq : b = q + c • (a - q) := by
    rw [add_comm]
    exact sub_eq_iff_eq_add.mp hc.symm
  exact ((isRadiallyInjective_geometricLink M) a haL b hbL c hcpos hbeq).symm

end DifferentialGeometry.Topology.PiecewiseLinear
