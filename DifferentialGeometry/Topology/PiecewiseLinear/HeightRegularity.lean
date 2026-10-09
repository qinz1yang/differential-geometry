/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightLevelLink
import DifferentialGeometry.Topology.PiecewiseLinear.SingularLevelPolygons

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem one_lt_encard_levelPolygons_of_mem_heightSingularPoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ heightSingularPoints K.space ℓ) :
    1 < (levelPolygons K.space ℓ (ℓ p)).encard := by
  classical
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) h
  have hpv := heightSingularPoints_subset_vertices K
    hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hdimE ℓ.toLinearMap
    hlinear hinj hp
  have hmem : p ∈ ⋃₀ levelPolygons K.space ℓ (ℓ p) :=
    mem_sUnion_levelPolygons_of_mem_heightSingularPoints K hK.isCombinatorialManifold
      hdimE ℓ.toLinearMap hlinear hinj hp
  obtain ⟨J, hJ, hpJ⟩ := mem_sUnion.mp hmem
  by_contra hnot
  have hcount : (levelPolygons K.space ℓ (ℓ p)).encard ≤ 1 := le_of_not_gt hnot
  have hsubsingle := encard_le_one_iff_subsingleton.mp hcount
  have hfiber : K.space ∩ {x | ℓ x = ℓ p} = J := by
    have hcover : K.space ∩ {x | ℓ x = ℓ p} =
        {p} ∪ ⋃₀ levelPolygons K.space ℓ (ℓ p) :=
      fiber_eq_singleton_union_sUnion_levelPolygons K hK.isCombinatorialManifold
        hdimE ℓ.toLinearMap hlinear hinj hpv
    refine Subset.antisymm ?_ hJ.2
    intro x hx
    rcases hcover.subset hx with hxp | hx
    · exact hxp ▸ hpJ
    · obtain ⟨C, hC, hxC⟩ := mem_sUnion.mp hx
      exact hsubsingle hC hJ ▸ hxC
  have hcircle : IsPLSphere 1 (K.space ∩ {x | ℓ x = ℓ p}) := hfiber.symm ▸ hJ.1
  exact notMem_heightSingularPoints_of_isPLSphere_one_fiber K hK hdimE ℓ hℓ hinj hpv hcircle hp

theorem heightSingularPoints_eq_empty_of_heightIndex_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) : heightSingularPoints K.space ℓ = ∅ := by
  classical
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) h
  let _ : Fintype (heightSingularPoints K.space ℓ) :=
    (finite_heightSingularPoints K hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
      hdimE ℓ.toLinearMap hlinear hinj).fintype
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hsum : ∑ q : heightSingularPoints K.space ℓ,
      ((levelPolygons K.space ℓ (ℓ q)).encard - 1) = 0 := by
    simpa only [heightIndex, tsum_fintype] using hzero
  have hterm : (levelPolygons K.space ℓ (ℓ p)).encard - 1 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le)).mp hsum
      ⟨p, hp⟩ (Finset.mem_univ _)
  exact (not_le_of_gt (one_lt_encard_levelPolygons_of_mem_heightSingularPoints K hK
    hdimE ℓ hℓ hinj hp)) (tsub_eq_zero_iff_le.mp hterm)

theorem heightIndex_eq_zero_iff_heightSingularPoints_eq_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) :
    heightIndex K.space ℓ = 0 ↔ heightSingularPoints K.space ℓ = ∅ :=
  ⟨heightSingularPoints_eq_empty_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj,
    heightIndex_eq_zero_of_no_singular_points⟩

end DifferentialGeometry.Topology.PiecewiseLinear
