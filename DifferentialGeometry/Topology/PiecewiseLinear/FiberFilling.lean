/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSpanningDisk
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiberCircle
import DifferentialGeometry.Topology.PlanarJordan.RegionRecognition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_closure_inter_fiber
    {U : Set E} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ}
    (hJ : IsPLSphere 1 (frontier U ∩ {x | ℓ x = r}))
    (hne : (U ∩ {x | ℓ x = r}).Nonempty) :
    ∃ f : (Fin 3 → ℝ) → E,
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (closure U ∩ {x | ℓ x = r}) ∧
      f '' stdSimplexBoundary 2 = frontier U ∩ {x | ℓ x = r} := by
  obtain ⟨e, π, hleft, hfixed, hheight⟩ := exists_affine_coordinates_of_linear_fiber hdim ℓ hℓ r
  let J := frontier U ∩ {x | ℓ x = r}
  let W := e ⁻¹' U
  have hπinj : InjOn π J := by
    intro x hx y hy hxy
    exact ((hfixed x).mpr hx.2).symm.trans ((congrArg e hxy).trans ((hfixed y).mpr hy.2))
  have hπ : IsPLHomeomorphOn π J (π '' J) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJ.isPolyhedron
      ((isPiecewiseAffineOn_of_affine π.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hJ.isPolyhedron (subset_univ _)) hπinj.bijOn_image
  have hJ' : IsPLSphere 1 (π '' J) := hJ.of_isPLHomeomorphOn hπ
  have hpreJ : e ⁻¹' frontier U = π '' J := by
    ext y
    constructor
    · intro hy
      exact ⟨e y, ⟨hy, hheight y⟩, hleft y⟩
    · rintro ⟨x, hx, rfl⟩
      change e (π x) ∈ frontier U
      rw [(hfixed x).mpr hx.2]
      exact hx.1
  have hWopen : IsOpen W := hU.preimage e.continuous_of_finiteDimensional
  have hWbounded : Bornology.IsBounded W :=
    ((LinearMap.toContinuousLinearMap π).lipschitzWith.isBounded_image hbounded).subset
      (fun y hy => ⟨e y, hy, hleft y⟩)
  have hWne : W.Nonempty := by
    obtain ⟨x, hxU, hxr⟩ := hne
    refine ⟨π x, ?_⟩
    change e (π x) ∈ U
    rwa [(hfixed x).mpr hxr]
  have hWfront : frontier W ⊆ π '' J :=
    (e.continuous_of_finiteDimensional.frontier_preimage_subset U).trans_eq hpreJ
  have hWdis : Disjoint W (π '' J) := by
    rw [← hpreJ]
    exact (show Disjoint U (frontier U) from
      disjoint_interior_frontier.mono_left hU.interior_eq.symm.subset).preimage e
  have hW : W = Schoenflies.inside (π '' J) :=
    PlanarJordan.eq_inside_of_isOpen_isBounded_frontier_subset
      (isJordanCurve_of_isPLSphere_one hJ') hWopen hWbounded hWne hWfront hWdis
  have hA : IsPLBall 2 (closure W) := by
    rw [hW]
    exact isPLBall_closure_inside_of_isPLSphere_one hJ'
  have hfront : frontier (closure W) = π '' J := by
    rw [hW]
    exact frontier_closure_inside_of_isPLSphere_one hJ'
  have hpre : e ⁻¹' closure U = closure W := by
    rw [closure_eq_self_union_frontier U, preimage_union, hpreJ]
    change W ∪ π '' J = closure W
    rw [hW, closure_eq_self_union_frontier]
    exact congrArg (fun A => Schoenflies.inside (π '' J) ∪ A)
      (Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hJ')).frontier_inside.symm
  have himage : e '' closure W = closure U ∩ {x | ℓ x = r} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hpre.symm.subset hy, hheight y⟩
    · rintro ⟨hx, hxr⟩
      refine ⟨π x, hpre.subset ?_, (hfixed x).mpr hxr⟩
      change e (π x) ∈ closure U
      rwa [(hfixed x).mpr hxr]
  have he : IsPLHomeomorphOn e (closure W) (closure U ∩ {x | ℓ x = r}) := by
    rw [← himage]
    exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hA.isPolyhedron
      ((isPiecewiseAffineOn_of_affine e isOpen_univ).mono_of_isPolyhedron
        hA.isPolyhedron (subset_univ _)) hleft.injective.injOn.bijOn_image
  have heπJ : e '' (π '' J) = J := by
    rw [image_image]
    have heq : EqOn (e ∘ π) id J := fun x hx => (hfixed x).mpr hx.2
    exact heq.image_eq.trans (image_id _)
  obtain ⟨g, hg⟩ := hA
  refine ⟨e ∘ g, hg.trans he, ?_⟩
  rw [image_comp, hg.image_stdSimplexBoundary, hfront, heπJ]

theorem exists_isPLHomeomorphOn_filling_fiber_of_heightIndex_eq_zero
    (L R : Geometry.SimplicialComplex ℝ E) [Finite L.faces] [Finite R.faces]
    (hL : IsPLSphere 2 L.space) (hdim : Module.finrank ℝ E = 3)
    (hRfront : frontier R.space = L.space) (hRcl : closure (interior R.space) = R.space)
    (hRconn : IsPreconnected (interior R.space))
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ L.vertices)
    (hzero : heightIndex L.space ℓ = 0) (r : ℝ)
    (hbelow : ∃ x ∈ L.space, ℓ x < r) (habove : ∃ y ∈ L.space, r < ℓ y) :
    ∃ f : (Fin 3 → ℝ) → E,
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (R.space ∩ {x | ℓ x = r}) ∧
      f '' stdSimplexBoundary 2 = L.space ∩ {x | ℓ x = r} := by
  have hUfront : frontier (interior R.space) = L.space := by
    rw [frontier, hRcl, interior_interior, ← (isPolyhedron_space R).isClosed.frontier_eq, hRfront]
  have hJ : IsPLSphere 1 (frontier (interior R.space) ∩ {x | ℓ x = r}) := by
    rw [hUfront]
    exact isPLSphere_one_fiber_of_heightIndex_eq_zero L hL hdim ℓ hℓ hinj hzero r hbelow habove
  have hne : (interior R.space ∩ {x | ℓ x = r}).Nonempty := by
    obtain ⟨x, hx, hxr⟩ := hbelow
    obtain ⟨y, hy, hry⟩ := habove
    have hxcl : x ∈ closure (interior R.space) :=
      frontier_subset_closure (hUfront.symm.subset hx)
    have hycl : y ∈ closure (interior R.space) :=
      frontier_subset_closure (hUfront.symm.subset hy)
    obtain ⟨a, har, ha⟩ := mem_closure_iff.mp hxcl {z | ℓ z < r}
      (isOpen_lt ℓ.continuous continuous_const) hxr
    obtain ⟨b, hrb, hb⟩ := mem_closure_iff.mp hycl {z | r < ℓ z}
      (isOpen_lt continuous_const ℓ.continuous) hry
    obtain ⟨z, hz, hzr⟩ := hRconn.intermediate_value ha hb
      ℓ.continuous.continuousOn ⟨har.le, hrb.le⟩
    exact ⟨z, hz, hzr⟩
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) hz
  obtain ⟨f, hf, hfJ⟩ := exists_isPLHomeomorphOn_closure_inter_fiber isOpen_interior
    ((isPolyhedron_space R).isCompact.isBounded.subset interior_subset) hdim ℓ.toLinearMap hlinear
        hJ hne
  exact ⟨f, hRcl ▸ hf, hUfront ▸ hfJ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
