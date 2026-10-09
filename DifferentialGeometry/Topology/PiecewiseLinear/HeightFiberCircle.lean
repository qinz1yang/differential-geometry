/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiberClosure
import DifferentialGeometry.Topology.PiecewiseLinear.LevelPolygons
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalComponents
import DifferentialGeometry.Topology.PiecewiseLinear.SingularLevelPolygons
import DifferentialGeometry.Topology.SimplicialComplex.PuncturedConnected

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_levelPolygon_of_between_heights
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) (r : ℝ)
    (hbelow : ∃ y ∈ K.space, ℓ y < r) (habove : ∃ z ∈ K.space, r < ℓ z) :
    ∃ J, J ∈ levelPolygons K.space ℓ r := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) h
  have hKm : IsCombinatorialManifold 2 K := hK.isCombinatorialManifold
  obtain ⟨y, hy, hyr⟩ := hbelow
  obtain ⟨z, hz, hrz⟩ := habove
  by_cases hp : ∃ p ∈ K.vertices, ℓ p = r
  · obtain ⟨p, hp, hpr⟩ := hp
    have hyp : y ≠ p := fun h => hyr.ne (h ▸ hpr)
    have hzp : z ≠ p := fun h => hrz.ne (h ▸ hpr.symm)
    obtain ⟨x, hx, hxr⟩ := (hKm.isConnected_sdiff_singleton hK.isConnected p).isPreconnected
      |>.intermediate_value ⟨hy, hyp⟩ ⟨hz, hzp⟩ ℓ.continuous.continuousOn ⟨hyr.le, hrz.le⟩
    have hxpoly := mem_sUnion_levelPolygons_of_ne_vertex K hKm hdimE ℓ.toLinearMap hlinear hinj
      hp hx.1 hx.2 (hxr.trans hpr.symm)
    obtain ⟨J, hJ, -⟩ := mem_sUnion.mp hxpoly
    exact ⟨J, hpr ▸ hJ⟩
  · have havoid : ∀ p ∈ K.vertices, ℓ.toLinearMap p ≠ r := fun p hpK hpheight => hp ⟨p, hpK,
      hpheight⟩
    obtain ⟨x, hx, hxr⟩ := hK.isConnected.isPreconnected.intermediate_value hy hz
      ℓ.continuous.continuousOn ⟨hyr.le, hrz.le⟩
    have hxpoly : x ∈ ⋃₀ levelPolygons K.space ℓ.toLinearMap r := by
      rw [sUnion_levelPolygons_of_ne_vertex_heights K hKm hdimE ℓ.toLinearMap hlinear havoid]
      exact ⟨hx, hxr⟩
    obtain ⟨J, hJ, -⟩ := mem_sUnion.mp hxpoly
    exact ⟨J, hJ⟩

theorem fiber_eq_levelPolygon_of_heightIndex_eq_zero
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) (r : ℝ)
    (hbelow : ∃ y ∈ K.space, ℓ y < r) (habove : ∃ z ∈ K.space, r < ℓ z)
    {J : Set E} (hJ : J ∈ levelPolygons K.space ℓ r) :
    K.space ∩ {x | ℓ x = r} = J := by
  obtain ⟨hcllow, hclhigh⟩ := closure_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero r
      hbelow habove
  obtain ⟨hconnlow, hconnhigh⟩ := isPreconnected_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ
      hinj hzero r
  obtain ⟨A, B, hunion, hinter, f, g, hf, hg, hfJ, hgJ⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hK hJ.1 (hJ.2.trans inter_subset_left)
  have hA : IsClosed A := (show IsPLBall 2 A from ⟨f, hf⟩).isPolyhedron.isClosed
  have hB : IsClosed B := (show IsPLBall 2 B from ⟨g, hg⟩).isPolyhedron.isClosed
  have hAproper : ¬ K.space ⊆ A := by
    intro hsub
    obtain ⟨x, hxB, hxJ⟩ := hg.isConnected_sdiff_image_stdSimplexBoundary.nonempty
    exact hxJ (hgJ.symm.subset (hinter.subset ⟨hsub (hunion.subset (Or.inr hxB)), hxB⟩))
  have hBproper : ¬ K.space ⊆ B := by
    intro hsub
    obtain ⟨x, hxA, hxJ⟩ := hf.isConnected_sdiff_image_stdSimplexBoundary.nonempty
    exact hxJ (hfJ.symm.subset (hinter.subset ⟨hxA, hsub (hunion.subset (Or.inl hxA))⟩))
  have hchoice {P : Set E} (hP : IsPreconnected P) (hPK : P ⊆ K.space) (hPJ : Disjoint P J) :
      P ⊆ A ∨ P ⊆ B := by
    apply isPreconnected_iff_subset_of_disjoint_closed.mp hP A B hA hB
      (hPK.trans_eq hunion.symm)
    rw [hinter, hPJ.inter_eq]
  have hlowchoice : K.space ∩ {x | ℓ x < r} ⊆ A ∨ K.space ∩ {x | ℓ x < r} ⊆ B :=
    hchoice hconnlow inter_subset_left (disjoint_left.mpr fun x hx hxJ =>
      (show ℓ x < r from hx.2).ne (hJ.2 hxJ).2)
  have hhighchoice : K.space ∩ {x | r < ℓ x} ⊆ A ∨ K.space ∩ {x | r < ℓ x} ⊆ B :=
    hchoice hconnhigh inter_subset_left (disjoint_left.mpr fun x hx hxJ =>
      (show r < ℓ x from hx.2).ne (hJ.2 hxJ).2.symm)
  have hcover : K.space ⊆ closure (K.space ∩ {x | ℓ x < r}) ∪
      closure (K.space ∩ {x | r < ℓ x}) := by
    rw [hcllow, hclhigh]
    intro x hx
    exact (le_total (ℓ x) r).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  have hnot {D : Set E} (hD : IsClosed D) (hproper : ¬ K.space ⊆ D)
      (hlow : K.space ∩ {x | ℓ x < r} ⊆ D) (hhigh : K.space ∩ {x | r < ℓ x} ⊆ D) : False :=
    hproper (hcover.trans (union_subset (closure_minimal hlow hD) (closure_minimal hhigh hD)))
  have hF : K.space ∩ {x | ℓ x = r} ⊆ closure (K.space ∩ {x | ℓ x < r}) ∩
      closure (K.space ∩ {x | r < ℓ x}) := by
    rw [hcllow, hclhigh]
    rintro x ⟨hxK, hxr⟩
    have hxr' : ℓ x = r := hxr
    exact ⟨⟨hxK, hxr'.le⟩, hxK, hxr'.ge⟩
  apply Subset.antisymm _ hJ.2
  rcases hlowchoice with hlow | hlow <;> rcases hhighchoice with hhigh | hhigh
  · exact (hnot hA hAproper hlow hhigh).elim
  · exact hF.trans ((inter_subset_inter (closure_minimal hlow hA)
      (closure_minimal hhigh hB)).trans_eq hinter)
  · exact hF.trans ((inter_subset_inter (closure_minimal hlow hB)
      (closure_minimal hhigh hA)).trans_eq ((inter_comm B A).trans hinter))
  · exact (hnot hB hBproper hlow hhigh).elim

theorem isPLSphere_one_fiber_of_heightIndex_eq_zero
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) (r : ℝ)
    (hbelow : ∃ y ∈ K.space, ℓ y < r) (habove : ∃ z ∈ K.space, r < ℓ z) :
    IsPLSphere 1 (K.space ∩ {x | ℓ x = r}) := by
  obtain ⟨J, hJ⟩ := exists_levelPolygon_of_between_heights K hK hdimE ℓ hℓ hinj r hbelow habove
  rw [fiber_eq_levelPolygon_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero r hbelow habove hJ]
  exact hJ.1

end DifferentialGeometry.Topology.PiecewiseLinear
