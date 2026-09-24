/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPair
import DifferentialGeometry.Topology.PiecewiseLinear.SphereDiskMarked

/-! Maps of two disjoint spherical disks retaining an interior marked point. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk_marked
    {S D₀ D₁ : Set E} {S' D₀' D₁' : Set F}
    (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    (hD₀ : IsPLBall 2 D₀) (hD₀S : D₀ ⊆ S) (hD₁S : D₁ ⊆ S)
    (hdis : Disjoint D₀ D₁) (hD₁'S' : D₁' ⊆ S') (hdis' : Disjoint D₀' D₁')
    {g : E → F} (hg : IsPLHomeomorphOn g D₀ D₀') (hD₀'S' : D₀' ⊆ S')
    {r₁ : (Fin 3 → ℝ) → E} {r₁' : (Fin 3 → ℝ) → F}
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁)
    (hr₁' : IsPLHomeomorphOn r₁' (stdSimplex ℝ (Fin 3)) D₁') :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧ EqOn G g D₀ ∧ G '' D₁ = D₁' ∧
      G (r₁ (stdCenter 1)) = r₁' (stdCenter 1) := by
  classical
  have hD₁ : IsPLBall 2 D₁ := ⟨r₁, hr₁⟩
  have hD₁' : IsPLBall 2 D₁' := ⟨r₁', hr₁'⟩
  obtain ⟨f, hf, hfg, hfD₁⟩ := exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk
    hS hS' hD₀ hD₀S hD₁ hD₁S hdis hD₁' hD₁'S' hdis' hg hD₀'S'
  have hf₁ : IsPLHomeomorphOn f D₁ D₁' := by
    have h := hf.restrict hD₁.isPolyhedron hD₁S
    rwa [hfD₁] at h
  have hr : IsPLHomeomorphOn (f ∘ r₁) (stdSimplex ℝ (Fin 3)) D₁' := hr₁.trans hf₁
  let R := closure (S' \ D₁')
  have hR : IsPLBall 2 R := hS'.isPLBall_closure_sdiff hD₁' hD₁'S'
  have hmeet : D₁' ∩ R = r₁' '' stdSimplexBoundary 2 :=
    hS'.inter_closure_sdiff_eq_image_stdSimplexBoundary hr₁' hD₁'S'
  have hbr := hr.image_stdSimplexBoundary_congr hr₁'
  have hB : IsPolyhedron (r₁' '' stdSimplexBoundary 2) := by
    rw [← hmeet]
    exact hD₁'.isPolyhedron.inter hR.isPolyhedron
  have hid : IsPLHomeomorphOn id ((f ∘ r₁) '' stdSimplexBoundary 2)
      (r₁' '' stdSimplexBoundary 2) := by
    rw [hbr]
    exact hB.isPLHomeomorphOn_id
  obtain ⟨k, hk, hkfix, hkc⟩ :=
    exists_isPLHomeomorphOn_extension_marked_stdSimplexBoundary hr hr₁' hid
  rw [hbr] at hkfix
  have hcover : D₁' ∪ R = S' := by
    refine Subset.antisymm
      (union_subset hD₁'S' (closure_minimal sdiff_subset hS'.isPolyhedron.isClosed)) ?_
    intro x hx
    by_cases hxD : x ∈ D₁'
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have hglue : IsPLHomeomorphOn (D₁'.piecewise k id) S' S' := by
    have h := hk.piecewise hR.isPolyhedron.isPLHomeomorphOn_id
      hD₁'.isPolyhedron hR.isPolyhedron (hkfix.mono hmeet.subset)
      (((hkfix.mono hmeet.subset).image_eq).trans (image_id _))
    rwa [hcover] at h
  refine ⟨D₁'.piecewise k id ∘ f, hf.trans hglue, fun x hx => ?_, ?_, ?_⟩
  · change D₁'.piecewise k id (f x) = g x
    have hfx : f x ∈ D₀' := (hfg hx).symm ▸ hg.bijOn.mapsTo hx
    rw [D₁'.piecewise_eq_of_notMem k id
      (fun hxD => disjoint_left.mp hdis' hfx hxD)]
    exact hfg hx
  · rw [image_comp, hfD₁]
    exact (D₁'.piecewise_eqOn k id).image_eq.trans hk.image_eq
  · change D₁'.piecewise k id (f (r₁ (stdCenter 1))) = r₁' (stdCenter 1)
    have hp : stdCenter 1 ∈ stdSimplex ℝ (Fin 3) :=
      openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)
    rw [D₁'.piecewise_eq_of_mem k id (hf₁.bijOn.mapsTo (hr₁.bijOn.mapsTo hp))]
    exact hkc

end DifferentialGeometry.Topology.PiecewiseLinear
