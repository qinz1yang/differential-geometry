/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskInteriorMove
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_map_disk_eqOn_disjoint_disk
    {S D A B : Set E} (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S)
    (hA : IsPLBall 2 A) (hAS : A ⊆ S) (hB : IsPLBall 2 B) (hBS : B ⊆ S)
    (hDA : Disjoint D A) (hDB : Disjoint D B) :
    ∃ G : E → E, IsPLHomeomorphOn G S S ∧ G '' A = B ∧ EqOn G id D := by
  classical
  let R := closure (S \ D)
  have hR : IsPLBall 2 R := hS.isPLBall_closure_sdiff hD hDS
  obtain ⟨r, hr⟩ := hR
  have hR : IsPLBall 2 R := ⟨r, hr⟩
  have hrB : r '' stdSimplexBoundary 2 = R ∩ D :=
    hS.image_stdSimplexBoundary_complement hD hDS hr
  have hsub {C : Set E} (hCS : C ⊆ S) (hDC : Disjoint D C) :
      C ⊆ R \ r '' stdSimplexBoundary 2 := by
    intro x hx
    have hxD : x ∉ D := fun hxD => disjoint_left.mp hDC hxD hx
    exact ⟨subset_closure ⟨hCS hx, hxD⟩, fun hxB => hxD (hrB ▸ hxB).2⟩
  obtain ⟨f, hf, hfA, hffix⟩ := exists_isPLHomeomorphOn_map_disk_eqOn_boundary hr hA hB
    (hsub hAS hDA) (hsub hBS hDB)
  have hcompat : EqOn id f (D ∩ R) := by
    intro x hx
    exact (hffix (hrB.symm ▸ ⟨hx.2, hx.1⟩)).symm
  have hcover : D ∪ R = S := by
    apply Subset.antisymm (union_subset hDS (closure_minimal sdiff_subset hS.isPolyhedron.isClosed))
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have hG := hD.isPolyhedron.isPLHomeomorphOn_id.piecewise hf
    hD.isPolyhedron hR.isPolyhedron hcompat (image_id _)
  rw [hcover] at hG
  refine ⟨D.piecewise id f, hG, ?_, D.piecewise_eqOn id f⟩
  have hGA : EqOn (D.piecewise id f) f A := fun x hx =>
    D.piecewise_eq_of_notMem id f (fun hxD => disjoint_left.mp hDA hxD hx)
  exact hGA.image_eq.trans hfA

theorem exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk
    {S D₀ D₁ : Set E} {S' D₀' D₁' : Set F}
    (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    (hD₀ : IsPLBall 2 D₀) (hD₀S : D₀ ⊆ S)
    (hD₁ : IsPLBall 2 D₁) (hD₁S : D₁ ⊆ S) (hdis : Disjoint D₀ D₁)
    (hD₁' : IsPLBall 2 D₁') (hD₁'S' : D₁' ⊆ S') (hdis' : Disjoint D₀' D₁')
    {g : E → F} (hg : IsPLHomeomorphOn g D₀ D₀') (hD₀'S' : D₀' ⊆ S') :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧ EqOn G g D₀ ∧ G '' D₁ = D₁' := by
  obtain ⟨f, hf, hfg⟩ := exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two
    hS hS' hD₀ hD₀S hg hD₀'S'
  have hfD₀ : f '' D₀ = D₀' := hfg.image_eq.trans hg.image_eq
  have hA : IsPLBall 2 (f '' D₁) :=
    hD₁.of_isPLHomeomorphOn (hf.restrict hD₁.isPolyhedron hD₁S)
  have hAS : f '' D₁ ⊆ S' := (image_mono hD₁S).trans hf.image_eq.subset
  have hDA : Disjoint D₀' (f '' D₁) := by
    rw [← hfD₀]
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    exact disjoint_left.mp hdis hx ((hf.bijOn.injOn (hD₁S hy) (hD₀S hx) heq) ▸ hy)
  obtain ⟨k, hk, hkA, hkfix⟩ := exists_isPLHomeomorphOn_map_disk_eqOn_disjoint_disk
    hS' (hD₀.of_isPLHomeomorphOn hg) hD₀'S' hA hAS hD₁' hD₁'S' hDA hdis'
  refine ⟨k ∘ f, hf.trans hk, ?_, (image_comp k f D₁).trans hkA⟩
  intro x hx
  change k (f x) = g x
  exact (hkfix (hfD₀ ▸ mem_image_of_mem f hx)).trans (hfg hx)

open Classical in
theorem exists_isPLHomeomorphOn_map_disk_pair_of_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hK : IsPLBall 3 K.space) (hL : IsPLBall 3 L.space)
    {D₀ D₁ : Set E} {D₀' D₁' : Set F}
    (hD₀ : IsPLBall 2 D₀) (hD₀K : D₀ ⊆ (boundaryComplex 3 K).space)
    (hD₁ : IsPLBall 2 D₁) (hD₁K : D₁ ⊆ (boundaryComplex 3 K).space)
    (hdis : Disjoint D₀ D₁) (hD₁' : IsPLBall 2 D₁')
    (hD₁'L : D₁' ⊆ (boundaryComplex 3 L).space) (hdis' : Disjoint D₀' D₁')
    {g : E → F} (hg : IsPLHomeomorphOn g D₀ D₀')
    (hD₀'L : D₀' ⊆ (boundaryComplex 3 L).space) :
    ∃ G : E → F, IsPLHomeomorphOn G K.space L.space ∧ EqOn G g D₀ ∧ G '' D₁ = D₁' := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq _
  obtain ⟨f, hf, hfg, hfD₁⟩ := exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk
    (isPLSphere_boundaryComplex_space_of_isPLBall K hK)
    (isPLSphere_boundaryComplex_space_of_isPLBall L hL)
    hD₀ hD₀K hD₁ hD₁K hdis hD₁' hD₁'L hdis' hg hD₀'L
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K L hK hL hf
  exact ⟨G, hG, (hGf.mono hD₀K).trans hfg, (hGf.mono hD₁K).image_eq.trans hfD₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
