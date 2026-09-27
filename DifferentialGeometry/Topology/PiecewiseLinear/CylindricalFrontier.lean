/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalSurface
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalCircle
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalMonodromy
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldBallInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSubcomplexComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsCylindricalDiagram.frontier_subset_image_side_union_bottom
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hdim : Module.finrank ℝ F = 3) :
    frontier S ⊆ f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1) ∪
      f '' (D.space ×ˢ {0}) := by
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  have hSclosed : IsClosed S := hf.image_eq ▸
    ((hD.isPolyhedron.isCompact.prod isCompact_Icc).image_of_continuousOn
      hf.isPiecewiseAffineOn.continuousOn).isClosed
  intro z hz
  have hzS : z ∈ S := hSclosed.closure_eq ▸ hz.1
  obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hf.image_eq.symm ▸ hzS
  by_cases hxB : x ∈ (boundaryComplex 2 D).space
  · exact Or.inl ⟨(x, t), ⟨hxB, ht⟩, rfl⟩
  by_cases ht0 : t = 0
  · exact Or.inr ⟨(x, t), ⟨hx, ht0⟩, rfl⟩
  by_cases ht1 : t = 1
  · apply Or.inr
    exact hf.image_top_eq_bottom ▸ ⟨(x, t), ⟨hx, ht1⟩, rfl⟩
  exfalso
  have ht0' : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have ht1' : t < 1 := lt_of_le_of_ne ht.2 ht1
  let a := t / 2
  let b := (t + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hab : a < b := hat.trans htb
  have hprism := isPLBall_three_prod hD (isPLBall_Icc hab)
  have hstrip := hf.isPLHomeomorphOn_strip hD.isPolyhedron ha.le hb.le (Or.inl ha)
  obtain ⟨Q, hQfin, hQsp⟩ := hprism.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQ : IsPLBall 3 Q.space := hQsp.symm ▸ hprism
  have himage := hprism.of_isPLHomeomorphOn hstrip
  obtain ⟨C, hCfin, hCsp⟩ := himage.isPolyhedron.exists_simplicialComplex
  let _ : Finite C.faces := hCfin.to_subtype
  have hC : IsPLBall 3 C.space := hCsp.symm ▸ himage
  have hmap : IsPLHomeomorphOn f Q.space C.space := by rw [hQsp, hCsp]; exact hstrip
  have hxtQ : (x, t) ∈ Q.space := hQsp.symm ▸ ⟨hx, hat.le, htb.le⟩
  have hnotQ : (x, t) ∉ (boundaryComplex 3 Q).space := by
    rw [boundaryComplex_space_prism D hD hab Q hQsp]
    rintro (⟨-, htend⟩ | ⟨hx', -⟩)
    · rcases htend with htend | htend
      · exact hat.ne' htend
      · exact htb.ne htend
    · exact hxB hx'
  have hnotC : f (x, t) ∉ (boundaryComplex 3 C).space := fun h => hnotQ
    ((mem_boundaryComplex_space_iff_of_isPLHomeomorphOn Q C
      hQ.isCombinatorialManifoldWithBoundary hmap hxtQ).mp h)
  have hCfront := frontier_space_eq_boundaryComplex_space_of_finrank hdim C
    hC.isCombinatorialManifoldWithBoundary
  have hintC : f (x, t) ∈ interior C.space := by
    by_contra hnot
    apply hnotC
    rw [← hCfront]
    exact ⟨subset_closure (hmap.bijOn.mapsTo hxtQ), hnot⟩
  have hCS : C.space ⊆ S := by
    rw [hCsp, ← hf.image_eq]
    exact image_mono (fun _ hw => ⟨hw.1, ha.le.trans hw.2.1, hw.2.2.trans hb.le⟩)
  exact hz.2 (interior_mono hCS hintC)

open Classical in
theorem IsCylindricalDiagram.image_side_eq_boundaryComplex
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hdim : Module.finrank ℝ F = 3) :
    f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1) = (boundaryComplex 3 M).space := by
  let _ : Finite (boundaryComplex 3 M).faces := (boundaryComplex_faces_finite 3 M).to_subtype
  have hL := isCombinatorialManifold_boundaryComplex M hM
  have hJ := isPLSphere_boundaryComplex_space_of_isPLBall D hD
  have hside := hf.boundary D hD.isCombinatorialManifoldWithBoundary
  obtain ⟨K, _, _, hKfin, -, -, hK, -, hKsp, -⟩ :=
    hside.exists_surface_annulus_pair hJ (a := 1 / 2) (by norm_num)
  let _ : Finite K.faces := hKfin.to_subtype
  have hKL : K.space ⊆ (boundaryComplex 3 M).space :=
    hKsp.subset.trans (hf.image_side_subset_boundaryComplex D M hD hM)
  obtain ⟨R, hRfin, hR, hRsp, hRbd⟩ :=
    hL.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_two
      hK.isCombinatorialManifoldWithBoundary hKL
  let _ : Finite R.faces := hRfin.to_subtype
  have hRemptyBd : (boundaryComplex 2 R).space = ∅ := by
    rw [hRbd, Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K]
    simp
  have hRclosed : IsCombinatorialManifold 2 R := by
    intro v hv
    apply hR.isPLSphere_geometricLink_of_not_mem_boundary R hv
    intro hvB
    have h := (boundaryComplex 2 R).subset_space hvB (Finset.mem_singleton_self v)
    rw [hRemptyBd] at h
    exact h
  have hbottom : IsPLBall 2 (f '' (D.space ×ˢ {0})) :=
    hD.of_isPLHomeomorphOn (hf.isPLHomeomorphOn_slice hD.isPolyhedron (by norm_num))
  have hRbottom : R.space ⊆ f '' (D.space ×ˢ {0}) := by
    rw [hRsp]
    apply closure_minimal ?_ hbottom.isPolyhedron.isClosed
    intro x hx
    have hxfront : x ∈ frontier M.space := by
      rw [frontier_space_eq_boundaryComplex_space_of_finrank hdim M hM]
      exact hx.1
    exact ((hf.frontier_subset_image_side_union_bottom D hD hdim) hxfront).resolve_left
      (fun hxside => hx.2 (hKsp.symm.subset hxside))
  have hRempty : R.space = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hRclosed.not_subset_of_isPLBall R ⟨x, hx⟩ hbottom hRbottom
  apply Subset.antisymm (hf.image_side_subset_boundaryComplex D M hD hM)
  intro x hx
  by_contra hxnot
  have hxR : x ∈ R.space := hRsp.symm ▸ subset_closure ⟨hx, fun hxK => hxnot (hKsp.subset hxK)⟩
  rw [hRempty] at hxR
  exact hxR

open Classical in
theorem IsCylindricalDiagram.frontier_eq_image_side
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hdim : Module.finrank ℝ F = 3) :
    frontier M.space = f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1) := by
  classical
  rw [frontier_space_eq_boundaryComplex_space_of_finrank hdim M hM]
  exact (hf.image_side_eq_boundaryComplex D M hD hM hdim).symm

end DifferentialGeometry.Topology.PiecewiseLinear
