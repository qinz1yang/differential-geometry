/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcSubset
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDerivedCellBase

/-! Arc gluing and derived-cell traces in combinatorial surfaces. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem boundaryComplex_space_eq_pair_of_space_eq_Icc_surfaceSplit
    (R : Geometry.SimplicialComplex ℝ ℝ) [Finite R.faces]
    (hRspace : R.space = Icc 0 1) (hRball : IsPLBall 1 R.space) :
    (@boundaryComplex _ _ _ (Classical.decEq _) 1 R).space = {(0 : ℝ), 1} := by
  have hsub : (@boundaryComplex _ _ _ (Classical.decEq _) 1 R).space ⊆
      frontier R.space :=
    boundaryComplex_space_subset_frontier_of_finrank (n := 0) (by simp) R
      hRball.isCombinatorialManifoldWithBoundary
  rw [hRspace, frontier_Icc (by norm_num : (0 : ℝ) ≤ 1)] at hsub
  have hsphere : IsPLSphere 0
      (@boundaryComplex _ _ _ (Classical.decEq _) 1 R).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall R hRball
  obtain ⟨a, b, hab, hboundary⟩ := isPLSphere_zero_iff.mp hsphere
  rw [hboundary] at hsub
  have ha : a ∈ ({(0 : ℝ), 1} : Set ℝ) := hsub (Or.inl rfl)
  have hb : b ∈ ({(0 : ℝ), 1} : Set ℝ) := hsub (Or.inr rfl)
  rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl)
  · exact (hab rfl).elim
  · exact hboundary
  · rw [hboundary, pair_comm]
  · exact (hab rfl).elim

private theorem exists_parametrization_Icc_boundaryComplex_surfaceSplit
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {A : Set E} (hA : IsPLBall 1 A)
    (K : Geometry.SimplicialComplex ℝ F) [Finite K.faces]
    {f : E → F} (hf : IsPLHomeomorphOn f A K.space) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) A ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) ∈ (@boundaryComplex _ _ _ (Classical.decEq _) 1 K).space ↔
          t = 0 ∨ t = 1 := by
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hA
  obtain ⟨R, hRfinite, hRspace⟩ :=
    (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfinite.to_subtype
  have hRball : IsPLBall 1 R.space := by
    rw [hRspace]
    exact isPLBall_Icc (by norm_num)
  have hcomp : IsPLHomeomorphOn (f ∘ γ) R.space K.space := by
    rw [hRspace]
    exact hγ.trans hf
  have hsourceBoundary :
      (@boundaryComplex _ _ _ (Classical.decEq _) 1 R).space = {(0 : ℝ), 1} :=
    boundaryComplex_space_eq_pair_of_space_eq_Icc_surfaceSplit R hRspace hRball
  refine ⟨γ, hγ, fun t ht => ?_⟩
  have htR : t ∈ R.space := hRspace.symm ▸ ht
  have hiff := mem_boundaryComplex_space_iff_of_isPLHomeomorphOn R K
    hRball.isCombinatorialManifoldWithBoundary hcomp htR
  rw [hsourceBoundary] at hiff
  simpa only [Function.comp_apply, mem_insert_iff, mem_singleton_iff] using hiff

private def reverseIccSurfaceSplit (f : ℝ → E) : ℝ → E := fun t => f (1 - t)

private noncomputable def concatenateSurfaceSplit (f g : ℝ → E) : ℝ → E :=
  fun t => if t ≤ 1 / 2 then f (2 * t) else g (2 * t - 1)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem concatenateSurfaceSplit_of_le {f g : ℝ → E} {t : ℝ} (ht : t ≤ 1 / 2) :
    concatenateSurfaceSplit f g t = f (2 * t) :=
  if_pos ht

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem concatenateSurfaceSplit_of_not_le {f g : ℝ → E} {t : ℝ}
    (ht : ¬t ≤ 1 / 2) : concatenateSurfaceSplit f g t = g (2 * t - 1) :=
  if_neg ht

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem concatenateSurfaceSplit_upperHalf {f g : ℝ → E} (hmid : f 1 = g 0)
    {t : ℝ} (ht : t ∈ Icc (1 / 2) 1) :
    concatenateSurfaceSplit f g t = g (2 * t - 1) := by
  by_cases h : t ≤ 1 / 2
  · have ht' : t = 1 / 2 := le_antisymm h ht.1
    subst t
    rw [concatenateSurfaceSplit_of_le (by norm_num)]
    norm_num
    exact hmid
  · exact concatenateSurfaceSplit_of_not_le h

private theorem double_mem_Icc_surfaceSplit {t : ℝ} (ht : t ∈ Icc 0 (1 / 2)) :
    2 * t ∈ Icc 0 1 :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

private theorem doubleBack_mem_Icc_surfaceSplit {t : ℝ} (ht : t ∈ Icc (1 / 2) 1) :
    2 * t - 1 ∈ Icc 0 1 :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

omit [FiniteDimensional ℝ E] in
private theorem isPiecewiseAffineOn_reverse_Icc_surfaceSplit {f : ℝ → E}
    (hf : IsPiecewiseAffineOn f (Icc 0 1)) :
    IsPiecewiseAffineOn (reverseIccSurfaceSplit f) (Icc 0 1) := by
  let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap 1 0
  have hA : ∀ t, A t = 1 - t := by
    intro t
    simp only [A, AffineMap.lineMap_apply_module, smul_eq_mul]
    ring
  have hsub : Icc (0 : ℝ) 1 ⊆ A ⁻¹' Icc 0 1 := by
    intro t ht
    rw [mem_preimage, hA]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h := hf.comp (isPiecewiseAffineOn_of_affine_of_isHPolytope A
    (isHPolytope_Icc (a := 0) (b := 1)))
  rw [inter_eq_left.mpr hsub] at h
  refine h.congr fun t _ => ?_
  rw [Function.comp_apply, hA]
  rfl

omit [FiniteDimensional ℝ E] in
private theorem isPiecewiseAffineOn_concatenate_surfaceSplit {f g : ℝ → E}
    (hf : IsPiecewiseAffineOn f (Icc 0 1)) (hg : IsPiecewiseAffineOn g (Icc 0 1))
    (hmid : f 1 = g 0) : IsPiecewiseAffineOn (concatenateSurfaceSplit f g) (Icc 0 1) := by
  have h₁ : IsPiecewiseAffineOn (concatenateSurfaceSplit f g) (Icc 0 (1 / 2)) := by
    let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap 0 2
    have hA : ∀ t, A t = 2 * t := by
      intro t
      simp [A, AffineMap.lineMap_apply_module, mul_comm]
    have hsub : Icc (0 : ℝ) (1 / 2) ⊆ A ⁻¹' Icc 0 1 := by
      intro t ht
      rw [mem_preimage, hA]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h := hf.comp (isPiecewiseAffineOn_of_affine_of_isHPolytope A
      (isHPolytope_Icc (a := 0) (b := 1 / 2)))
    rw [inter_eq_left.mpr hsub] at h
    refine h.congr fun t ht => ?_
    rw [Function.comp_apply, hA, concatenateSurfaceSplit_of_le ht.2]
  have h₂ : IsPiecewiseAffineOn (concatenateSurfaceSplit f g) (Icc (1 / 2) 1) := by
    let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap (-1) 1
    have hA : ∀ t, A t = 2 * t - 1 := by
      intro t
      simp only [A, AffineMap.lineMap_apply_module, smul_eq_mul]
      ring
    have hsub : Icc (1 / 2 : ℝ) 1 ⊆ A ⁻¹' Icc 0 1 := by
      intro t ht
      rw [mem_preimage, hA]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h := hg.comp (isPiecewiseAffineOn_of_affine_of_isHPolytope A
      (isHPolytope_Icc (a := 1 / 2) (b := 1)))
    rw [inter_eq_left.mpr hsub] at h
    refine h.congr fun t ht => ?_
    rw [Function.comp_apply, hA, concatenateSurfaceSplit_upperHalf hmid ht]
  have h := h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h

private theorem IsPLHomeomorphOn.reverse_Icc_surfaceSplit {f : ℝ → E} {A : Set E}
    (hf : IsPLHomeomorphOn f (Icc 0 1) A) :
    IsPLHomeomorphOn (reverseIccSurfaceSplit f) (Icc 0 1) A := by
  have hPL := isPiecewiseAffineOn_reverse_Icc_surfaceSplit hf.isPiecewiseAffineOn
  have hinj : InjOn (reverseIccSurfaceSplit f) (Icc 0 1) := by
    intro x hx y hy hxy
    have h := hf.bijOn.injOn
      (show 1 - x ∈ Icc (0 : ℝ) 1 by exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (show 1 - y ∈ Icc (0 : ℝ) 1 by exact ⟨by linarith [hy.2], by linarith [hy.1]⟩)
      (by simpa only [reverseIccSurfaceSplit] using hxy)
    linarith
  have himage : reverseIccSurfaceSplit f '' Icc 0 1 = A := by
    rw [← hf.image_eq]
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      simp only [reverseIccSurfaceSplit]
      congr 1
      ring
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    hPL (himage ▸ hinj.bijOn_image)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem concatenateSurfaceSplit_seam {f g : ℝ → E}
    (hfi : InjOn f (Icc 0 1)) (hgi : InjOn g (Icc 0 1)) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' Icc 0 1, z ∈ g '' Icc 0 1 → z = f 1) {x y : ℝ}
    (hx : x ∈ Icc 0 (1 / 2)) (hy : y ∈ Icc (1 / 2) 1)
    (h : concatenateSurfaceSplit f g x = concatenateSurfaceSplit f g y) : x = y := by
  rw [concatenateSurfaceSplit_of_le hx.2, concatenateSurfaceSplit_upperHalf hmid hy] at h
  have hz : f (2 * x) = f 1 :=
    hmeet _ ⟨2 * x, double_mem_Icc_surfaceSplit hx, rfl⟩
      ⟨2 * y - 1, doubleBack_mem_Icc_surfaceSplit hy, h.symm⟩
  have hxmid := hfi (double_mem_Icc_surfaceSplit hx) (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hz
  have hyzero : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
  have hymid := hgi (doubleBack_mem_Icc_surfaceSplit hy)
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hyzero
  linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem injOn_concatenateSurfaceSplit {f g : ℝ → E}
    (hfi : InjOn f (Icc 0 1)) (hgi : InjOn g (Icc 0 1)) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' Icc 0 1, z ∈ g '' Icc 0 1 → z = f 1) :
    InjOn (concatenateSurfaceSplit f g) (Icc 0 1) := by
  intro x hx y hy h
  rcases le_or_gt x (1 / 2) with hxl | hxg
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · rw [concatenateSurfaceSplit_of_le hxl, concatenateSurfaceSplit_of_le hyl] at h
      have hxy := hfi (double_mem_Icc_surfaceSplit ⟨hx.1, hxl⟩)
        (double_mem_Icc_surfaceSplit ⟨hy.1, hyl⟩) h
      linarith
    · exact concatenateSurfaceSplit_seam hfi hgi hmid hmeet
        ⟨hx.1, hxl⟩ ⟨hyg.le, hy.2⟩ h
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · exact (concatenateSurfaceSplit_seam hfi hgi hmid hmeet
        ⟨hy.1, hyl⟩ ⟨hxg.le, hx.2⟩ h.symm).symm
    · rw [concatenateSurfaceSplit_of_not_le (not_le.2 hxg),
        concatenateSurfaceSplit_of_not_le (not_le.2 hyg)] at h
      have hxy := hgi (doubleBack_mem_Icc_surfaceSplit ⟨hxg.le, hx.2⟩)
        (doubleBack_mem_Icc_surfaceSplit ⟨hyg.le, hy.2⟩) h
      linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem image_concatenateSurfaceSplit {f g : ℝ → E} (hmid : f 1 = g 0) :
    concatenateSurfaceSplit f g '' Icc 0 1 = f '' Icc 0 1 ∪ g '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases le_or_gt t (1 / 2) with h | h
    · exact Or.inl ⟨2 * t, double_mem_Icc_surfaceSplit ⟨ht.1, h⟩,
        (concatenateSurfaceSplit_of_le h).symm⟩
    · exact Or.inr ⟨2 * t - 1, doubleBack_mem_Icc_surfaceSplit ⟨h.le, ht.2⟩,
        (concatenateSurfaceSplit_of_not_le (not_le.2 h)).symm⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenateSurfaceSplit_of_le (by linarith [hu.2])]
      congr 1
      ring
    · refine ⟨(u + 1) / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenateSurfaceSplit_upperHalf hmid
        ⟨by linarith [hu.1], by linarith [hu.2]⟩]
      congr 1
      ring

private theorem exists_isPLHomeomorphOn_Icc_end_of_mem_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 1 K.space) {r : E}
    (hr : r ∈ (@boundaryComplex _ _ _ (Classical.decEq _) 1 K).space) :
    ∃ f : ℝ → E, IsPLHomeomorphOn f (Icc 0 1) K.space ∧ f 1 = r := by
  classical
  obtain ⟨f, hf, hboundary⟩ := exists_parametrization_Icc_boundaryComplex_surfaceSplit hK K
    hK.isPolyhedron.isPLHomeomorphOn_id
  obtain ⟨t, ht, htr⟩ := hf.bijOn.surjOn
    ((boundaryComplex_space_subset 1 K) hr)
  have htend : t = 0 ∨ t = 1 := (hboundary t ht).mp (by simpa only [id_eq, htr] using hr)
  rcases htend with rfl | rfl
  · refine ⟨reverseIccSurfaceSplit f, hf.reverse_Icc_surfaceSplit, ?_⟩
    simpa only [reverseIccSurfaceSplit, sub_self] using htr
  · exact ⟨f, hf, htr⟩

private theorem exists_isPLHomeomorphOn_Icc_start_of_mem_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 1 K.space) {r : E}
    (hr : r ∈ (@boundaryComplex _ _ _ (Classical.decEq _) 1 K).space) :
    ∃ f : ℝ → E, IsPLHomeomorphOn f (Icc 0 1) K.space ∧ f 0 = r := by
  classical
  obtain ⟨f, hf, hf1⟩ := exists_isPLHomeomorphOn_Icc_end_of_mem_boundaryComplex K hK hr
  refine ⟨reverseIccSurfaceSplit f, hf.reverse_Icc_surfaceSplit, ?_⟩
  simpa only [reverseIccSurfaceSplit, sub_zero] using hf1

open Classical in
theorem isPLBall_union_of_subcomplexes_inter_isPLBall_zero
    (R A B : Geometry.SimplicialComplex ℝ E)
    [Finite R.faces] [Finite A.faces] [Finite B.faces]
    (hR : IsCombinatorialManifoldWithBoundary 1 R)
    (hA : IsPLBall 1 A.space) (hB : IsPLBall 1 B.space)
    (hAR : A.faces ⊆ R.faces) (hBR : B.faces ⊆ R.faces)
    (hI : IsPLBall 0 (A.space ∩ B.space)) : IsPLBall 1 (A.space ∪ B.space) := by
  obtain ⟨r, hIeq⟩ := isPLBall_zero_iff.mp hI
  have hboundaryA : A.space ∩ B.space ⊆
      (@boundaryComplex _ _ _ (Classical.decEq _) 1 A).space :=
    inter_subset_boundaryComplex_of_isPLBall R A B hR hA hB hAR hBR hI
  have hboundaryB : A.space ∩ B.space ⊆
      (@boundaryComplex _ _ _ (Classical.decEq _) 1 B).space := by
    rw [inter_comm] at hI ⊢
    exact inter_subset_boundaryComplex_of_isPLBall R B A hR hB hA hBR hAR hI
  have hrI : r ∈ A.space ∩ B.space := hIeq.symm.subset (mem_singleton r)
  obtain ⟨f, hf, hf1⟩ :=
    exists_isPLHomeomorphOn_Icc_end_of_mem_boundaryComplex A hA (hboundaryA hrI)
  obtain ⟨g, hg, hg0⟩ :=
    exists_isPLHomeomorphOn_Icc_start_of_mem_boundaryComplex B hB (hboundaryB hrI)
  have hmid : f 1 = g 0 := hf1.trans hg0.symm
  have hmeet : ∀ z ∈ f '' Icc (0 : ℝ) 1, z ∈ g '' Icc (0 : ℝ) 1 → z = f 1 := by
    rw [hf.image_eq, hg.image_eq]
    intro z hzA hzB
    have hz : z ∈ ({r} : Set E) := hIeq ▸ ⟨hzA, hzB⟩
    exact (mem_singleton_iff.mp hz).trans hf1.symm
  have hinj := injOn_concatenateSurfaceSplit hf.bijOn.injOn hg.bijOn.injOn hmid hmeet
  have hball := isPLBall_image_Icc_of_isPiecewiseAffineOn (by norm_num : (0 : ℝ) < 1)
    (isPiecewiseAffineOn_concatenate_surfaceSplit hf.isPiecewiseAffineOn
      hg.isPiecewiseAffineOn hmid) hinj
  rwa [image_concatenateSurfaceSplit hmid, hf.image_eq, hg.image_eq] at hball

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_union_of_inter_isPLBall_zero
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) {C D : Set E}
    (hC : IsPLBall 1 C) (hD : IsPLBall 1 D) (hCK : C ⊆ K.space) (hDK : D ⊆ K.space)
    (hI : IsPLBall 0 (C ∩ D)) : IsPLBall 1 (C ∪ D) := by
  obtain ⟨R, hR, hfin, hcover⟩ := exists_isSubdivision_subcomplexes K
    (fun b : Bool => if b then C else D)
    (fun b => by cases b with
      | false => exact hD.isPolyhedron
      | true => exact hC.isPolyhedron)
    (fun b => by cases b with
      | false => exact hDK
      | true => exact hCK)
  let _ : Finite R.faces := hfin.to_subtype
  let A := restrict R C
  let B := restrict R D
  let _ : Finite A.faces := (restrict_faces_finite R C).to_subtype
  let _ : Finite B.faces := (restrict_faces_finite R D).to_subtype
  have hA : A.space = C := restrict_space_of_eq_biUnion R C (by simpa using hcover true)
  have hB : B.space = D := restrict_space_of_eq_biUnion R D (by simpa using hcover false)
  rw [← hA] at hC
  rw [← hB] at hD
  rw [← hA, ← hB] at hI ⊢
  exact isPLBall_union_of_subcomplexes_inter_isPLBall_zero R A B (hK.of_isSubdivision hR)
    hC hD (restrict_faces_subset R C) (restrict_faces_subset R D) hI

namespace IsCombinatorialManifoldWithBoundary

open Classical in
theorem isCombinatorialManifoldWithBoundary_derivedNeighborhoodCellBase_one
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {s : Finset E} (hs : s ∈ K.faces) :
    IsCombinatorialManifoldWithBoundary 1 (derivedNeighborhoodCellBase K s) := by
  let c := s.centroid ℝ id
  have hc : ({c} : Finset E) ∈ (PiecewiseLinear.barycentricSubdivision K).faces :=
    singleton_centroid_mem_barycentricSubdivision K hs
  let _ : Finite
      (upperLink (PiecewiseLinear.barycentricSubdivision K) ({c} : Finset E)).faces :=
    (upperLink_faces_finite (PiecewiseLinear.barycentricSubdivision K) {c}).to_subtype
  rcases hK.barycentricSubdivision.isPLSphere_or_isPLBall_upperLink
      (PiecewiseLinear.barycentricSubdivision K) hc (k := 0) (Finset.card_singleton c)
      (Nat.zero_le 1) with hbase | hbase
  · exact hbase.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
  · exact hbase.isCombinatorialManifoldWithBoundary

open Classical in
theorem isPLBall_derivedNeighborhoodCell_inter_inter_zero
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {s t u : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hcst : s ⊆ t ∨ t ⊆ s) (hcsu : s ⊆ u ∨ u ⊆ s) (hctu : t ⊆ u ∨ u ⊆ t) :
    IsPLBall 0 ((derivedNeighborhoodCell K s).space ∩
      (derivedNeighborhoodCell K t).space ∩ (derivedNeighborhoodCell K u).space) := by
  classical
  let d : Finset (Finset E) := {s, t, u}
  have hd : IsFlag K d := by
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [d, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    · intro v hv w hw
      simp only [d, Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
        first | exact Or.inl subset_rfl | exact hcst | exact hcst.symm |
          exact hcsu | exact hcsu.symm | exact hctu | exact hctu.symm
  have hdne : d.Nonempty := Finset.insert_nonempty s {t, u}
  have himage : d.image (fun v => v.centroid ℝ id) ∈
      (PiecewiseLinear.barycentricSubdivision K).faces := ⟨d, hd, hdne, rfl⟩
  have himageCard : (d.image fun v => v.centroid ℝ id).card = 3 := by
    rw [Finset.card_image_of_injOn (hd.injOn K (centroid_mem_openSimplex_of_mem_faces K))]
    simp [d, hst, hsu, htu]
  have hcard (v : Finset E) (hv : v ∈ (PiecewiseLinear.barycentricSubdivision K).faces) :
      v.card ≤ (d.image fun w => w.centroid ℝ id).card := by
    rw [himageCard]
    simpa using hK.barycentricSubdivision.card_le
      (PiecewiseLinear.barycentricSubdivision K) hv
  have hsingle := dualCell_space_eq_singleton_of_card
    (PiecewiseLinear.barycentricSubdivision K) himage hcard
  have hzero : IsPLBall 0 (⋂ v ∈ d, (derivedNeighborhoodCell K v).space) := by
    rw [iInter_derivedNeighborhoodCell_space K hd hdne, hsingle]
    exact isPLBall_zero_iff.mpr ⟨_, rfl⟩
  simpa [d, inter_assoc] using hzero

open Classical in
theorem isPLBall_union_iUnion_of_pairwiseDisjoint_in_curve
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) {ι : Type*} {C : Set E}
    (hC : IsPLBall 1 C) (hCK : C ⊆ K.space)
    (d : Finset ι) (A : ι → Set E) (hA : ∀ i ∈ d, IsPLBall 1 (A i))
    (hAK : ∀ i ∈ d, A i ⊆ K.space) (hI : ∀ i ∈ d, IsPLBall 0 (C ∩ A i))
    (hdis : ∀ i ∈ d, ∀ j ∈ d, i ≠ j → Disjoint (A i) (A j)) :
    IsPLBall 1 (C ∪ ⋃ i ∈ d, A i) := by
  classical
  induction d using Finset.induction_on with
  | empty => simpa using hC
  | @insert i d hi ih =>
    have hA' : ∀ j ∈ d, IsPLBall 1 (A j) :=
      fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hAK' : ∀ j ∈ d, A j ⊆ K.space :=
      fun j hj => hAK j (Finset.mem_insert_of_mem hj)
    have hI' : ∀ j ∈ d, IsPLBall 0 (C ∩ A j) :=
      fun j hj => hI j (Finset.mem_insert_of_mem hj)
    have hdis' : ∀ j ∈ d, ∀ k ∈ d, j ≠ k → Disjoint (A j) (A k) :=
      fun j hj k hk hjk => hdis j (Finset.mem_insert_of_mem hj) k
        (Finset.mem_insert_of_mem hk) hjk
    have hprev := ih hA' hAK' hI' hdis'
    have hprevK : (C ∪ ⋃ j ∈ d, A j) ⊆ K.space :=
      union_subset hCK (iUnion₂_subset hAK')
    have hinter : (C ∪ ⋃ j ∈ d, A j) ∩ A i = C ∩ A i := by
      apply Subset.antisymm
      · rintro x ⟨hx | hx, hxi⟩
        · exact ⟨hx, hxi⟩
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
          exact ((hdis j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _)
            (ne_of_mem_of_not_mem hj hi)).le_bot ⟨hxj, hxi⟩).elim
      · rintro x ⟨hx, hxi⟩
        exact ⟨Or.inl hx, hxi⟩
    have h := hK.isPLBall_union_of_inter_isPLBall_zero hprev
      (hA i (Finset.mem_insert_self _ _)) hprevK (hAK i (Finset.mem_insert_self _ _))
      (hinter.symm ▸ hI i (Finset.mem_insert_self _ _))
    simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using h

open Classical in
theorem isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces_one
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ≠ t)
    (hcst : s ⊆ t ∨ t ⊆ s) (d : Finset (Finset E)) (hd : ∀ u ∈ d, u ∈ K.faces)
    (hne : ∀ u ∈ d, u ≠ s ∧ u ≠ t)
    (hcomp : ∀ u ∈ d, (s ⊆ u ∨ u ⊆ s) ∧ (t ⊆ u ∨ u ⊆ t))
    (hincomp : ∀ u ∈ d, ∀ v ∈ d, u ≠ v → ¬u ⊆ v ∧ ¬v ⊆ u) :
    IsPLBall 1 ((derivedNeighborhoodCell K s).space ∩
      ((derivedNeighborhoodCell K t).space ∪ ⋃ u ∈ d, (derivedNeighborhoodCell K u).space)) := by
  classical
  let _ : Finite (derivedNeighborhoodCellBase K s).faces :=
    (upperLink_faces_finite (PiecewiseLinear.barycentricSubdivision K)
      {s.centroid ℝ id}).to_subtype
  have hbase := hK.isCombinatorialManifoldWithBoundary_derivedNeighborhoodCellBase_one hs
  have hcenter := hK.isPLBall_derivedNeighborhoodCell_inter hs ht hst hcst
  let A := fun u => (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K u).space
  have hA (u : Finset E) (hu : u ∈ d) : IsPLBall 1 (A u) :=
    hK.isPLBall_derivedNeighborhoodCell_inter hs (hd u hu) (hne u hu).1.symm
      (hcomp u hu).1
  have hAB (u : Finset E) (hu : u ∈ d) :
      A u ⊆ (derivedNeighborhoodCellBase K s).space :=
    derivedNeighborhoodCell_inter_subset_base K hs (hd u hu) (hne u hu).1.symm
  have hcenterB :
      (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space ⊆
        (derivedNeighborhoodCellBase K s).space :=
    derivedNeighborhoodCell_inter_subset_base K hs ht hst
  have hI (u : Finset E) (hu : u ∈ d) :
      IsPLBall 0 (((derivedNeighborhoodCell K s).space ∩
        (derivedNeighborhoodCell K t).space) ∩ A u) := by
    have heq : ((derivedNeighborhoodCell K s).space ∩
        (derivedNeighborhoodCell K t).space) ∩ A u =
          (derivedNeighborhoodCell K s).space ∩
            (derivedNeighborhoodCell K t).space ∩ (derivedNeighborhoodCell K u).space := by
      ext x
      simp only [A, mem_inter_iff]
      tauto
    rw [heq]
    exact hK.isPLBall_derivedNeighborhoodCell_inter_inter_zero hs ht (hd u hu) hst
      (hne u hu).1.symm (hne u hu).2.symm hcst (hcomp u hu).1 (hcomp u hu).2
  have hdis (u : Finset E) (hu : u ∈ d) (v : Finset E) (hv : v ∈ d)
      (hneuv : u ≠ v) : Disjoint (A u) (A v) :=
    (disjoint_derivedNeighborhoodCell_space K (hd u hu) (hd v hv)
      (hincomp u hu v hv hneuv).1 (hincomp u hu v hv hneuv).2).mono
        inter_subset_right inter_subset_right
  have h := hbase.isPLBall_union_iUnion_of_pairwiseDisjoint_in_curve hcenter hcenterB
    d A hA hAB hI hdis
  simpa only [inter_union_distrib_left, inter_iUnion] using h

end IsCombinatorialManifoldWithBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
