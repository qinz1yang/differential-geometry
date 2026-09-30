/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

theorem mem_boundaryComplex_space_iff_degree {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hG : IsCombinatorialManifoldWithBoundary 1 G) {x : E} :
    x ∈ (boundaryComplex 1 G).space ↔ ∃ hx : {x} ∈ G.faces,
      ((SimplicialComplex.edgeGraph G).neighborSet (⟨x, hx⟩ : G.vertices)).ncard = 1 := by
  classical
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := (boundaryComplex 1 G).mem_space_iff.mp hx
    have hs' := hs
    obtain ⟨hsG, t, ht, hst, htc, -⟩ := hs'
    have hsc : s.card = 1 := by
      have hpos := Finset.card_pos.mpr (G.nonempty_of_mem_faces hsG)
      have hle := Finset.card_le_card hst
      omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsc
    have hxv : x = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hxs
    subst hxv
    refine ⟨hsG, ?_⟩
    apply (mem_boundaryComplex_vertices_iff_edgeGraph_neighborSet_ncard_eq_one G hG
      ⟨x, hsG⟩).mp
    rw [Geometry.SimplicialComplex.mem_vertices]
    convert hs
  · rintro ⟨hx, hdeg⟩
    have hv := (mem_boundaryComplex_vertices_iff_edgeGraph_neighborSet_ncard_eq_one G hG
      ⟨x, hx⟩).mpr hdeg
    rw [Geometry.SimplicialComplex.mem_vertices] at hv
    have hv' : {x} ∈ (boundaryComplex 1 G).faces := by convert hv
    exact (boundaryComplex 1 G).vertices_subset_space hv'

open Classical in
theorem map_mem_boundary_iff_mem_boundaryComplex (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) {x : EuclideanSpace ℝ (Fin T.piece.ambientDim)}
    (hx : x ∈ (T.branchComplex c).space) :
    T.piece.piece.map x ∈ BdM ↔ x ∈ (boundaryComplex 1 (T.branchComplex c)).space := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  have hxT : x ∈ T.complex.space := T.branchComplex_space_subset c hx
  have hxP : x ∈ T.piece.piece.complex.space := T.branchComplex_space_subset_piece c hx
  have hTbd : T.piece.piece.map x ∈ BdM ↔ x ∈ (boundaryComplex 1 T.complex).space := by
    constructor
    · intro hB
      have hmem : T.piece.piece.map x ∈ doublePointSet D D.domain ∩ BdM :=
        ⟨T.map_space ▸ ⟨x, hxT, rfl⟩, hB⟩
      rw [← T.map_boundary] at hmem
      obtain ⟨x', hx', hxx'⟩ := hmem
      have hx'P : x' ∈ T.piece.piece.complex.space :=
        space_mono_of_faces_subset T.faces_subset (boundaryComplex_space_subset 1 _ hx')
      rwa [T.piece.piece.bijOn.injOn hx'P hxP hxx'] at hx'
    · intro hbd
      have hmem : T.piece.piece.map x ∈
          T.piece.piece.map '' (boundaryComplex 1 T.complex).space := ⟨x, hbd, rfl⟩
      rw [T.map_boundary] at hmem
      exact hmem.2
  rw [hTbd, mem_boundaryComplex_space_iff_degree T.complex T.isManifoldWithBoundary,
    mem_boundaryComplex_space_iff_degree (T.branchComplex c)
      (T.branchComplex_isManifoldWithBoundary c)]
  constructor
  · rintro ⟨hxv, hdeg⟩
    have hxG : {x} ∈ (T.branchComplex c).faces :=
      (SimplicialComplex.singleton_mem_subcomplex_iff_mem_space (K := T.complex)
        (L := T.branchComplex c) (T.branchComplex_faces_subset c) hxv).mpr hx
    refine ⟨hxG, ?_⟩
    obtain ⟨w, hwc, hwx⟩ : x ∈ T.branchVertices c := hxG.2 (by simp)
    have hbv : T.branchVertex c ⟨w, hwc⟩ = ⟨x, hxG⟩ := Subtype.ext hwx
    rw [← hbv, T.branchEdgeGraph_neighborSet_ncard c ⟨w, hwc⟩]
    have hw : (⟨x, hxv⟩ : T.complex.vertices) = w := Subtype.ext hwx.symm
    change ((SimplicialComplex.edgeGraph T.complex).neighborSet w).ncard = 1
    rw [← hw]
    exact hdeg
  · rintro ⟨hxG, hdeg⟩
    have hxv : {x} ∈ T.complex.faces := T.branchComplex_faces_subset c hxG
    refine ⟨hxv, ?_⟩
    obtain ⟨w, hwc, hwx⟩ : x ∈ T.branchVertices c := hxG.2 (by simp)
    have hbv : T.branchVertex c ⟨w, hwc⟩ = ⟨x, hxG⟩ := Subtype.ext hwx
    rw [← hbv, T.branchEdgeGraph_neighborSet_ncard c ⟨w, hwc⟩] at hdeg
    have hw : (⟨x, hxv⟩ : T.complex.vertices) = w := Subtype.ext hwx.symm
    change ((SimplicialComplex.edgeGraph T.complex).neighborSet w).ncard = 1 at hdeg
    rw [← hw] at hdeg
    exact hdeg

theorem stdSimplexBoundary_one_eq :
    stdSimplexBoundary 1 = {(![1, 0] : Fin 2 → ℝ), ![0, 1]} := by
  ext x
  constructor
  · rintro ⟨hx, i, hi⟩
    have hsum : x 0 + x 1 = 1 := by
      have := hx.2
      rwa [Fin.sum_univ_two] at this
    fin_cases i
    · right
      ext j
      fin_cases j <;> simp <;> simp at hi <;> linarith
    · left
      ext j
      fin_cases j <;> simp <;> simp at hi <;> linarith
  · rintro (rfl | rfl)
    · refine ⟨⟨fun i => ?_, by simp [Fin.sum_univ_two]⟩, 1, by simp⟩
      fin_cases i <;> simp
    · refine ⟨⟨fun i => ?_, by simp [Fin.sum_univ_two]⟩, 0, by simp⟩
      fin_cases i <;> simp

theorem image_Icc_stdSimplex_two :
    (fun t : ℝ => (![1 - t, t] : Fin 2 → ℝ)) '' Icc 0 1 = Convexity.StdSimplex.coordinateSet ℝ (Fin 2) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => ?_, by simp [Fin.sum_univ_two]⟩
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith [ht.2]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ht.1
  · intro hx
    have hsum : x 0 + x 1 = 1 := by
      have := hx.2
      rwa [Fin.sum_univ_two] at this
    refine ⟨x 1, ⟨hx.1 1, by linarith [hx.1 0]⟩, ?_⟩
    ext j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith
    · rfl

open Classical in
theorem exists_arc_of_isBoundaryBranch (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : T.IsBoundaryBranch c) :
    ∃ γ : ℝ → M, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧
      γ '' Icc 0 1 = T.branchCarrier c ∧ γ 0 ∈ BdM ∧ γ 1 ∈ BdM ∧
        ∀ r ∈ Ioo (0 : ℝ) 1, γ r ∉ BdM := by
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  obtain ⟨g, hg⟩ := T.branchComplex_isPLBall hc
  have hbd : (boundaryComplex 1 (T.branchComplex c)).space = g '' stdSimplexBoundary 1 := by
    have h := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex (n := 0)
      (T.branchComplex c) hg
    rwa [simplexBoundary_stdVertices_space] at h
  set lam : ℝ → (Fin 2 → ℝ) := fun t => ![1 - t, t] with hlam
  have hlamc : Continuous lam := by
    rw [hlam]
    fun_prop
  have hlami : Function.Injective lam := by
    intro s t hst
    have h := congrFun hst 1
    simpa [hlam] using h
  have hlamimg : lam '' Icc 0 1 = Convexity.StdSimplex.coordinateSet ℝ (Fin 2) := image_Icc_stdSimplex_two
  have hlammem : ∀ t ∈ Icc (0 : ℝ) 1, lam t ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2) := fun t ht =>
    hlamimg ▸ mem_image_of_mem lam ht
  have hsub : (T.branchComplex c).space ⊆ T.piece.piece.complex.space :=
    T.branchComplex_space_subset_piece c
  refine ⟨fun t => T.piece.piece.map (g (lam t)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) := hg.isPiecewiseAffineOn.continuousOn
    have h2 := h1.comp hlamc.continuousOn fun t ht => hlammem t ht
    exact T.piece.piece.continuousOn.comp h2 fun t ht => hsub (hg.bijOn.mapsTo (hlammem t ht))
  · intro s hs t ht hst
    apply hlami
    apply hg.bijOn.injOn (hlammem s hs) (hlammem t ht)
    exact T.piece.piece.bijOn.injOn (hsub (hg.bijOn.mapsTo (hlammem s hs)))
      (hsub (hg.bijOn.mapsTo (hlammem t ht))) hst
  · change (T.piece.piece.map ∘ g ∘ lam) '' Icc 0 1 = T.piece.piece.map '' _
    rw [image_comp, image_comp, hlamimg, hg.image_eq]
  · have hmem : g (lam 0) ∈ (T.branchComplex c).space := hg.bijOn.mapsTo (hlammem 0 ⟨le_rfl,
      zero_le_one⟩)
    refine (T.map_mem_boundary_iff_mem_boundaryComplex c hmem).mpr ?_
    rw [hbd, stdSimplexBoundary_one_eq]
    exact ⟨lam 0, by simp [hlam], rfl⟩
  · have hmem : g (lam 1) ∈ (T.branchComplex c).space := hg.bijOn.mapsTo (hlammem 1 ⟨zero_le_one,
      le_rfl⟩)
    refine (T.map_mem_boundary_iff_mem_boundaryComplex c hmem).mpr ?_
    rw [hbd, stdSimplexBoundary_one_eq]
    exact ⟨lam 1, by simp [hlam], rfl⟩
  · intro r hr hB
    have hmem : g (lam r) ∈ (T.branchComplex c).space :=
      hg.bijOn.mapsTo (hlammem r ⟨hr.1.le, hr.2.le⟩)
    have h := (T.map_mem_boundary_iff_mem_boundaryComplex c hmem).mp hB
    rw [hbd, stdSimplexBoundary_one_eq] at h
    obtain ⟨z, hz, hgz⟩ := h
    have hzmem : z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2) := by
      rcases hz with rfl | rfl
      · simpa [hlam] using hlammem 0 ⟨le_rfl, zero_le_one⟩
      · simpa [hlam] using hlammem 1 ⟨zero_le_one, le_rfl⟩
    have hzr : z = lam r := hg.bijOn.injOn hzmem (hlammem r ⟨hr.1.le, hr.2.le⟩) hgz
    rcases hz with rfl | rfl
    · have := congrFun hzr 1
      simp [hlam] at this
      linarith [hr.1]
    · have := congrFun hzr 1
      simp [hlam] at this
      linarith [hr.2]

end NormalSingularSetTriangulation

end DifferentialGeometry.Topology.PiecewiseLinear
