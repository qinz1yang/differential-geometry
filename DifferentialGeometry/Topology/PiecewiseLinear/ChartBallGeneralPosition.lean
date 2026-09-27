/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem subsingleton_convexHull_inter_convexHull_of_sup_eq_top {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdimE : Module.finrank ℝ E = 3) (K L : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ L.faces) (hscard : s.card ≤ 3) (htcard : t.card ≤ 2)
    (hst : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Subsingleton := by
  have h1 := finrank_vectorSpan_add_one_of_mem_faces K hs
  have h2 := finrank_vectorSpan_add_one_of_mem_faces L ht
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (vectorSpan ℝ (s : Set E))
    (vectorSpan ℝ (t : Set E))
  rw [hst, finrank_top, hdimE] at h3
  have h4 : Module.finrank ℝ ↥(vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E)) = 0 := by
    omega
  have hbot := Submodule.finrank_eq_zero.mp h4
  rintro x ⟨hxs, hxt⟩ y ⟨hys, hyt⟩
  have hA : x -ᵥ y ∈ vectorSpan ℝ (s : Set E) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hxs)
      (convexHull_subset_affineSpan _ hys)
  have hB : x -ᵥ y ∈ vectorSpan ℝ (t : Set E) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hxt)
      (convexHull_subset_affineSpan _ hyt)
  have hAB : x -ᵥ y ∈ vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) := ⟨hA, hB⟩
  rw [hbot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hAB
  exact hAB

open Classical in
theorem exists_isPLBall_transverse_of_isPLBall {P A U : Set (EuclideanSpace ℝ (Fin 3))}
    (hP : IsPLBall 3 P) (hA : IsCompact A) (hAP : A ⊆ interior P) (hU : IsOpen U)
    (hPU : P ⊆ U) (L C : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite L.faces] (hL : IsCombinatorialManifoldWithBoundary 2 L) (hCL : C.faces ⊆ L.faces)
    (hC : ∀ t ∈ C.faces, t.card ≤ 2)
    (hCB : ∀ t ∈ C.faces, t.card = 2 → t ∉ (boundaryComplex 2 L).faces) :
    ∃ P' : Set (EuclideanSpace ℝ (Fin 3)), IsPLBall 3 P' ∧ A ⊆ interior P' ∧ P' ⊆ U ∧
      (∀ x ∈ frontier P' ∩ L.space, HasPLCrossingAt (frontier P') L.space x) ∧
      (∀ x ∈ frontier P' ∩ C.space,
        HasPLCurveCrossingOnAt L.space (frontier P' ∩ L.space) C.space x) ∧
      (frontier P' ∩ C.space).Finite ∧
      ∃ M N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)), M.faces.Finite ∧
        N.faces ⊆ M.faces ∧ M.space = frontier P' ∧ N.space = frontier P' ∩ L.space ∧
        ∀ σ ∈ M.faces, σ ∉ N.faces → Disjoint (openSimplex σ) L.space := by
  classical
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hS : IsPLSphere 2 (frontier P) := hP.isPLSphere_frontier
  obtain ⟨K, hKfin, hKspace⟩ := hS.isPolyhedron.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  have hKman : IsCombinatorialManifold 2 K :=
    IsPLSphere.isCombinatorialManifold (n := 1) (by rw [hKspace]; exact hS)
  have hPc : IsCompact P := hP.isPolyhedron.isCompact
  obtain ⟨ε₁, hε₁, hε₁U⟩ := hPc.exists_thickening_subset_open hU hPU
  obtain ⟨ε₂, hε₂, hε₂A⟩ := hA.exists_thickening_subset_open isOpen_interior hAP
  have hBK : (⊥ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))).faces ⊆ K.faces := by
    rw [Geometry.SimplicialComplex.faces_bot]
    exact empty_subset _
  obtain ⟨h, M, hh, hclose, -, -, hMfin, hMman, hMspace, htrans⟩ :=
    exists_small_homeomorph_transverse_relative K ⊥ L hBK
      hKman.isCombinatorialManifoldWithBoundary (by omega)
      (fun s hs => by rw [Geometry.SimplicialComplex.faces_bot] at hs; exact hs.elim)
      isOpen_univ (subset_univ _) (lt_min hε₁ hε₂)
  have : Finite M.faces := hMfin.to_subtype
  have hcont : Continuous h := continuousOn_univ.mp hh.isPiecewiseAffineOn.continuousOn
  have hcont' : Continuous (Function.invFunOn h univ) :=
    continuousOn_univ.mp hh.isPiecewiseAffineOn_invFunOn.continuousOn
  let Hh : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := h
      invFun := Function.invFunOn h univ
      left_inv := fun x => hh.bijOn.invOn_invFunOn.1 (mem_univ x)
      right_inv := fun y => hh.bijOn.invOn_invFunOn.2 (mem_univ y)
      continuous_toFun := hcont
      continuous_invFun := hcont' }
  have hP' : IsPLBall 3 (Hh '' P) := hP.of_isPLHomeomorphOn (hh.restrict hP.isPolyhedron
    (subset_univ _))
  have hfr : frontier (Hh '' P) = M.space := by
    rw [← Hh.image_frontier, hMspace, hKspace]
    rfl
  refine ⟨Hh '' P, hP', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [← Hh.image_interior]
    refine ⟨Hh.symm y, hε₂A (Metric.mem_thickening_iff.mpr ⟨y, hy, ?_⟩), Hh.apply_symm_apply y⟩
    have hd := hclose (Hh.symm y)
    change dist (Hh (Hh.symm y)) (Hh.symm y) < min ε₁ ε₂ at hd
    rw [Hh.apply_symm_apply, dist_comm] at hd
    exact hd.trans_le (min_le_right _ _)
  · rintro _ ⟨x, hx, rfl⟩
    exact hε₁U (Metric.mem_thickening_iff.mpr ⟨x, hx, (hclose x).trans_le (min_le_left _ _)⟩)
  · intro x hx
    rw [hfr] at hx ⊢
    exact hasPLCrossingAt_of_transverse_faces M L hMman hL hdim htrans hx
  · intro x hx
    rw [hfr] at hx ⊢
    exact hasPLCurveCrossingOnAt_of_transverse_faces M L C
      (fun s hs => by have := hMman.card_le M hs; omega) hL hdim hCL hC (by convert hCB)
      htrans hx
  · rw [hfr]
    have hCfin : C.faces.Finite := (Set.toFinite L.faces).subset hCL
    have hfin : (⋃ s ∈ M.faces, ⋃ τ ∈ C.faces,
        convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3))) ∩
          convexHull ℝ (τ : Set (EuclideanSpace ℝ (Fin 3)))).Finite := by
      refine hMfin.biUnion fun s hs => hCfin.biUnion fun τ hτ => ?_
      rcases (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3))) ∩
        convexHull ℝ (τ : Set (EuclideanSpace ℝ (Fin 3)))).eq_empty_or_nonempty with he | hne
      · rw [he]
        exact finite_empty
      · exact (subsingleton_convexHull_inter_convexHull_of_sup_eq_top hdim M L hs (hCL hτ)
          (by have := hMman.card_le M hs; omega) (hC τ hτ) (htrans s hs τ (hCL hτ) hne)).finite
    refine hfin.subset ?_
    · rintro x ⟨hxM, hxC⟩
      obtain ⟨s, hs, hxs⟩ := M.mem_space_iff.mp hxM
      obtain ⟨τ, hτ, hxτ⟩ := C.mem_space_iff.mp hxC
      exact mem_iUnion₂.mpr ⟨s, hs, mem_iUnion₂.mpr ⟨τ, hτ, hxs, hxτ⟩⟩
  · obtain ⟨M', hM'M, hM'fin, hM'eq⟩ := exists_isSubdivision_subcomplexes M
      (fun _ : Unit => M.space ∩ L.space)
      (fun _ => (isPolyhedron_space M).inter (isPolyhedron_space L)) (fun _ => inter_subset_left)
    have hX := hM'eq ()
    refine ⟨M', restrict M' (M.space ∩ L.space), hM'fin, restrict_faces_subset _ _, ?_, ?_, ?_⟩
    · rw [hM'M.space_eq, hfr]
    · rw [restrict_space_of_eq_biUnion M' _ hX, hfr]
    · intro σ hσ hσN
      rw [Set.disjoint_left]
      intro x hxσ hxL
      apply hσN
      have hxM : x ∈ M.space := by
        rw [← hM'M.space_eq]
        exact M'.convexHull_subset_space hσ (openSimplex_subset_convexHull σ hxσ)
      have hxX : x ∈ M.space ∩ L.space := ⟨hxM, hxL⟩
      rw [hX] at hxX
      obtain ⟨τ, ⟨hτ, hτX⟩, hxτ⟩ := mem_iUnion₂.mp hxX
      have hστ := face_subset_of_mem_openSimplex_of_mem_convexHull _ hσ hτ hxσ hxτ
      exact ⟨hσ, (convexHull_mono (Finset.coe_subset.mpr hστ)).trans hτX⟩

end DifferentialGeometry.Topology.PiecewiseLinear
