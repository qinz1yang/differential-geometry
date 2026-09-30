/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def standardTriangleShrink : (Fin 3 → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ) :=
  AffineMap.homothety (stdCenter 1) (2 : ℝ)⁻¹

theorem standardTriangleShrink_apply (x : Fin 3 → ℝ) (i : Fin 3) :
    standardTriangleShrink x i = (2 : ℝ)⁻¹ * x i + (6 : ℝ)⁻¹ := by
  simp [standardTriangleShrink, AffineMap.homothety_apply, stdCenter]
  ring

theorem standardTriangleShrink_injective : Function.Injective standardTriangleShrink := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  rw [standardTriangleShrink_apply, standardTriangleShrink_apply] at hi
  linarith

theorem standardTriangleShrink_mem_openSimplex {x : Fin 3 → ℝ}
    (hx : x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :
    standardTriangleShrink x ∈ openSimplex (stdVertices 1) := by
  rw [mem_openSimplex_stdVertices_iff]
  refine ⟨fun i => ?_, ?_⟩
  · rw [standardTriangleShrink_apply]
    have hxi := hx.1 i
    positivity
  · simp_rw [standardTriangleShrink_apply]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx.2]
    norm_num

theorem isPLHomeomorphOn_standardTriangleShrink :
    IsPLHomeomorphOn standardTriangleShrink (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      (standardTriangleShrink '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := by
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    (isHPolytope_stdSimplex (Fin 3)).isPolyhedron
  · exact (isPiecewiseAffineOn_of_affine standardTriangleShrink isOpen_univ).mono_of_isPolyhedron
      (isHPolytope_stdSimplex (Fin 3)).isPolyhedron (subset_univ _)
  · exact standardTriangleShrink_injective.injOn.bijOn_image

theorem isPLBall_standardTriangleShrink :
    IsPLBall 2 (standardTriangleShrink '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
  (isPLBall_stdSimplex 2).of_isPLHomeomorphOn isPLHomeomorphOn_standardTriangleShrink

theorem isPLSphere_standardTriangleShrink_boundary :
    IsPLSphere 1 (standardTriangleShrink '' stdSimplexBoundary 2) :=
  isPLHomeomorphOn_standardTriangleShrink.isPLSphere_image_stdSimplexBoundary

theorem disjoint_standardTriangleShrink_boundary_stdSimplexBoundary :
    Disjoint (standardTriangleShrink '' stdSimplexBoundary 2) (stdSimplexBoundary 2) := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx, rfl⟩ hy
  have hopen := standardTriangleShrink_mem_openSimplex hx.1
  rw [openSimplex_eq_sdiff_simplexBoundary (stdVertices 1)
    (stdVertices_affineIndependent 1), convexHull_stdVertices,
    simplexBoundary_stdVertices_space] at hopen
  exact hopen.2 hy

theorem IsPLHomeomorphOn.exists_inner_triangle [FiniteDimensional ℝ E] {D : Set E}
    {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) :
    ∃ q : (Fin 3 → ℝ) → E,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (q '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ∧
      IsPLSphere 1 (q '' stdSimplexBoundary 2) ∧
      q '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ⊆ r '' openSimplex (stdVertices 1) ∧
      Disjoint (q '' stdSimplexBoundary 2) (r '' stdSimplexBoundary 2) := by
  let q := r ∘ standardTriangleShrink
  have hsmall : standardTriangleShrink '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    rintro _ ⟨x, hx, rfl⟩
    exact openSimplex_stdVertices_subset_stdSimplex
      (standardTriangleShrink_mem_openSimplex hx)
  have hrsmall := hr.restrict isPLBall_standardTriangleShrink.isPolyhedron hsmall
  have hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      (q '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := by
    simpa only [q, image_comp] using isPLHomeomorphOn_standardTriangleShrink.trans hrsmall
  refine ⟨q, hq, hq.isPLSphere_image_stdSimplexBoundary, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨standardTriangleShrink x, standardTriangleShrink_mem_openSimplex hx, rfl⟩
  · rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    have hxS : standardTriangleShrink x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
      hsmall ⟨x, hx.1, rfl⟩
    change r z = r (standardTriangleShrink x) at heq
    have hxz := hr.bijOn.injOn hxS hz.1 heq.symm
    exact Set.disjoint_left.mp disjoint_standardTriangleShrink_boundary_stdSimplexBoundary
      ⟨x, hx, rfl⟩ (hxz ▸ hz)

open Classical in
theorem IsCombinatorialManifold.splittingDisk_subset_boundary_graphDualCell
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w : E} (hvw : v ≠ w)
    (he : {v, w} ∈ L.faces) :
    (splittingDisk K {v, w} (hL he)).space ⊆
      (boundaryComplex 3 (graphDualCell K L w)).space := by
  let Cv := graphDualCell K L v
  let Cw := graphDualCell K L w
  let _ : Finite Cv.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite Cw.faces := (graphDualCell_faces_finite K L w).to_subtype
  have hv : {v} ∈ L.faces := L.down_closed he (by simp) (Finset.singleton_nonempty v)
  have hw : {w} ∈ L.faces := L.down_closed he (by simp) (Finset.singleton_nonempty w)
  have hCv := hK.isPLBall_graphDualCell K L hL hcard hv
  have hCw := hK.isPLBall_graphDualCell K L hL hcard hw
  have hD : IsPLBall 2 (splittingDisk K {v, w} (hL he)).space :=
    hK.isPLBall_splittingDisk K (hL he) (Finset.card_pair hvw) (by omega)
  have hinter := graphDualCell_space_inter K L hL hcard hvw he
  have hI : IsPLBall 2 (Cw.space ∩ Cv.space) := by
    rw [inter_comm, hinter]
    exact hD
  have hsub := PiecewiseLinear.inter_subset_boundaryComplex_of_isPLBall
    (PiecewiseLinear.secondDerived K) Cw Cv
    hK.secondDerived.isCombinatorialManifoldWithBoundary hCw hCv
    ((graphDualCell_faces_subset K L w).trans (derivedNeighborhood_faces_subset K L))
    ((graphDualCell_faces_subset K L v).trans (derivedNeighborhood_faces_subset K L)) hI
  rw [inter_comm, hinter] at hsub
  exact hsub

open Classical in
theorem IsCombinatorialManifold.exists_graphDualCell_piercing
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w : E} (hvw : v ≠ w)
    (he : {v, w} ∈ L.faces) :
    ∃ (J C : Set E) (f : E → E),
      IsPLSphere 1 J ∧
      J ⊆ (splittingDisk K {v, w} (hL he)).space ∧
      Disjoint J (boundaryComplex 2 (splittingDisk K {v, w} (hL he))).space ∧
      IsPLHomeomorphOn f (graphDualCell K L w).space C ∧
      C ⊆ (graphDualCell K L w).space ∧ EqOn f id J ∧ IsPLBall 3 C ∧
      (graphDualCell K L v).space ∩ C = J := by
  let Cv := graphDualCell K L v
  let Cw := graphDualCell K L w
  let D := splittingDisk K {v, w} (hL he)
  let _ : Finite Cv.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite Cw.faces := (graphDualCell_faces_finite K L w).to_subtype
  let _ : Finite D.faces := (splittingDisk_faces_finite K (hL he)).to_subtype
  have hv : {v} ∈ L.faces := L.down_closed he (by simp) (Finset.singleton_nonempty v)
  have hw : {w} ∈ L.faces := L.down_closed he (by simp) (Finset.singleton_nonempty w)
  have hCv : IsPLBall 3 Cv.space := hK.isPLBall_graphDualCell K L hL hcard hv
  have hCw : IsPLBall 3 Cw.space := hK.isPLBall_graphDualCell K L hL hcard hw
  have hD : IsPLBall 2 D.space :=
    hK.isPLBall_splittingDisk K (hL he) (Finset.card_pair hvw) (by omega)
  have hinter : Cv.space ∩ Cw.space = D.space :=
    graphDualCell_space_inter K L hL hcard hvw he
  have hDbd : D.space ⊆ (boundaryComplex 3 Cw).space :=
    hK.splittingDisk_subset_boundary_graphDualCell K L hL hcard hvw he
  obtain ⟨r, hr⟩ := hD
  obtain ⟨q, hq, hJ, hqopen, hJouter⟩ := hr.exists_inner_triangle
  let J := q '' stdSimplexBoundary 2
  have hJD : J ⊆ D.space := by
    exact (image_mono fun _ hx => hx.1).trans <|
      hqopen.trans <|
        (image_mono openSimplex_stdVertices_subset_stdSimplex).trans hr.image_eq.subset
  have hJbd : J ⊆ (boundaryComplex 3 Cw).space := hJD.trans hDbd
  have hDparamBoundary : (boundaryComplex 2 D).space = r '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex D hr,
      simplexBoundary_stdVertices_space]
  have hJdis : Disjoint J (boundaryComplex 2 D).space := by
    rw [hDparamBoundary]
    exact hJouter
  obtain ⟨f, hf, hmap, hfix, -, hmeet⟩ :=
    hCw.isCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward Cw
      hJ.isPolyhedron hJbd
  let C := f '' Cw.space
  have hCCw : C ⊆ Cw.space := image_subset_iff.mpr hmap
  have hCball : IsPLBall 3 C := hCw.of_isPLHomeomorphOn hf
  have hCvC : Cv.space ∩ C = J := by
    apply Subset.antisymm
    · rintro x ⟨hxv, hxC⟩
      have hxw := hCCw hxC
      have hxD : x ∈ D.space := hinter ▸ ⟨hxv, hxw⟩
      exact hmeet.subset ⟨hxC, hDbd hxD⟩
    · intro x hxJ
      have hxD := hJD hxJ
      have hxvw := hinter.symm.subset hxD
      refine ⟨hxvw.1, ⟨x, hxvw.2, ?_⟩⟩
      exact hfix hxJ
  exact ⟨J, C, f, hJ, hJD, hJdis, hf, hCCw, hfix, hCball, hCvC⟩

open Classical in
theorem IsCombinatorialManifold.exists_graphDualCell_piercings_of_trivalent_vertex
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (w : Fin 3 → E)
    (hwinj : Function.Injective w) (hvw : ∀ i, v ≠ w i)
    (hneighbors : ∀ u, u ≠ v → ({v, u} ∈ L.faces ↔ u ∈ Set.range w)) :
    ∃ (J C : Fin 3 → Set E) (f : Fin 3 → E → E),
      (∀ i,
        IsPLSphere 1 (J i) ∧
        J i ⊆ (splittingDisk K {v, w i} (hL ((hneighbors (w i) (hvw i).symm).mpr
          ⟨i, rfl⟩))).space ∧
        Disjoint (J i)
          (boundaryComplex 2 (splittingDisk K {v, w i}
            (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩)))).space ∧
        IsPLHomeomorphOn (f i) (graphDualCell K L (w i)).space (C i) ∧
        C i ⊆ (graphDualCell K L (w i)).space ∧ EqOn (f i) id (J i) ∧
        IsPLBall 3 (C i) ∧ (graphDualCell K L v).space ∩ C i = J i) ∧
      Pairwise fun i j => Disjoint (J i) (J j) := by
  have hedge (i : Fin 3) : {v, w i} ∈ L.faces :=
    (hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩
  have hpierce (i : Fin 3) :=
    hK.exists_graphDualCell_piercing K L hL hcard (hvw i) (hedge i)
  choose J C f hJ hJD hJbd hf hCsub hfix hCball hinter using hpierce
  refine ⟨J, C, f, fun i => ⟨hJ i, hJD i, hJbd i, hf i, hCsub i, hfix i,
    hCball i, hinter i⟩, ?_⟩
  intro i j hij
  have hedgeNe : ({v, w i} : Finset E) ≠ {v, w j} := by
    intro heq
    have hmem : w i ∈ ({v, w j} : Finset E) := by
      rw [← heq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (w i))
    have hwij : w i = w j := by
      simpa [(hvw i).symm] using hmem
    exact hij (hwinj hwij)
  have hdis := disjoint_splittingDisk_space K (hL (hedge i)) (hL (hedge j))
    hedgeNe (by rw [Finset.card_pair (hvw i), Finset.card_pair (hvw j)])
  exact hdis.mono (hJD i) (hJD j)

end DifferentialGeometry.Topology.PiecewiseLinear
