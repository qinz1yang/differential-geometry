/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphEdgeArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualFaceRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem geometricLink_subset_boundary_star_of_isPLBall
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {v : E} (hv : {v} ∈ K.faces)
    (hlink : IsPLBall n (SimplicialComplex.geometricLink K {v}).space) :
    (SimplicialComplex.geometricLink K {v}).space ⊆
      (boundaryComplex (n + 1) (starComplex K v)).space := by
  classical
  let _ : Finite (starComplex K v).faces := (starComplex_faces_finite K v).to_subtype
  let _ : Finite (SimplicialComplex.geometricLink K {v}).faces :=
    ((Set.toFinite K.faces).subset (SimplicialComplex.geometricLink_le K {v})).to_subtype
  have hball : IsPLBall (n + 1) (starComplex K v).space := by
    rw [starComplex_space K v hv]
    exact hK.isPLBall_closedStar hv
  apply space_mono_of_faces_subset
  intro s hs
  obtain ⟨t, ht, hst, htcard⟩ := exists_face_superset_card_eq_of_isPLBall _ hlink hs
  obtain ⟨htne, hvt, hinst⟩ := (SimplicialComplex.mem_geometricLink_singleton K v t).mp ht
  have htB : t ∈ (boundaryComplex (n + 1) (starComplex K v)).faces := by
    refine (hball.isCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface
      (starComplex K v) htcard).mpr ⟨v, ?_⟩
    ext w
    constructor
    · rintro ⟨hwt, hw⟩
      by_contra hwv
      have hle := hK.card_le K hw.2
      have hvw : v ∉ insert w t := by
        rw [Finset.mem_insert, not_or]
        exact ⟨fun h => hwv (mem_singleton_iff.mpr h.symm), hvt⟩
      rw [Finset.card_insert_of_notMem hvw, Finset.card_insert_of_notMem hwt, htcard] at hle
      omega
    · intro hwv
      rw [mem_singleton_iff] at hwv
      subst w
      exact ⟨hvt, hinst, by rwa [Finset.insert_idem]⟩
  exact (boundaryComplex (n + 1) (starComplex K v)).down_closed htB hst
    ((SimplicialComplex.geometricLink K {v}).nonempty_of_mem_faces hs)

open Classical in
theorem splittingDisk_inter_residual_subset_closure_boundary_sdiff_boundary
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : L.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ L.faces) (heB : e ∈ (boundaryComplex 3 K).faces)
    (hcard : e.card = 2) (hmax : ∀ s ∈ L.faces, s.card ≤ e.card) :
    (splittingDisk K e (hL he)).space ∩ closure (K.space \ (derivedNeighborhood K L).space) ⊆
      closure ((boundaryComplex 2 (splittingDisk K e (hL he))).space \
        (boundaryComplex 3 K).space) := by
  classical
  let D := splittingDisk K e (hL he)
  let R := closure (K.space \ (derivedNeighborhood K L).space)
  let T := D.space ∩ R
  let B := boundaryComplex 3 K
  let G := restrict L B.space
  let X := barycentricSubdivision (dualCell K e (hL he))
  let c := e.centroid ℝ id
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let _ : Finite (dualCell K e (hL he)).faces := (dualCell_faces_finite K (hL he)).to_subtype
  have hBS : B.faces ⊆ K.faces := boundaryComplex_faces_subset 3 K
  have hGB : G.faces ⊆ B.faces := fun f hf =>
    ((mem_restrict_faces_iff_of_faces_subset K L B hL hBS).mp hf).2
  have heG : e ∈ G.faces := ⟨he, B.convexHull_subset_space heB⟩
  have hmaxG : ∀ f ∈ G.faces, f.card ≤ e.card := fun f hf => hmax f hf.1
  have hlocal : B.space \ (derivedNeighborhood K L).space =
      B.space \ (derivedNeighborhood B G).space := by
    rw [show G = restrict L B.space from rfl,
      derivedNeighborhood_restrict_core_eq K B L hBS hL,
      ← derivedNeighborhood_space_inter_subcomplex K B L hBS]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have htrace : T ∩ B.space = (splittingDisk B e heB).space ∩
      closure (B.space \ (derivedNeighborhood B G).space) := by
    change (D.space ∩ R) ∩ B.space = _
    rw [show (D.space ∩ R) ∩ B.space = (D.space ∩ B.space) ∩ (R ∩ B.space) by
      ext x; simp only [mem_inter_iff]; tauto]
    rw [show D.space ∩ B.space = (splittingDisk B e heB).space from
      splittingDisk_space_inter_subcomplex K B hBS heB,
      show R ∩ B.space = closure (B.space \ (derivedNeighborhood K L).space) from
        closure_sdiff_derivedNeighborhood_inter_subcomplex_ambient K K B L (subset_refl _) hBS hL,
      hlocal]
  have hfinite : (T ∩ B.space).Finite := by
    rw [htrace]
    apply IsPLSphere.finite_of_zero
    rw [splittingDisk_inter_residual_eq_geometricLink B G hGB heG hmaxG]
    let _ : Finite (dualCell B e heB).faces := (dualCell_faces_finite B heB).to_subtype
    rw [isPLSphere_geometricLink_iff_of_isSubdivision
      (barycentricSubdivision_isSubdivision (dualCell B e heB))
      (singleton_centroid_mem_dualCell B heB), geometricLink_dualCell]
    exact (isCombinatorialManifold_boundaryComplex K hK).isPLSphere_upperLink B heB
      (k := 1) hcard (by omega)
  have hT : IsPLBall 1 T :=
    hK.isPLBall_splittingDisk_inter_residual K L hL he heB (k := 1) hcard hmax
  have hTlink : T = (SimplicialComplex.geometricLink X {c}).space :=
    splittingDisk_inter_residual_eq_geometricLink K L hL he hmax
  have hX : IsPLBall 2 X.space := by
    rw [show X.space = (dualCell K e (hL he)).space from
      (barycentricSubdivision_isSubdivision (dualCell K e (hL he))).space_eq]
    exact hK.isPLBall_dualCell K (hL he) (k := 1) hcard (by omega)
  have hTB : T ⊆ (boundaryComplex 2 D).space := by
    rw [hTlink]
    exact geometricLink_subset_boundary_star_of_isPLBall X hX.isCombinatorialManifoldWithBoundary
      ((barycentricSubdivision_isSubdivision (dualCell K e (hL he))).singleton_mem
        (singleton_centroid_mem_dualCell K (hL he))) (hTlink ▸ hT)
  have hdense : closure (T \ B.space) = T := by
    have heq : T \ (T ∩ B.space) = T \ B.space := by
      ext x
      simp only [mem_sdiff, mem_inter_iff]
      tauto
    rw [← heq]
    exact hT.closure_sdiff_of_finite hfinite
  exact hdense.symm.subset.trans (closure_mono (sdiff_subset_sdiff_left hTB))

end DifferentialGeometry.Topology.PiecewiseLinear
