/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskCapRemoval
import DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskRim
import DifferentialGeometry.Topology.PiecewiseLinear.UpperLinkBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.UpperLinkSubcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem boundaryComplex_starComplex_eq_geometricLink {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {v : E}
    (hv : {v} ∈ K.faces)
    (hlink : IsPLSphere n (SimplicialComplex.geometricLink K {v}).space) :
    boundaryComplex (n + 1) (starComplex K v) =
      SimplicialComplex.geometricLink K {v} := by
  ext s
  rw [hK.mem_boundaryComplex_starComplex_faces_iff hv hlink,
    SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨hs, hvs⟩
    exact ⟨K.nonempty_of_mem_faces hs.1, hvs, hs.2⟩
  · rintro ⟨hne, hvs, hins⟩
    exact ⟨⟨K.down_closed hins (Finset.subset_insert _ _) hne, hins⟩, hvs⟩

open Classical in
theorem boundaryComplex_splittingDisk_eq_upperLink
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {e : Finset E}
    (he : e ∈ K.faces) (hcard : e.card = 2)
    (hebd : e ∉ (boundaryComplex 3 K).faces) :
    boundaryComplex 2 (splittingDisk K e he) =
      upperLink (dualCell K e he) {e.centroid ℝ id} := by
  let D := dualCell K e he
  let _ : Finite D.faces := (dualCell_faces_finite K he).to_subtype
  have hDball : IsPLBall 2 D.space := by
    exact hK.isPLBall_dualCell K he (k := 1) hcard (by omega)
  have hc : {e.centroid ℝ id} ∈ D.faces := singleton_centroid_mem_dualCell K he
  have hlink : IsPLSphere 1
      (SimplicialComplex.geometricLink D {e.centroid ℝ id}).space := by
    rw [show D = dualCell K e he from rfl, geometricLink_dualCell K he]
    exact hK.isPLSphere_upperLink_of_not_mem_boundaryComplex K he hebd
      (k := 1) hcard (by omega)
  have hsub := barycentricSubdivision_isSubdivision D
  have hlink' : IsPLSphere 1
      (SimplicialComplex.geometricLink (barycentricSubdivision D)
        {e.centroid ℝ id}).space :=
    (isPLSphere_geometricLink_iff_of_isSubdivision hsub hc).mpr hlink
  change boundaryComplex 2 (starComplex (barycentricSubdivision D) (e.centroid ℝ id)) = _
  rw [boundaryComplex_starComplex_eq_geometricLink _
    hDball.isCombinatorialManifoldWithBoundary.barycentricSubdivision
    (hsub.singleton_mem hc) hlink', geometricLink_barycentricSubdivision_singleton D hc]

open Classical in
theorem boundaryComplex_splittingDisk_inter_subcomplex
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hAK : A.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ A.faces) (hcard : e.card = 2)
    (hebd : e ∉ (boundaryComplex 3 K).faces) :
    (boundaryComplex 2 (splittingDisk K e (hAK he))).space ∩ A.space =
      (upperLink (dualCell A e he) {e.centroid ℝ id}).space := by
  rw [boundaryComplex_splittingDisk_eq_upperLink K hK (hAK he) hcard hebd]
  have hsub : (upperLink (dualCell K e (hAK he)) {e.centroid ℝ id}).space ⊆
      (dualCell K e (hAK he)).space := by
    exact (space_mono_of_faces_subset (upperLink_faces_subset _ _)).trans
      (barycentricSubdivision_isSubdivision _).space_eq.subset
  calc
    _ = (upperLink (dualCell K e (hAK he)) {e.centroid ℝ id}).space ∩
        (dualCell A e he).space := by
      rw [← dualCell_space_inter_subcomplex K A hAK he]
      ext x
      exact ⟨fun h => ⟨h.1, hsub h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    _ = _ := upperLink_space_inter_subcomplex _ _
      (dualCell_faces_subset_of_subcomplex K A hAK he) _

open Classical in
theorem isPLBall_boundary_splittingDisk_inter_subcomplex
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ (boundaryComplex 3 A).faces) (hcard : e.card = 2)
    (hebd : e ∉ (boundaryComplex 3 K).faces) :
    IsPLBall 1 ((boundaryComplex 2 (splittingDisk K e
      (hAK (boundaryComplex_faces_subset 3 A he)))).space ∩ A.space) := by
  have heA := boundaryComplex_faces_subset 3 A he
  rw [boundaryComplex_splittingDisk_inter_subcomplex K A hK hAK heA hcard hebd]
  let D := dualCell A e heA
  let _ : Finite D.faces := (dualCell_faces_finite A heA).to_subtype
  have hDball : IsPLBall 2 D.space :=
    hA.isPLBall_dualCell A heA (k := 1) hcard (by omega)
  have hc : {e.centroid ℝ id} ∈ D.faces := singleton_centroid_mem_dualCell A heA
  have hcbd : {e.centroid ℝ id} ∈ (boundaryComplex 2 D).faces := by
    apply (hDball.isCombinatorialManifoldWithBoundary.mem_boundaryComplex_faces_iff D).mpr
    refine ⟨hc, by simp, ?_⟩
    rw [Finset.card_singleton, show 2 - 1 = 1 from rfl,
      show D = dualCell A e heA from rfl, geometricLink_dualCell A heA]
    exact hA.isPLBall_upperLink_of_mem_boundaryComplex A he (k := 1) hcard
  exact hDball.isCombinatorialManifoldWithBoundary.isPLBall_upperLink_of_mem_boundaryComplex
    D hcbd (k := 0) (Finset.card_singleton _)

open Classical in
theorem isPLBall_closure_boundary_splittingDisk_sdiff
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ (boundaryComplex 3 A).faces) (hcard : e.card = 2)
    (hebd : e ∉ (boundaryComplex 3 K).faces) :
    IsPLBall 1 (closure ((boundaryComplex 2 (splittingDisk K e
      (hAK (boundaryComplex_faces_subset 3 A he)))).space \ A.space)) := by
  have heK := hAK (boundaryComplex_faces_subset 3 A he)
  let D := splittingDisk K e heK
  let _ : Finite D.faces := (splittingDisk_faces_finite K heK).to_subtype
  have hD : IsPLBall 2 D.space :=
    hK.isPLBall_splittingDisk K heK (k := 1) hcard (by omega)
  have hS := isPLSphere_boundaryComplex_space_of_isPLBall D hD
  have htrace := isPLBall_boundary_splittingDisk_inter_subcomplex K A hK hA hAK
    he hcard hebd
  have h := hS.isPLBall_closure_sdiff_one htrace inter_subset_left
  have heq : (boundaryComplex 2 D).space \ ((boundaryComplex 2 D).space ∩ A.space) =
      (boundaryComplex 2 D).space \ A.space := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  exact heq ▸ h

open Classical in
theorem exists_parametrizations_boundary_splittingDisk_complement
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ (boundaryComplex 3 A).faces) (hcard : e.card = 2)
    (hebd : e ∉ (boundaryComplex 3 K).faces) :
    let S := (boundaryComplex 2 (splittingDisk K e
      (hAK (boundaryComplex_faces_subset 3 A he)))).space
    ∃ γ δ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) (S ∩ A.space) ∧
      IsPLHomeomorphOn δ (Icc 0 1) (closure (S \ A.space)) ∧
      δ 0 = γ 0 ∧ δ 1 = γ 1 ∧
      (S ∩ A.space) ∩ closure (S \ A.space) = {γ 0, γ 1} := by
  dsimp only
  have heK := hAK (boundaryComplex_faces_subset 3 A he)
  let D := splittingDisk K e heK
  let _ : Finite D.faces := (splittingDisk_faces_finite K heK).to_subtype
  have hD : IsPLBall 2 D.space :=
    hK.isPLBall_splittingDisk K heK (k := 1) hcard (by omega)
  have hS := isPLSphere_boundaryComplex_space_of_isPLBall D hD
  have htrace := isPLBall_boundary_splittingDisk_inter_subcomplex K A hK hA hAK
    he hcard hebd
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one htrace
  obtain ⟨δ, hδ, hδ0, hδ1, hmeet, -⟩ :=
    hS.exists_isPLHomeomorphOn_closure_sdiff hγ inter_subset_left
  have heq : (boundaryComplex 2 D).space \ ((boundaryComplex 2 D).space ∩ A.space) =
      (boundaryComplex 2 D).space \ A.space := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [heq] at hδ hmeet
  exact ⟨γ, δ, hγ, hδ, hδ0, hδ1, hmeet⟩

end DifferentialGeometry.Topology.PiecewiseLinear
