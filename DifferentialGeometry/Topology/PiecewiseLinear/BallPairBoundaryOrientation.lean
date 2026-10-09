/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskTraceChart
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionMeetingDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BallMarkedExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.PiecewiseLinear.HalfSpaceCircleOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePositiveConjugation

open Set Filter
open scoped Topology Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.LocalDegree

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem isPLCirclePositive_iff_orientationParity_eq_zero_of_ball_pair
    {P Q D : Set E3} (hP : IsPLBall 3 P) (hQ : IsPLBall 3 Q)
    {r : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : P ∩ Q = D) (hDP : D ⊆ frontier P) (hDQ : D ⊆ frontier Q)
    {K : E3 → E3} (hK : IsPLHomeomorphOn K (P ∪ Q) (P ∪ Q))
    (hKP : K '' P = P) (hKQ : K '' Q = Q) {z : E3} (hz : z ∈ interior (P ∪ Q)) :
    IsPLCirclePositive (r '' stdSimplexBoundary 2) K ↔
      embeddingOrientationParity isOpen_interior
        (hK.isPiecewiseAffineOn.continuousOn.mono interior_subset)
        (hK.bijOn.injOn.mono interior_subset) ⟨z, hz⟩ = 0 := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hDU : D ⊆ P ∪ Q := fun _ hx => Or.inl (hP.isPolyhedron.isClosed.frontier_subset (hDP hx))
  have hKD : K '' D = D := by
    rw [← hmeet, hK.bijOn.injOn.image_inter subset_union_left subset_union_right, hKP, hKQ]
  have hKdisk : IsPLHomeomorphOn K D D := by
    have h := hK.restrict hD.isPolyhedron hDU
    rwa [hKD] at h
  have hKball : IsPLHomeomorphOn K P P := by
    have h := hK.restrict hP.isPolyhedron subset_union_left
    rwa [hKP] at h
  have hKfr : K '' frontier P = frontier P :=
    hKball.image_frontier rfl hP.isPolyhedron.isClosed hP.isPolyhedron.isClosed
  let J := r '' stdSimplexBoundary 2
  have hJD : J ⊆ D := image_subset_iff.mpr fun _ hx => hr.bijOn.mapsTo hx.1
  have hKJ : K '' J = J := by
    simpa only [J, image_comp] using (hr.trans hKdisk).image_stdSimplexBoundary_congr hr
  have hKo : K '' (D \ J) = D \ J := by
    rw [hKdisk.bijOn.injOn.image_sdiff_subset hJD, hKD, hKJ]
  have hKmem {T : Set E3} (hTU : T ⊆ P ∪ Q) (hKT : K '' T = T)
      {x : E3} (hx : x ∈ P ∪ Q) : K x ∈ T ↔ x ∈ T := by
    constructor
    · intro h
      obtain ⟨y, hy, he⟩ := hKT.symm ▸ h
      exact hK.bijOn.injOn (hTU hy) hx he ▸ hy
    · intro h
      exact hKT ▸ mem_image_of_mem K h
  have hBo : IsPLBall 3 (P ∪ Q) := isPLBall_union_of_inter_isPLBall_two hP hQ
    (hmeet.symm ▸ hD) (hmeet.symm ▸ hDP) (hmeet.symm ▸ hDQ)
  have hDo : D \ J ⊆ interior (P ∪ Q) :=
    sdiff_subset_interior_union_of_inter_eq hP hQ hr hmeet hDP hDQ
  have hDc := hr.isConnected_sdiff_image_stdSimplexBoundary
  obtain ⟨y, hy⟩ := hDc.nonempty
  have hyO := hDo hy
  have hKy : K y ∈ D \ J := hKo ▸ mem_image_of_mem K hy
  obtain ⟨A, p, c, hA, hp, hDcsource, hpc, hcfr, hcP⟩ :=
    hP.exists_boundary_disk_trace_chart hD hDP
  let C : OpenPartialHomeomorph E3 E3 :=
    c ≫ₕ (euclideanProductChart 1).symm.toContinuousLinearEquiv.toHomeomorph.toOpenPartialHomeomorph
  have hcoord (x : E3) : euclideanProductChart 1 (C x) = c x :=
    (euclideanProductChart 1).apply_symm_apply (c x)
  have hDC : D ⊆ C.source := fun _ hx => ⟨hDcsource hx, mem_univ _⟩
  have hCval {x : E3} (hx : x ∈ D) : C x = euclideanProductPoint 1 (p x) 0 := by
    apply (euclideanProductChart 1).injective
    change euclideanProductChart 1 (C x) =
      euclideanProductChart 1 ((euclideanProductChart 1).symm (p x, 0))
    rw [hcoord, (euclideanProductChart 1).apply_symm_apply]
    exact Prod.ext (hpc x).symm ((hcfr x (hDcsource hx)).mp (hDP hx))
  have hpJ : p '' J = frontier A := by
    simpa only [J, image_comp] using (hr.trans hp).image_stdSimplexBoundary
  have hpo : p '' (D \ J) = interior A := by
    rw [hp.bijOn.injOn.image_sdiff_subset hJD, hp.image_eq, hpJ, self_sdiff_frontier]
  let f := p ∘ K ∘ Function.invFunOn p D
  have hf : IsPLHomeomorphOn f A A := (hp.symm.trans hKdisk).trans hp
  have hfB : MapsTo f (interior A) (interior A) :=
    fun _ hx => (hf.image_interior rfl) ▸ mem_image_of_mem f hx
  have hffr : f '' frontier A = frontier A :=
    hf.image_frontier rfl hA.isPolyhedron.isClosed hA.isPolyhedron.isClosed
  have hfS : BijOn f (frontier A) (frontier A) :=
    ⟨fun _ hx => hffr ▸ mem_image_of_mem f hx,
      hf.bijOn.injOn.mono hA.isPolyhedron.isClosed.frontier_subset, hffr.ge⟩
  obtain ⟨H, hHs, -, hH⟩ := exists_openPartialHomeomorph_of_continuousOn_injOn
    (E := E3) isOpen_interior (hK.isPiecewiseAffineOn.continuousOn.mono interior_subset)
      (hK.bijOn.injOn.mono interior_subset)
  let F := C.symm ≫ₕ (H ≫ₕ C)
  have hCy : C y ∈ F.source := by
    refine ⟨C.map_source (hDC hy.1), ?_⟩
    change C.symm (C y) ∈ (H ≫ₕ C).source
    rw [C.left_inv (hDC hy.1)]
    exact ⟨by change y ∈ H.source; rw [hHs]; exact hyO,
      by change H y ∈ C.source; rw [hH]; exact hDC hKy.1⟩
  have hpoint : euclideanProductPoint 1 (p y) 0 ∈ F.source := hCval hy.1 ▸ hCy
  have hnormal (v : E3) (hv : v ∈ F.source) :
      (0 ≤ (euclideanProductChart 1 (F v)).2 ↔ 0 ≤ (euclideanProductChart 1 v).2) ∧
      ((euclideanProductChart 1 (F v)).2 = 0 ↔ (euclideanProductChart 1 v).2 = 0) := by
    let x := C.symm v
    have hxc : x ∈ c.source := (C.map_target hv.1).1
    have hKxc : K x ∈ c.source := by
      have h : H x ∈ c.source := hv.2.2.1
      rwa [hH] at h
    have hxU : x ∈ P ∪ Q := interior_subset (hHs ▸ hv.2.1)
    have hin : euclideanProductChart 1 v = c x := by rw [← C.right_inv hv.1, hcoord]
    have hout : euclideanProductChart 1 (F v) = c (K x) := by
      change euclideanProductChart 1 (C (H x)) = _
      rw [hcoord, hH]
    rw [hin, hout, ← hcP _ hKxc, ← hcP _ hxc, ← hcfr _ hKxc, ← hcfr _ hxc]
    exact ⟨hKmem subset_union_left hKP hxU,
      hKmem (hP.isPolyhedron.isClosed.frontier_subset.trans subset_union_left) hKfr hxU⟩
  have htrace : ∀ v ∈ F.source, (euclideanProductChart 1 v).2 = 0 →
      F v = euclideanProductPoint 1 (f (euclideanProductChart 1 v).1) 0 := by
    intro v hv hv0
    let x := C.symm v
    have hxc : x ∈ c.source := (C.map_target hv.1).1
    have hxO : x ∈ interior (P ∪ Q) := hHs ▸ hv.2.1
    have hin : euclideanProductChart 1 v = c x := by rw [← C.right_inv hv.1, hcoord]
    have hxfr : x ∈ frontier P := (hcfr x hxc).mpr (by rwa [← hin])
    have hxQ : x ∈ Q := by
      by_contra hxQ
      apply hxfr.2
      refine interior_maximal (t := interior (P ∪ Q) ∩ Qᶜ) (fun t ht => ?_)
        (isOpen_interior.inter hQ.isPolyhedron.isClosed.isOpen_compl) ⟨hxO, hxQ⟩
      exact (interior_subset ht.1).resolve_right ht.2
    have hxD : x ∈ D := hmeet ▸ ⟨hP.isPolyhedron.isClosed.frontier_subset hxfr, hxQ⟩
    have hKxD : K x ∈ D := hKD ▸ mem_image_of_mem K hxD
    have hpx : (euclideanProductChart 1 v).1 = p x := by rw [hin, hpc]
    change C (H x) = _
    rw [hH, hCval hKxD, hpx]
    congr 1
    change p (K x) = p (K (Function.invFunOn p D (p x)))
    rw [hp.bijOn.invOn_invFunOn.1 hxD]
  have hpos : ∀ v ∈ F.source, 0 < (euclideanProductChart 1 v).2 →
      0 < (euclideanProductChart 1 (F v)).2 := by
    intro v hv hvpos
    have hn := (hnormal v hv).1.mpr (le_of_lt hvpos)
    have hne : (euclideanProductChart 1 (F v)).2 ≠ 0 :=
      fun he => (ne_of_gt hvpos) ((hnormal v hv).2.mp he)
    exact lt_of_le_of_ne hn hne.symm
  have hneg : ∀ v ∈ F.source, (euclideanProductChart 1 v).2 < 0 →
      (euclideanProductChart 1 (F v)).2 < 0 := by
    intro v hv hvneg
    exact lt_of_not_ge fun he => (not_le_of_gt hvneg) ((hnormal v hv).1.mp he)
  have hlocal := isPLCirclePositive_iff_halfspace_orientationParity_eq_zero_at hA
    hf.isPiecewiseAffineOn.continuousOn hf.bijOn.injOn hfB hfS
    (hpo ▸ mem_image_of_mem p hy) F.open_source F.continuousOn F.injOn hpoint htrace hpos hneg
  have hcircle : IsPLCirclePositive (frontier A) f ↔ IsPLCirclePositive J K := by
    rw [← hpJ]
    exact hp.isPLCirclePositive_conj_iff hJD (fun _ hx => hKJ ▸ mem_image_of_mem K hx)
  let a := OpenPartialHomeomorph.refl E3
  have hyH : y ∈ H.source := hHs ▸ hyO
  have hHy : H y ∈ D \ J := by rwa [hH]
  have hrel := chartOrientationParity_relative_eq_of_isPreconnected H a C hDc.isPreconnected
    (fun _ _ => mem_univ _) (fun _ hx => hDC hx.1) y hyH hy hHy
  have hleft : chartOrientationParity a (H ≫ₕ a) y (mem_univ _) ⟨hyH, mem_univ _⟩ =
      embeddingOrientationParity isOpen_interior
        (hK.isPiecewiseAffineOn.continuousOn.mono interior_subset)
        (hK.bijOn.injOn.mono interior_subset) ⟨y, hyO⟩ := by
    unfold chartOrientationParity
    exact embeddingOrientationParity_congr _ _ _ _ _ _ _ _ (Filter.Eventually.of_forall hH)
  have hright : chartOrientationParity C (H ≫ₕ C) y (hDC hy.1)
      ⟨hyH, by change H y ∈ C.source; rw [hH]; exact hDC hKy.1⟩ =
      embeddingOrientationParity F.open_source F.continuousOn F.injOn
        ⟨euclideanProductPoint 1 (p y) 0, hpoint⟩ := by
    unfold chartOrientationParity
    congr 1
    exact Subtype.ext (hCval hy.1)
  have hsame := embeddingOrientationParity_eq_of_isPreconnected isOpen_interior
    (hK.isPiecewiseAffineOn.continuousOn.mono interior_subset)
    (hK.bijOn.injOn.mono interior_subset)
    (hBo.isConnected_interior_of_finrank (by simp)).isPreconnected (Subset.refl _) hyO hz
  rw [hleft, hright] at hrel
  exact hcircle.symm.trans (hlocal.trans (by rw [← hrel, hsame]))

end DifferentialGeometry.Topology.PiecewiseLinear
