/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellFlatChart
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitEndpointDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_disk_neighborhood {Ec Eint Ebd D Ω : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) (hD : IsPLBall 2 D) (hDM : D ⊆ Eint \ {P})
    (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ (M : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) M ∧ M ⊆ Eint \ {P} ∧ M ⊆ Ω ∧
      D ⊆ r '' openSimplex (stdVertices 1) ∧
      ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ M ↔ y ∈ Ec := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨L, hLfin, hL, hag⟩ := exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff
    (ι := Unit) {()} (M := fun _ => Eint) (Cc := fun _ => D) (P := fun _ => P)
    (fun _ _ => hpc.isOpenCell) (fun _ _ => hpc.regular)
    (fun i _ j _ hij => (hij (Subsingleton.elim i j)).elim)
    (fun _ _ => hD.isPolyhedron.isCompact) (fun _ _ => hDM)
  have : Finite L.faces := hLfin.to_subtype
  have hagD : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ y ∈ Eint :=
    hag () (Finset.mem_singleton_self _)
  have hDL : D ⊆ L.space := fun x hx => (hagD x hx).self_of_nhds.mpr (hDM hx).1
  let W : Set E3 := ({x | ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ y ∈ Eint} ∩ Ω) \ {P}
  have hW : IsOpen W := (isOpen_setOfPred_eventually_nhds.inter hΩ).sdiff isClosed_singleton
  have hDW : D ⊆ W := fun x hx => ⟨⟨hagD x hx, hDΩ hx⟩, (hDM hx).2⟩
  let V : Bool → Set E3
    | false => W
    | true => Dᶜ
  have hVo : ∀ i, IsOpen (((↑) : L.space → E3) ⁻¹' V i) := by
    intro i
    cases i
    · exact hW.preimage continuous_subtype_val
    · exact hD.isPolyhedron.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hcover : L.space ⊆ ⋃ i, V i := by
    intro x _
    by_cases hx : x ∈ D
    · exact mem_iUnion.mpr ⟨false, hDW hx⟩
    · exact mem_iUnion.mpr ⟨true, hx⟩
  obtain ⟨R₀, hR₀, hR₀fin, -, hstars₀⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_cover L (fun _ : Unit => D)
      (fun _ => hD.isPolyhedron) (fun _ => hDL) V hVo hcover
  have : Finite R₀.faces := hR₀fin.to_subtype
  obtain ⟨R, A, T, φ, ψ, hR, hRfin, hAR, hAfin, hAD, hTfin, hT, hIso, -⟩ :=
    exists_isSubdivision_subcomplex_isGlueIso_planar R₀ hD
      (hDL.trans hR₀.space_eq.symm.subset)
  have : Finite R.faces := hRfin.to_subtype
  have : Finite A.faces := hAfin.to_subtype
  have : Finite T.faces := hTfin.to_subtype
  have hstarsR : ∀ s ∈ R.faces, ∃ i, (⋃ v ∈ s, closedStar R v) ⊆ V i :=
    hR.closedStars_subset_cover hstars₀
  have hstars₂ : ∀ s ∈ (PiecewiseLinear.secondDerived R).faces,
      ∃ i, (⋃ v ∈ s, closedStar (PiecewiseLinear.secondDerived R) v) ⊆ V i :=
    (secondDerived_isSubdivision R).closedStars_subset_cover hstarsR
  have hcellW (s : Finset E3) (hs : s ∈ A.faces) :
      (derivedNeighborhoodCell R s).space ⊆ W := by
    have hsR := hAR hs
    have hc : {s.centroid ℝ id} ∈ (PiecewiseLinear.secondDerived R).faces :=
      (barycentricSubdivision_isSubdivision
        (PiecewiseLinear.barycentricSubdivision R)).singleton_mem
          (singleton_centroid_mem_barycentricSubdivision R hsR)
    obtain ⟨i, hi⟩ := hstars₂ _ hc
    have hi' : closedStar (PiecewiseLinear.secondDerived R) (s.centroid ℝ id) ⊆ V i := by
      simpa only [Finset.set_biUnion_singleton] using hi
    cases i
    · rw [derivedNeighborhoodCell_space_eq_closedStar R hsR]
      simpa only [V] using hi'
    · have hcentroidA : s.centroid ℝ id ∈ A.space :=
        A.convexHull_subset_space hs
          (s.centroid_mem_convexHull (A.nonempty_of_mem_faces hs))
      have hcentroidD : s.centroid ℝ id ∈ D := hAD ▸ hcentroidA
      have hcentroidNot : s.centroid ℝ id ∉ D := by
        simpa only [V, mem_compl_iff] using hi' (mem_closedStar_self _ hc)
      exact (hcentroidNot hcentroidD).elim
  let N := PiecewiseLinear.derivedNeighborhood R A
  have : Finite N.faces := (derivedNeighborhood_faces_finite R A).to_subtype
  have hNW : N.space ⊆ W := by
    change (PiecewiseLinear.derivedNeighborhood R A).space ⊆ W
    rw [← iUnion_derivedNeighborhoodCell_space R A hAR]
    exact iUnion₂_subset hcellW
  have hRL := hR.trans hR₀
  have hNL : N.space ⊆ L.space :=
    (derivedNeighborhood_space_subset R A).trans hRL.space_eq.subset
  have hNball : IsPLBall 2 N.space :=
    (hL.of_isSubdivision hRL).isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_in_surface
      hAR hT hIso
  have hDN : D ⊆ N.space := by
    change D ⊆ (PiecewiseLinear.derivedNeighborhood R A).space
    rw [← hAD, ← iUnion_derivedNeighborhoodCell_space R A hAR]
    exact space_subset_iUnion_derivedNeighborhoodCell_space R A hAR
  have hNnhds : ∀ x ∈ D, N.space ∈ 𝓝[L.space] x := by
    intro x hx
    have hxA : x ∈ A.space := hAD.symm ▸ hx
    have h := derivedNeighborhood_mem_nhdsWithin hAR hxA
    rwa [hRL.space_eq] at h
  have hagN : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ N.space ↔ y ∈ Eint := by
    intro x hx
    obtain ⟨U, hU, hUN⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hNnhds x hx)
    filter_upwards [hU, hagD x hx] with y hyU hy
    exact ⟨fun hyN => hy.mp (hNL hyN), fun hyE => hUN ⟨hyU, hy.mpr hyE⟩⟩
  obtain ⟨r, hr⟩ := hNball
  refine ⟨N.space, r, hr, ?_, fun x hx => (hNW hx).1.2, ?_, ?_⟩
  · intro x hx
    exact ⟨(hNW hx).1.1.self_of_nhds.mp (hNL hx), (hNW hx).2⟩
  · rw [hr.image_openSimplex_eq_sdiff_boundaryComplex N rfl]
    intro x hx
    refine ⟨hDN hx, fun hxB => ?_⟩
    obtain ⟨S, hSN, hSfin, hxS⟩ := exists_isSubdivision_singleton_mem N (hDN hx)
    have : Finite S.faces := hSfin.to_subtype
    obtain ⟨χ⟩ := hpc.isOpenCell
    have hsph := isPLSphere_one_geometricLink_of_homeomorph S Metric.isOpen_ball χ hxS
      (by rw [hSN.space_eq]; exact hagN x hx)
    have hball := (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision (n := 1)
      N S (show IsPLBall 2 N.space from ⟨r, hr⟩).isCombinatorialManifoldWithBoundary
        hSN hxS).mpr hxB
    exact hball.not_isPLSphere hsph
  · intro x hx
    have hbdc : IsClosed Ebd := by
      obtain ⟨χ⟩ := hpc.isSphere
      exact (isCompact_iff_compactSpace.mpr χ.symm.compactSpace).isClosed
    have hxbd : x ∉ Ebd := fun h => Set.disjoint_left.mp hpc.disjointRim (hDM hx).1 h
    filter_upwards [hagN x hx, hbdc.isOpen_compl.mem_nhds hxbd] with y hy hybd
    rw [hy, hpc.carrierEq, mem_union]
    exact ⟨Or.inl, fun h => h.resolve_right hybd⟩

end DifferentialGeometry.Topology.PiecewiseLinear
