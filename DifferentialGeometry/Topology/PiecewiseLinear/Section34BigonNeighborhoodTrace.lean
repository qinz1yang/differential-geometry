import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodPolygon
import DifferentialGeometry.Topology.PiecewiseLinear.ArcSubset
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitBoundaryTrace
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem derivedNeighborhood_eq_restrict_core
    (K S B : Geometry.SimplicialComplex ℝ E)
    (hS : S.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces) :
    derivedNeighborhood S B = derivedNeighborhood S (restrict B S.space) := by
  ext u
  constructor
  · rintro ⟨D, hD, hne, hmeet, rfl⟩
    refine ⟨D, hD, hne, ?_, rfl⟩
    intro e he
    obtain ⟨s, hs, hse⟩ := hmeet e he
    have hcS : s.centroid ℝ id ∈ S.space :=
      (barycentricSubdivision_isSubdivision S).space_eq.subset
        ((barycentricSubdivision S).convexHull_subset_space (hD.mem_faces he)
          (subset_convexHull ℝ _ hse))
    have hsS : s ∈ S.faces :=
      mem_faces_of_mem_openSimplex_of_mem_space hS (hB hs)
        (centroid_mem_openSimplex (B.nonempty_of_mem_faces hs)) hcS
    exact ⟨s, ⟨hs, S.convexHull_subset_space hsS⟩, hse⟩
  · rintro ⟨D, hD, hne, hmeet, rfl⟩
    refine ⟨D, hD, hne, ?_, rfl⟩
    intro e he
    obtain ⟨s, hs, hse⟩ := hmeet e he
    exact ⟨s, hs.1, hse⟩

open Classical in
theorem derivedNeighborhood_inter_eq_neighborhood_restricted_core
    (K S B : Geometry.SimplicialComplex ℝ E)
    (hS : S.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces) :
    (derivedNeighborhood K B).space ∩ S.space =
      (derivedNeighborhood S (restrict B S.space)).space := by
  rw [derivedNeighborhood_space_inter_subcomplex K S B hS,
    derivedNeighborhood_eq_restrict_core K S B hS hB]

open Classical in
theorem IsPLSphere.isPLBall_inter_derivedNeighborhood_of_arc_core
    [FiniteDimensional ℝ E] (K S B : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hS : S.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces)
    (hcircle : IsPLSphere 1 S.space) (hcore : IsPLBall 1 (B.space ∩ S.space))
    (hproper : (derivedNeighborhood K B).space ∩ S.space ⊂ S.space) :
    IsPLBall 1 ((derivedNeighborhood K B).space ∩ S.space) := by
  have : Finite S.faces := (Set.toFinite K.faces |>.subset hS).to_subtype
  have : Finite B.faces := (Set.toFinite K.faces |>.subset hB).to_subtype
  let C := restrict B S.space
  have : Finite C.faces := (restrict_faces_finite B S.space).to_subtype
  have hCS : C.faces ⊆ S.faces := fun s hs =>
    ((mem_restrict_faces_iff_of_faces_subset K B S hB hS).mp hs).2
  have hC : C.space = B.space ∩ S.space :=
    restrict_space_eq_inter_of_faces_subset K B S hB hS
  have heq := derivedNeighborhood_inter_eq_neighborhood_restricted_core K S B hS hB
  have hconn : IsConnected ((derivedNeighborhood K B).space ∩ S.space) := by
    rw [heq]
    exact isConnected_derivedNeighborhood_space hCS (hC ▸ hcore.isConnected)
  have hsub : B.space ∩ S.space ⊆ (derivedNeighborhood K B).space ∩ S.space := by
    rw [heq, ← hC]
    exact subcomplex_space_subset_derivedNeighborhood hCS
  have : Finite (derivedNeighborhood K B).faces :=
    (derivedNeighborhood_faces_finite K B).to_subtype
  have hcompact : IsCompact ((derivedNeighborhood K B).space ∩ S.space) :=
    (isPolyhedron_space (derivedNeighborhood K B)).isCompact.inter_right
      hcircle.isPolyhedron.isClosed
  obtain ⟨A, hA, hNA, -⟩ :=
    hcircle.exists_isPLBall_one_superset_of_ssubset hcompact.isClosed hproper
  exact hA.isPLBall_one_of_isCompact_of_isConnected hcompact hconn
    (hcore.nontrivial.mono hsub) hNA

open Classical in
theorem IsCombinatorialManifold.derivedNeighborhood_crosscut_boundary
    [FiniteDimensional ℝ E] (K S B : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite S.faces]
    (hK : IsCombinatorialManifold 2 K) (hS : IsCombinatorialManifold 1 S)
    (hSK : S.faces ⊆ K.faces)
    {r : (Fin 3 → ℝ) → E} {q : (Fin 2 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (derivedNeighborhood K B).space)
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
      ((derivedNeighborhood K B).space ∩ S.space)) :
    ((derivedNeighborhood K B).space ∩ S.space) ∩ r '' stdSimplexBoundary 2 =
      q '' stdSimplexBoundary 1 := by
  have hQ : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
      (derivedNeighborhood S B).space := by
    rwa [derivedNeighborhood_space_inter_subcomplex K S B hSK] at hq
  have hbdN := hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr
    (derivedNeighborhood_space_subset K B)
  have hbdQ := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary S hQ
    (derivedNeighborhood_space_subset S B)
  rw [← hbdN, ← hbdQ,
    ← space_inter_closure_sdiff_derivedNeighborhood_eq K B S hSK,
    ← derivedNeighborhood_space_inter_subcomplex K S B hSK]
  ext x
  simp only [mem_inter_iff]
  tauto

theorem IsCombinatorialManifold.exists_disk_neighborhood_with_crosscuts
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {B Ω : Set E}
    (hB : IsPLBall 2 B) (hBK : B ⊆ K.space) (hΩ : IsOpen Ω) (hBΩ : B ⊆ Ω)
    {ι : Type*} [Finite ι] (J : ι → Set E)
    (hJ : ∀ i, IsPLSphere 1 (J i)) (hJK : ∀ i, J i ⊆ K.space)
    (hBJ : ∀ i, IsPLBall 1 (B ∩ J i)) :
    ∃ (N : Set E) (r : (Fin 3 → ℝ) → E) (q : ι → (Fin 2 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N ∧ N ⊆ K.space ∩ Ω ∧
      B ⊆ r '' openSimplex (stdVertices 1) ∧
      ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) (N ∩ J i) ∧
        (N ∩ J i) ∩ r '' stdSimplexBoundary 2 = q i '' stdSimplexBoundary 1 := by
  classical
  have hex : ∀ i, ∃ p, p ∈ J i ∧ p ∉ B := by
    intro i
    by_contra! hn
    have heq : B ∩ J i = J i := inter_eq_right.mpr hn
    exact (hJ i).not_isPLBall (heq ▸ hBJ i)
  choose p hpJ hpB using hex
  let W : Set E := Ω \ range p
  have hW : IsOpen W := hΩ.sdiff (finite_range p).isClosed
  have hBW : B ⊆ W := by
    intro x hx
    refine ⟨hBΩ hx, ?_⟩
    rintro ⟨i, rfl⟩
    exact hpB i hx
  let V : Bool → Set E
    | false => W
    | true => Bᶜ
  have hVo : ∀ i, IsOpen (((↑) : K.space → E) ⁻¹' V i) := by
    intro i
    cases i
    · exact hW.preimage continuous_subtype_val
    · exact hB.isPolyhedron.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hcover : K.space ⊆ ⋃ i, V i := by
    intro x _
    by_cases hx : x ∈ B
    · exact mem_iUnion.mpr ⟨false, hBW hx⟩
    · exact mem_iUnion.mpr ⟨true, hx⟩
  obtain ⟨R₀, hR₀, hR₀fin, hJ₀, hstars₀⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_cover K J
      (fun i => (hJ i).isPolyhedron) hJK V hVo hcover
  have : Finite R₀.faces := hR₀fin.to_subtype
  obtain ⟨R, A, T, φ, ψ, hR, hRfin, hAR, hAfin, hAB, hTfin, hT, hIso, -⟩ :=
    exists_isSubdivision_subcomplex_isGlueIso_planar R₀ hB
      (hBK.trans hR₀.space_eq.symm.subset)
  have : Finite R.faces := hRfin.to_subtype
  have : Finite A.faces := hAfin.to_subtype
  have : Finite T.faces := hTfin.to_subtype
  have hstarsR : ∀ s ∈ R.faces, ∃ i, (⋃ v ∈ s, closedStar R v) ⊆ V i :=
    hR.closedStars_subset_cover hstars₀
  have hstars₂ : ∀ s ∈ (PiecewiseLinear.secondDerived R).faces,
      ∃ i, (⋃ v ∈ s, closedStar (PiecewiseLinear.secondDerived R) v) ⊆ V i :=
    (secondDerived_isSubdivision R).closedStars_subset_cover hstarsR
  have hcellW (s : Finset E) (hs : s ∈ A.faces) :
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
      exact hi'
    · have hcentroidB : s.centroid ℝ id ∈ B :=
        hAB.subset (A.convexHull_subset_space hs
          (s.centroid_mem_convexHull (A.nonempty_of_mem_faces hs)))
      exact (hi' (mem_closedStar_self _ hc) hcentroidB).elim
  let N := derivedNeighborhood R A
  have hNW : N.space ⊆ W := by
    change (derivedNeighborhood R A).space ⊆ W
    rw [← iUnion_derivedNeighborhoodCell_space R A hAR]
    exact iUnion₂_subset hcellW
  have hRK := hR.trans hR₀
  have hNK : N.space ⊆ K.space :=
    (derivedNeighborhood_space_subset R A).trans hRK.space_eq.subset
  have hRM := hK.of_isSubdivision hRK
  have hNball : IsPLBall 2 N.space :=
    hRM.isCombinatorialManifoldWithBoundary
      |>.isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_in_surface hAR hT hIso
  obtain ⟨r, hr⟩ := hNball
  have hBint : B ⊆ r '' openSimplex (stdVertices 1) := by
    rw [hr.image_openSimplex_stdVertices]
    intro x hx
    have hnhds : N.space ∈ 𝓝[K.space] x := by
      have hn := derivedNeighborhood_mem_nhdsWithin hAR (hAB.symm.subset hx)
      rwa [hRK.space_eq] at hn
    refine ⟨mem_of_mem_nhdsWithin (hBK hx) hnhds, ?_⟩
    intro hxbd
    have hbd := hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hNK
    have hxcl := (hbd.superset hxbd).2
    obtain ⟨O, hO, hxO, hON⟩ := mem_nhdsWithin.mp hnhds
    obtain ⟨y, hyO, hy⟩ := mem_closure_iff_nhds.mp hxcl O (hO.mem_nhds hxO)
    exact hy.2 (hON ⟨hyO, hy.1⟩)
  have hcross : ∀ i, ∃ q : (Fin 2 → ℝ) → E,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) (N.space ∩ J i) ∧
        (N.space ∩ J i) ∩ r '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 1 := by
    intro i
    let S := restrict R (J i)
    have : Finite S.faces := (restrict_faces_finite R (J i)).to_subtype
    have hSR : S.faces ⊆ R.faces := restrict_faces_subset R (J i)
    have hS : S.space = J i := by
      have h := (hR.restrict (restrict R₀ (J i)) (restrict_faces_subset R₀ (J i))).space_eq
      rwa [hJ₀ i] at h
    have hsph : IsPLSphere 1 S.space := hS.symm ▸ hJ i
    have hcore : IsPLBall 1 (A.space ∩ S.space) := by
      rw [hAB, hS]
      exact hBJ i
    have hproper : N.space ∩ S.space ⊂ S.space := by
      refine ⟨inter_subset_right, ?_⟩
      intro h
      have hpN := (h (hS.symm.subset (hpJ i))).1
      exact (hNW hpN).2 (mem_range_self i)
    obtain ⟨q, hq⟩ := hsph.isPLBall_inter_derivedNeighborhood_of_arc_core R S A
      hSR hAR hcore hproper
    refine ⟨q, hS ▸ hq, ?_⟩
    have hbd := hRM.derivedNeighborhood_crosscut_boundary R S A
      hsph.isCombinatorialManifold hSR hr hq
    rwa [hS] at hbd
  choose q hq hbd using hcross
  exact ⟨N.space, r, q, hr, fun x hx => ⟨hNK hx, (hNW hx).1⟩,
    hBint, fun i => ⟨hq i, hbd i⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
