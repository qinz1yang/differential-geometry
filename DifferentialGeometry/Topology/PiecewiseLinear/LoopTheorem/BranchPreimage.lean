import DifferentialGeometry.Topology.PiecewiseLinear.ChartPolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePartition
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringLift
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DoublePointCover
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldComponents
import DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalCycles
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.Covering.SimplyConnectedCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

theorem branchCarrier_isCompact
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsCompact (T.branchCarrier c) :=
  (T.branchPieceIn c).isCompact

end NormalSingularSetTriangulation

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

private noncomputable def euclideanBoundaryComplexModel (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) :=
  boundaryComplex 1 K

private noncomputable def classicalEuclideanBoundaryComplexModel (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) :=
  @boundaryComplex (EuclideanSpace ℝ (Fin n)) _ _ (Classical.decEq _) 1 K

private theorem euclideanBoundaryComplexModel_eq_classical
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) :
    euclideanBoundaryComplexModel n K = classicalEuclideanBoundaryComplexModel n K := by
  unfold euclideanBoundaryComplexModel classicalEuclideanBoundaryComplexModel
  exact congrArg
    (fun d : DecidableEq (EuclideanSpace ℝ (Fin n)) =>
      @boundaryComplex (EuclideanSpace ℝ (Fin n)) _ _ d 1 K)
    (Subsingleton.elim _ _)

open Classical in
private theorem mem_boundaryComplex_source_iff_of_isPLHomeomorphOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (hK : IsCombinatorialManifoldWithBoundary 1 K)
    {f : E → F} (hf : IsPLHomeomorphOn f K.space L.space) {x : E} (hx : x ∈ K.space) :
    x ∈ (boundaryComplex 1 K).space ↔ f x ∈ (boundaryComplex 1 L).space :=
  (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn
    (n := 0) K L hK hf hx).symm

open Classical in
private theorem mem_boundaryComplex_faceStar_iff_of_isSubdivision
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) (hR : IsSubdivision R K)
    {x : E} (hx : {x} ∈ R.faces) (hopen : x ∈ openSimplex ({x} : Finset E)) :
    x ∈ (boundaryComplex 1 (faceStarComplex R ({x} : Finset E))).space ↔
      x ∈ (boundaryComplex 1 K).space := by
  exact (mem_boundaryComplex_faceStarComplex_space_iff
    (n := 0) R (hK.of_isSubdivision hR) hx hopen).trans (by
      rw [boundaryComplex_space_of_isSubdivision (n := 0) K R hK hR])

private theorem isPLSphere_or_exists_two_isPLSpheres_of_component_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} (hPcompact : IsCompact P) {C : Set (Set E)} (hCfinite : C.Finite)
    (hCsphere : ∀ S ∈ C, IsPLSphere 1 S) (hCdisjoint : C.PairwiseDisjoint id)
    (hcover : P = ⋃₀ C)
    (hsplit : ConnectedSpace P ∨
      ∃ x y : P, Disjoint (connectedComponent x) (connectedComponent y) ∧
        connectedComponent x ∪ connectedComponent y = univ) :
    IsPLSphere 1 P ∨
      ∃ S T : Set E, IsPLSphere 1 S ∧ IsPLSphere 1 T ∧
        Disjoint S T ∧ P = S ∪ T := by
  rcases hsplit with hconnected | ⟨x, y, hxy, hcomponents⟩
  · apply Or.inl
    rw [hcover]
    apply (isPLSphere_one_sUnion_iff_isConnected hCfinite hCsphere hCdisjoint).mpr
    rw [← hcover]
    exact isConnected_iff_connectedSpace.mpr hconnected
  · let _ : CompactSpace P := isCompact_iff_compactSpace.mp hPcompact
    let S : Set E := ((↑) : P → E) '' connectedComponent x
    let T : Set E := ((↑) : P → E) '' connectedComponent y
    have hSconnected : IsConnected S :=
      isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn
    have hTconnected : IsConnected T :=
      isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn
    have hSclosed : IsClosed S :=
      (isClosed_connectedComponent.isCompact.image continuous_subtype_val).isClosed
    have hTclosed : IsClosed T :=
      (isClosed_connectedComponent.isCompact.image continuous_subtype_val).isClosed
    have hSne : S.Nonempty := ⟨x, ⟨x, mem_connectedComponent, rfl⟩⟩
    have hTne : T.Nonempty := ⟨y, ⟨y, mem_connectedComponent, rfl⟩⟩
    have hSTdisjoint : Disjoint S T :=
      (Set.disjoint_image_iff Subtype.val_injective).mpr hxy
    have hSTcover : S ∪ T = P := by
      apply Subset.antisymm
      · rintro z (hz | hz)
        · obtain ⟨w, -, rfl⟩ := hz
          exact w.2
        · obtain ⟨w, -, rfl⟩ := hz
          exact w.2
      · intro z hz
        let w : P := ⟨z, hz⟩
        have hw : w ∈ connectedComponent x ∪ connectedComponent y := by
          rw [hcomponents]
          exact mem_univ w
        rcases hw with hw | hw
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
    have hSsub : S ⊆ ⋃₀ C := by
      intro z hz
      rw [← hcover]
      exact hSTcover.subset (Or.inl hz)
    have hTsub : T ⊆ ⋃₀ C := by
      intro z hz
      rw [← hcover]
      exact hSTcover.subset (Or.inr hz)
    obtain ⟨S', ⟨hS'C, hSS'⟩, -⟩ :=
      existsUnique_subset_of_isConnected_of_finite_closed_partition hSconnected hCfinite
        (fun U hU => (hCsphere U hU).isPolyhedron.isClosed) hCdisjoint hSsub
    obtain ⟨T', ⟨hT'C, hTT'⟩, -⟩ :=
      existsUnique_subset_of_isConnected_of_finite_closed_partition hTconnected hCfinite
        (fun U hU => (hCsphere U hU).isPolyhedron.isClosed) hCdisjoint hTsub
    have hS'sub : S' ⊆ S := by
      have hS'cover : S' ⊆ S ∪ T := by
        rw [hSTcover, hcover]
        exact subset_sUnion_of_mem hS'C
      rcases subset_or_subset_of_isPreconnected_of_isClosed
          (hCsphere S' hS'C).isConnected_one.isPreconnected
          hSclosed hTclosed hSTdisjoint hS'cover with hS'S | hS'T
      · exact hS'S
      · obtain ⟨z, hz⟩ := hSne
        exact False.elim (Set.disjoint_left.mp hSTdisjoint hz (hS'T (hSS' hz)))
    have hT'sub : T' ⊆ T := by
      have hT'cover : T' ⊆ S ∪ T := by
        rw [hSTcover, hcover]
        exact subset_sUnion_of_mem hT'C
      rcases subset_or_subset_of_isPreconnected_of_isClosed
          (hCsphere T' hT'C).isConnected_one.isPreconnected
          hSclosed hTclosed hSTdisjoint hT'cover with hT'S | hT'T
      · obtain ⟨z, hz⟩ := hTne
        exact False.elim (Set.disjoint_left.mp hSTdisjoint (hT'S (hTT' hz)) hz)
      · exact hT'T
    have hSeq : S = S' := Subset.antisymm hSS' hS'sub
    have hTeq : T = T' := Subset.antisymm hTT' hT'sub
    refine Or.inr ⟨S, T, ?_, ?_, hSTdisjoint, hSTcover.symm⟩
    · rw [hSeq]
      exact hCsphere S' hS'C
    · rw [hTeq]
      exact hCsphere T' hT'C

def branchPreimage (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) : Set (EuclideanSpace ℝ (Fin 2)) :=
  D.domain ∩ D ⁻¹' hD.singularSet.branchCarrier c

noncomputable def branchCoordinate (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) :
    EuclideanSpace ℝ (Fin 2) →
      EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim) :=
  Function.invFunOn (hD.singularSet.branchPieceIn c).map
    (hD.singularSet.branchPieceIn c).complex.space ∘ D

open Classical in
theorem branchCoordinate_mem
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ hD.branchPreimage c) :
    hD.branchCoordinate c x ∈ (hD.singularSet.branchComplex c).space := by
  exact (hD.singularSet.branchPieceIn c).bijOn.surjOn.mapsTo_invFunOn hx.2

open Classical in
theorem branchPieceIn_map_branchCoordinate
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ hD.branchPreimage c) :
    (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c x) = D x := by
  exact (hD.singularSet.branchPieceIn c).bijOn.invOn_invFunOn.2 hx.2

noncomputable def branchProjection
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    hD.branchPreimage c → (hD.singularSet.branchComplex c).space :=
  fun x => ⟨hD.branchCoordinate c x, hD.branchCoordinate_mem c x.2⟩

def branchPreimageCoverHomeomorph
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    hD.branchPreimage c ≃ₜ
      ((doublePointProjection D D.domain) ⁻¹' hD.singularSet.branchSet c) where
  toFun x :=
    ⟨⟨x, ⟨x.2.1,
      hD.singularSet.branchCarrier_subset_doublePointSet c x.2.2⟩⟩, x.2.2⟩
  invFun x := ⟨x.1, ⟨x.1.2.1, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    exact (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

noncomputable def branchComplexBranchSetHomeomorph [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    (hD.singularSet.branchComplex c).space ≃ₜ hD.singularSet.branchSet c := by
  let f : (hD.singularSet.branchComplex c).space → hD.singularSet.branchSet c :=
    fun x =>
      ⟨⟨(hD.singularSet.branchPieceIn c).map x,
        hD.singularSet.branchCarrier_subset_doublePointSet c
          ((hD.singularSet.branchPieceIn c).bijOn.mapsTo x.2)⟩,
        (hD.singularSet.branchPieceIn c).bijOn.mapsTo x.2⟩
  have hfbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply (hD.singularSet.branchPieceIn c).bijOn.injOn x.2 y.2
      exact congrArg (fun z : hD.singularSet.branchSet c => (z : M)) hxy
    · intro y
      obtain ⟨x, hx, hxy⟩ :=
        (hD.singularSet.branchPieceIn c).bijOn.surjOn y.2
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hxy
  let e : (hD.singularSet.branchComplex c).space ≃
      hD.singularSet.branchSet c := Equiv.ofBijective f hfbij
  have hfcont : Continuous f := by
    exact ((continuousOn_iff_continuous_domRestrict.mp
      (hD.singularSet.branchPieceIn c).continuousOn).subtype_mk _).subtype_mk _
  let _ : CompactSpace (hD.singularSet.branchComplex c).space :=
    isCompact_iff_compactSpace.mp
      (hD.singularSet.branchComplex_space_isPolyhedron c).isCompact
  exact e.toHomeomorphOfContinuousClosed hfcont hfcont.isClosedMap

open Classical in
theorem branchComplexBranchSetHomeomorph_symm_coe [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    (y : hD.singularSet.branchSet c) :
    ((hD.branchComplexBranchSetHomeomorph c).symm y :
      EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim)) =
      Function.invFunOn (hD.singularSet.branchPieceIn c).map
        (hD.singularSet.branchPieceIn c).complex.space (y : M) := by
  apply (hD.singularSet.branchPieceIn c).bijOn.injOn
  · exact (hD.branchComplexBranchSetHomeomorph c).symm y |>.2
  · exact (hD.singularSet.branchPieceIn c).bijOn.surjOn.mapsTo_invFunOn y.2
  · calc
      (hD.singularSet.branchPieceIn c).map
          ((hD.branchComplexBranchSetHomeomorph c).symm y) = (y : M) := by
        exact congrArg (fun z : hD.singularSet.branchSet c => (z : M))
          ((hD.branchComplexBranchSetHomeomorph c).apply_symm_apply y)
      _ = (hD.singularSet.branchPieceIn c).map
          (Function.invFunOn (hD.singularSet.branchPieceIn c).map
            (hD.singularSet.branchPieceIn c).complex.space (y : M)) :=
        ((hD.singularSet.branchPieceIn c).bijOn.invOn_invFunOn.2 y.2).symm

open Classical in
theorem branchProjection_isLocalHomeomorph [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    IsLocalHomeomorph (hD.branchProjection c) := by
  let J := hD.singularSet.branchSet c
  let p := doublePointProjection D D.domain
  let eSource := hD.branchPreimageCoverHomeomorph c
  let eTarget := hD.branchComplexBranchSetHomeomorph c
  have hlocal : IsLocalHomeomorph
      (eTarget.symm ∘ J.restrictPreimage p ∘ eSource) :=
    eTarget.symm.isLocalHomeomorph.comp
      ((hD.doublePointProjection_isCoveringMap.restrictPreimage J).isLocalHomeomorph.comp
        eSource.isLocalHomeomorph)
  have heq : hD.branchProjection c =
      eTarget.symm ∘ J.restrictPreimage p ∘ eSource := by
    funext x
    apply Subtype.ext
    exact (hD.branchComplexBranchSetHomeomorph_symm_coe c
      (J.restrictPreimage p (eSource x))).symm
  rw [heq]
  exact hlocal

open Classical in
theorem branchCoordinate_isPiecewiseAffineOn
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    IsPiecewiseAffineOn (hD.branchCoordinate c) (hD.branchPreimage c) := by
  exact (hD.singularSet.branchPieceIn c).isPiecewiseAffineOn_invFunOn_comp D.isPLOn

open Classical in
theorem injOn_affineMap_of_eqOn_branchCoordinate
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    {s : Finset (EuclideanSpace ℝ (Fin 2))}
    {A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ]
      EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim)}
    (hsub : convexHull ℝ (s : Set _) ⊆ hD.branchPreimage c)
    (hA : EqOn (hD.branchCoordinate c) A (convexHull ℝ (s : Set _))) :
    InjOn A (convexHull ℝ (s : Set _)) := by
  intro x hx y hy hAxy
  by_contra hxy
  let z := midpoint ℝ x y
  have hz : z ∈ convexHull ℝ (s : Set _) := by
    change midpoint ℝ x y ∈ convexHull ℝ (s : Set _)
    exact (convex_convexHull ℝ
      (s : Set (EuclideanSpace ℝ (Fin 2)))).midpoint_mem hx hy
  have hxz : x ≠ z := by
    intro hxz
    apply hxy
    exact (left_eq_midpoint_iff (R := ℝ)).mp (by simpa only [z] using hxz)
  have hyz : y ≠ z := by
    intro hyz
    apply hxy
    exact (right_eq_midpoint_iff (R := ℝ)).mp (by simpa only [z] using hyz)
  have hAzx : A z = A x := by
    rw [show z = midpoint ℝ x y by rfl, A.map_midpoint, hAxy, midpoint_self]
  have hqxy : hD.branchCoordinate c x = hD.branchCoordinate c y :=
    (hA hx).trans (hAxy.trans (hA hy).symm)
  have hqzx : hD.branchCoordinate c z = hD.branchCoordinate c x :=
    (hA hz).trans (hAzx.trans (hA hx).symm)
  have hxP := hsub hx
  have hyP := hsub hy
  have hzP := hsub hz
  have hDxy : D x = D y := by
    calc
      D x = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c x) :=
        (hD.branchPieceIn_map_branchCoordinate c hxP).symm
      _ = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c y) :=
        congrArg (hD.singularSet.branchPieceIn c).map hqxy
      _ = D y := hD.branchPieceIn_map_branchCoordinate c hyP
  have hDzx : D z = D x := by
    calc
      D z = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c z) :=
        (hD.branchPieceIn_map_branchCoordinate c hzP).symm
      _ = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c x) :=
        congrArg (hD.singularSet.branchPieceIn c).map hqzx
      _ = D x := hD.branchPieceIn_map_branchCoordinate c hxP
  have hfiber : ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      D.domain ∩ D ⁻¹' {D x} := by
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨hxP.1, rfl⟩
    · exact ⟨hyP.1, hDxy.symm⟩
    · exact ⟨hzP.1, hDzx⟩
  have hbound := (encard_mono hfiber).trans (hD.fiber_le_two (D x))
  rw [encard_insert_of_notMem (by simp [hxy, hxz]), encard_pair hyz] at hbound
  norm_num at hbound

theorem branchPreimage_subset_doublePointPreimage
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    hD.branchPreimage c ⊆ doublePointPreimage D D.domain := by
  rintro x ⟨hxD, hx⟩
  exact ⟨hxD, hD.singularSet.branchCarrier_subset_doublePointSet c hx⟩

theorem branchPreimage_isCompact [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    IsCompact (hD.branchPreimage c) := by
  have hDcompact : IsCompact D.domain := D.isPLBall_domain.isPolyhedron.isCompact
  have hDclosed : IsClosed D.domain := hDcompact.isClosed
  have hcarrierclosed : IsClosed (hD.singularSet.branchCarrier c) :=
    (hD.singularSet.branchCarrier_isCompact c).isClosed
  have hpreimageclosed : IsClosed (hD.branchPreimage c) :=
    D.continuousOn.preimage_isClosed_of_isClosed hDclosed hcarrierclosed
  exact hDcompact.of_isClosed_subset hpreimageclosed inter_subset_left

theorem branchProjection_isCoveringMap [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    IsCoveringMap (hD.branchProjection c) := by
  let _ : CompactSpace (hD.branchPreimage c) :=
    isCompact_iff_compactSpace.mp (hD.branchPreimage_isCompact c)
  exact isLocalHomeomorph_iff_isCoveringMap.mp (hD.branchProjection_isLocalHomeomorph c)

theorem branchProjection_isClosedMap [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    IsClosedMap (hD.branchProjection c) := by
  let _ : CompactSpace (hD.branchPreimage c) :=
    isCompact_iff_compactSpace.mp (hD.branchPreimage_isCompact c)
  exact (hD.branchProjection_isCoveringMap c).continuous.isClosedMap

theorem branchProjection_fiber_encard_eq_two
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    (y : (hD.singularSet.branchComplex c).space) :
    ((hD.branchProjection c) ⁻¹' {y}).encard = 2 := by
  let P := hD.branchPreimage c
  let fiber : Set P := (hD.branchProjection c) ⁻¹' {y}
  have himage : ((↑) : P → EuclideanSpace ℝ (Fin 2)) '' fiber =
      D.domain ∩ D ⁻¹' {(hD.singularSet.branchPieceIn c).map y} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hpzy : hD.branchProjection c z = y := hz
      refine ⟨z.2.1, ?_⟩
      calc
        D z = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c z) :=
          (hD.branchPieceIn_map_branchCoordinate c z.2).symm
        _ = (hD.singularSet.branchPieceIn c).map y :=
          congrArg (hD.singularSet.branchPieceIn c).map (congrArg Subtype.val hpzy)
    · rintro ⟨hxD, hDxy⟩
      have hycarrier :
          (hD.singularSet.branchPieceIn c).map y ∈ hD.singularSet.branchCarrier c :=
        (hD.singularSet.branchPieceIn c).bijOn.mapsTo y.2
      have hxcarrier : D x ∈ hD.singularSet.branchCarrier c := by
        rw [hDxy]
        exact hycarrier
      have hxP : x ∈ P := ⟨hxD, hxcarrier⟩
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      apply Subtype.ext
      apply (hD.singularSet.branchPieceIn c).bijOn.injOn
      · exact hD.branchCoordinate_mem c hxP
      · exact y.2
      · exact (hD.branchPieceIn_map_branchCoordinate c hxP).trans hDxy
  have hyDouble :
      (hD.singularSet.branchPieceIn c).map y ∈ doublePointSet D D.domain :=
    hD.singularSet.branchCarrier_subset_doublePointSet c
      ((hD.singularSet.branchPieceIn c).bijOn.mapsTo y.2)
  calc
    fiber.encard = (((↑) : P → EuclideanSpace ℝ (Fin 2)) '' fiber).encard :=
      (Subtype.val_injective.encard_image fiber).symm
    _ = (D.domain ∩ D ⁻¹' {(hD.singularSet.branchPieceIn c).map y}).encard :=
      congrArg Set.encard himage
    _ = 2 := hD.fiber_encard_eq_two hyDouble

open Classical in
theorem branchProjection_connected_or_two_components [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    ConnectedSpace (hD.branchPreimage c) ∨
      ∃ x y : hD.branchPreimage c,
        Disjoint (connectedComponent x) (connectedComponent y) ∧
        connectedComponent x ∪ connectedComponent y = univ ∧
        (∃ e : connectedComponent x ≃ₜ (hD.singularSet.branchComplex c).space,
          ∀ z : connectedComponent x, e z = hD.branchProjection c z) ∧
        ∃ e : connectedComponent y ≃ₜ (hD.singularSet.branchComplex c).space,
          ∀ z : connectedComponent y, e z = hD.branchProjection c z := by
  let L := hD.singularSet.branchComplex c
  let _ : ConnectedSpace L.space :=
    Subtype.connectedSpace (hD.singularSet.branchComplex_space_isConnected c)
  let y : L.space := Classical.arbitrary L.space
  obtain ⟨a, b, -, -⟩ := encard_eq_two.mp (hD.branchProjection_fiber_encard_eq_two c y)
  let _ : Nonempty (hD.branchPreimage c) := ⟨a⟩
  exact DifferentialGeometry.Topology.Covering.connectedSpace_or_exists_exactly_two_components
    (hD.branchProjection_isCoveringMap c) (hD.branchProjection_isClosedMap c)
      (hD.branchProjection_fiber_encard_eq_two c)

open Classical in
theorem branchPreimage_isPolyhedron [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    IsPolyhedron (hD.branchPreimage c) :=
  (hD.singularSet.branchPieceIn c).isPolyhedron_inter_preimage_of_isCompact
    D.isPLOn (hD.branchPreimage_isCompact c)

open Classical in
theorem exists_local_branchPreimage_manifold [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ hD.branchPreimage c) :
    ∃ H : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
      H.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 H ∧ x ∈ H.space ∧
        (∀ᶠ z in 𝓝 x, z ∈ hD.branchPreimage c ↔ z ∈ H.space) ∧
        (x ∈ (boundaryComplex 1 H).space ↔
          hD.branchCoordinate c x ∈
            (boundaryComplex 1 (hD.singularSet.branchComplex c)).space) := by
  let P := hD.branchPreimage c
  let L := hD.singularSet.branchComplex c
  let f := hD.branchCoordinate c
  let px : P := ⟨x, hx⟩
  let y := f x
  have hy : y ∈ L.space := hD.branchCoordinate_mem c hx
  obtain ⟨ι, hι, C₀, A, hC₀, hC₀nhds⟩ :=
    hD.branchCoordinate_isPiecewiseAffineOn c x hx
  obtain ⟨U, hU, hDinj⟩ := hD.locallyInjective x hx.1
  obtain ⟨O, hO, hOU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU
  obtain ⟨Q, hQpoly, hQO, hQnhds⟩ := exists_isHPolytope_subset_mem_nhds hO
  let C := (⋃ i, C₀ i) ∩ Q
  have hCpoly : IsPolyhedron C :=
    (IsPolyhedron.iUnion fun i => (hC₀ i).1.isPolyhedron).inter hQpoly.isPolyhedron
  have hCsubP : C ⊆ P := by
    rintro z ⟨hz, -⟩
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
    exact (hC₀ i).2.1 hzi
  have hCsubU : C ⊆ U := by
    intro z hz
    exact hOU ⟨hQO hz.2, (hCsubP hz).1⟩
  have hCnhds : C ∈ 𝓝[P] x :=
    Filter.inter_mem hC₀nhds (mem_nhdsWithin_of_mem_nhds hQnhds)
  have hfC : IsPiecewiseAffineOn f C :=
    (hD.branchCoordinate_isPiecewiseAffineOn c).mono_of_isPolyhedron hCpoly hCsubP
  have hfinj : InjOn f C := by
    intro a ha b hb hab
    apply hDinj (hCsubU ha) (hCsubU hb)
    calc
      D a = (hD.singularSet.branchPieceIn c).map (f a) :=
        (hD.branchPieceIn_map_branchCoordinate c (hCsubP ha)).symm
      _ = (hD.singularSet.branchPieceIn c).map (f b) := congrArg _ hab
      _ = D b := hD.branchPieceIn_map_branchCoordinate c (hCsubP hb)
  have hCpl : IsPLHomeomorphOn f C (f '' C) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hCpoly hfC hfinj.bijOn_image
  have hsourceNhds : ((↑) : P → EuclideanSpace ℝ (Fin 2)) ⁻¹' C ∈ 𝓝 px :=
    preimage_coe_mem_nhds_subtype.mpr hCnhds
  have himageNhds :=
    (hD.branchProjection_isLocalHomeomorph c).isOpenMap.image_mem_nhds hsourceNhds
  have himageEq : hD.branchProjection c ''
      (((↑) : P → EuclideanSpace ℝ (Fin 2)) ⁻¹' C) =
        ((↑) : L.space → EuclideanSpace ℝ
          (Fin hD.singularSet.piece.ambientDim)) ⁻¹' (f '' C) := by
    ext z
    constructor
    · rintro ⟨w, hwC, rfl⟩
      exact ⟨w, hwC, rfl⟩
    · rintro ⟨w, hwC, hwz⟩
      have hwP : w ∈ P := hCsubP hwC
      refine ⟨⟨w, hwP⟩, hwC, ?_⟩
      apply Subtype.ext
      change f w = z
      exact hwz
  rw [himageEq] at himageNhds
  have hImageWithin : f '' C ∈ 𝓝[L.space] y :=
    preimage_coe_mem_nhds_subtype.mp himageNhds
  obtain ⟨V, hV, hVsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hImageWithin
  let _ : Finite L.faces :=
    (hD.singularSet.branchComplex_faces_finite c).to_subtype
  obtain ⟨R, hR, hRfinite, hyR, hstarV⟩ :=
    exists_isSubdivision_closedStar_subset_of_mem_nhds L hy hV
  let _ : Finite R.faces := hRfinite.to_subtype
  have hstarSub : closedStar R y ⊆ f '' C := by
    intro z hz
    apply hVsub
    refine ⟨hstarV hz, ?_⟩
    rw [← hR.space_eq]
    exact closedStar_subset_space R y hz
  have hyOpen : y ∈ openSimplex ({y} : Finset _) := mem_openSimplex_singleton y
  have hstarBall : IsPLBall 1 (closedStar R y) := by
    have hball :=
      (hD.singularSet.branchComplex_isManifoldWithBoundary c).of_isSubdivision hR
        |>.isPLBall_faceStarComplex R hyR
    rwa [faceStarComplex_space R hyR hyOpen] at hball
  let S := C ∩ f ⁻¹' closedStar R y
  have hSpoly : IsPolyhedron S := hCpl.isPolyhedron_preimage hstarBall.isPolyhedron hstarSub
  have himageS : f '' S = closedStar R y := by
    apply Subset.antisymm
    · rintro z ⟨w, hw, rfl⟩
      exact hw.2
    · intro z hz
      obtain ⟨w, hwC, hwz⟩ := hstarSub hz
      refine ⟨w, ⟨hwC, ?_⟩, hwz⟩
      change f w ∈ closedStar R y
      rw [hwz]
      exact hz
  have hSpl : IsPLHomeomorphOn f S (closedStar R y) := by
    have h := hCpl.restrict hSpoly inter_subset_left
    rwa [himageS] at h
  have hSball : IsPLBall 1 S := hstarBall.of_isPLHomeomorphOn hSpl.symm
  obtain ⟨H, hHfinite, hHspace⟩ := hSpoly.exists_simplicialComplex
  let _ : Finite H.faces := hHfinite.to_subtype
  have hHman : IsCombinatorialManifoldWithBoundary 1 H := by
    apply IsPLBall.isCombinatorialManifoldWithBoundary (n := 0) (K := H)
    rw [hHspace]
    exact hSball
  have hxC : x ∈ C := mem_of_mem_nhdsWithin hx hCnhds
  have hxS : x ∈ S := ⟨hxC, mem_closedStar_self R hyR⟩
  have hstarWithin : closedStar R y ∈ 𝓝[L.space] y := by
    rw [← hR.space_eq]
    exact closedStar_mem_nhdsWithin R y
  have htargetNhds :
      ((↑) : L.space → EuclideanSpace ℝ
        (Fin hD.singularSet.piece.ambientDim)) ⁻¹' closedStar R y ∈
          𝓝 (hD.branchProjection c px) :=
    preimage_coe_mem_nhds_subtype.mpr hstarWithin
  have hpreimageNhds :=
    (hD.branchProjection_isLocalHomeomorph c).continuous.continuousAt htargetNhds
  change (hD.branchProjection c) ⁻¹'
      (((↑) : L.space → EuclideanSpace ℝ
        (Fin hD.singularSet.piece.ambientDim)) ⁻¹' closedStar R y) ∈ 𝓝 px at hpreimageNhds
  have hpreimageEq : (hD.branchProjection c) ⁻¹'
      (((↑) : L.space → EuclideanSpace ℝ
        (Fin hD.singularSet.piece.ambientDim)) ⁻¹' closedStar R y) =
        ((↑) : P → EuclideanSpace ℝ (Fin 2)) ⁻¹' (f ⁻¹' closedStar R y) := by
    rfl
  rw [hpreimageEq] at hpreimageNhds
  have hpreimageWithin : f ⁻¹' closedStar R y ∈ 𝓝[P] x :=
    preimage_coe_mem_nhds_subtype.mp hpreimageNhds
  have hSnhds : S ∈ 𝓝[P] x := Filter.inter_mem hCnhds hpreimageWithin
  obtain ⟨W, hW, hWsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hSnhds
  have hxH : x ∈ H.space := hHspace ▸ hxS
  let T := faceStarComplex R ({y} : Finset _)
  let _ : Finite T.faces := (faceStarComplex_faces_finite R ({y} : Finset _)).to_subtype
  have hTspace : T.space = closedStar R y := faceStarComplex_space R hyR hyOpen
  have hSplHT : IsPLHomeomorphOn f H.space T.space := by
    rw [hHspace, hTspace]
    exact hSpl
  have hboundary :
      x ∈ (boundaryComplex 1 H).space ↔
        f x ∈ (boundaryComplex 1 L).space := by
    change x ∈ (euclideanBoundaryComplexModel 2 H).space ↔
      f x ∈ (euclideanBoundaryComplexModel hD.singularSet.piece.ambientDim L).space
    rw [euclideanBoundaryComplexModel_eq_classical,
      euclideanBoundaryComplexModel_eq_classical]
    have hmap :
        x ∈ (classicalEuclideanBoundaryComplexModel 2 H).space ↔
          f x ∈
            (classicalEuclideanBoundaryComplexModel
              hD.singularSet.piece.ambientDim T).space := by
      exact mem_boundaryComplex_source_iff_of_isPLHomeomorphOn H T hHman hSplHT hxH
    have htarget :
        f x ∈
            (classicalEuclideanBoundaryComplexModel
              hD.singularSet.piece.ambientDim T).space ↔
          f x ∈
            (classicalEuclideanBoundaryComplexModel
              hD.singularSet.piece.ambientDim L).space := by
      simpa only [T, y, classicalEuclideanBoundaryComplexModel] using
        (mem_boundaryComplex_faceStar_iff_of_isSubdivision L R
          (hD.singularSet.branchComplex_isManifoldWithBoundary c) hR hyR hyOpen)
    exact hmap.trans htarget
  refine ⟨H, hHfinite, hHman, hxH, ?_, hboundary⟩
  filter_upwards [hW] with z hzW
  rw [hHspace]
  constructor
  · exact fun hzP => hWsub ⟨hzW, hzP⟩
  · exact fun hzS => hCsubP hzS.1

open Classical in
theorem exists_branchPreimage_simplicialComplex [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
      K.faces.Finite ∧ K.space = hD.branchPreimage c ∧
        ∀ s ∈ K.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ]
            EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim),
          EqOn (hD.branchCoordinate c) A (convexHull ℝ (s : Set _)) := by
  obtain ⟨K, hKfinite, hKspace⟩ := (hD.branchPreimage_isPolyhedron c).exists_simplicialComplex
  let _ : Finite K.faces := hKfinite.to_subtype
  have hcoordinate : IsPiecewiseAffineOn (hD.branchCoordinate c) K.space := by
    rw [hKspace]
    exact hD.branchCoordinate_isPiecewiseAffineOn c
  obtain ⟨K', hsub, hfinite, haffine⟩ :=
    hcoordinate.exists_isSubdivision_affineOn_faces K
  exact ⟨K', hfinite, hsub.space_eq.trans hKspace, haffine⟩

open Classical in
theorem exists_branchPreimage_simplicialComplex_aligned [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
      K.faces.Finite ∧ K.space = hD.branchPreimage c ∧
        (∀ s ∈ K.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ]
            EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim),
          EqOn (hD.branchCoordinate c) A (convexHull ℝ (s : Set _))) ∧
        ∀ s ∈ K.faces, ∃ t ∈ (hD.singularSet.branchComplex c).faces,
          MapsTo (hD.branchCoordinate c) (convexHull ℝ (s : Set _))
            (convexHull ℝ (t : Set _)) := by
  obtain ⟨K, hKfinite, hKspace, hKaffine⟩ := hD.exists_branchPreimage_simplicialComplex c
  let _ : Finite K.faces := hKfinite.to_subtype
  let _ : Finite (hD.singularSet.branchComplex c).faces :=
    (hD.singularSet.branchComplex_faces_finite c).to_subtype
  let Q : (hD.singularSet.branchComplex c).faces → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun t => K.space ∩ (hD.branchCoordinate c) ⁻¹'
      convexHull ℝ (↑t.1 : Set
        (EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim)))
  have hcoordinate : IsPiecewiseAffineOn (hD.branchCoordinate c) K.space := by
    rw [hKspace]
    exact hD.branchCoordinate_isPiecewiseAffineOn c
  have hQpoly : ∀ t, IsPolyhedron (Q t) := by
    intro t
    have htpoly : IsHPolytope
        (convexHull ℝ (↑t.1 : Set
          (EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim)))) :=
      isHPolytope_convexHull_of_affineIndependent _
        ((hD.singularSet.branchComplex c).indep t.2)
    have hKcompact : IsCompact K.space := (isPolyhedron_space K).isCompact
    have hKclosed : IsClosed K.space := hKcompact.isClosed
    have hQclosed : IsClosed (Q t) :=
      hcoordinate.continuousOn.preimage_isClosed_of_isClosed hKclosed htpoly.isClosed
    exact isPolyhedron_inter_preimage_of_isCompact hcoordinate htpoly
      (hKcompact.of_isClosed_subset hQclosed inter_subset_left)
  have hQsub : ∀ t, Q t ⊆ K.space := fun _ => inter_subset_left
  obtain ⟨R, hR, hRfinite, hQunion⟩ :=
    exists_isSubdivision_subcomplexes K Q hQpoly hQsub
  refine ⟨R, hRfinite, hR.space_eq.trans hKspace, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := hR.exists_face_subset hs
    obtain ⟨A, hA⟩ := hKaffine t ht
    exact ⟨A, hA.mono hst⟩
  · intro s hs
    have hcent : s.centroid ℝ id ∈ openSimplex s :=
      centroid_mem_openSimplex (R.nonempty_of_mem_faces hs)
    have hcentR : s.centroid ℝ id ∈ R.space :=
      R.convexHull_subset_space hs (openSimplex_subset_convexHull s hcent)
    have hcentK : s.centroid ℝ id ∈ K.space := hR.space_eq ▸ hcentR
    have hcentP : s.centroid ℝ id ∈ hD.branchPreimage c := hKspace ▸ hcentK
    have hqcent := hD.branchCoordinate_mem c hcentP
    obtain ⟨t, ht, hqt⟩ := (hD.singularSet.branchComplex c).mem_space_iff.mp hqcent
    let t' : (hD.singularSet.branchComplex c).faces := ⟨t, ht⟩
    have hcentQ : s.centroid ℝ id ∈ Q t' := ⟨hcentK, hqt⟩
    rw [hQunion t'] at hcentQ
    obtain ⟨r, ⟨hr, hrQ⟩, hcentr⟩ := mem_iUnion₂.mp hcentQ
    have hsr : s ⊆ r :=
      face_subset_of_mem_openSimplex_of_mem_convexHull R hs hr hcent hcentr
    have hsQ : convexHull ℝ (s : Set _) ⊆ Q t' :=
      (convexHull_mono (Finset.coe_subset.mpr hsr)).trans hrQ
    exact ⟨t, ht, fun x hx => (hsQ hx).2⟩

open Classical in
theorem exists_branchPreimage_simplicialComplex_card_le_two [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
      K.faces.Finite ∧ K.space = hD.branchPreimage c ∧
        (∀ s ∈ K.faces, s.card ≤ 2) ∧
        (∀ s ∈ K.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ]
            EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim),
          EqOn (hD.branchCoordinate c) A (convexHull ℝ (s : Set _))) ∧
        ∀ s ∈ K.faces, ∃ t ∈ (hD.singularSet.branchComplex c).faces,
          MapsTo (hD.branchCoordinate c) (convexHull ℝ (s : Set _))
            (convexHull ℝ (t : Set _)) := by
  obtain ⟨K, hKfinite, hKspace, hKaffine, hKmaps⟩ :=
    hD.exists_branchPreimage_simplicialComplex_aligned c
  let _ : Finite (hD.singularSet.branchComplex c).faces :=
    (hD.singularSet.branchComplex_faces_finite c).to_subtype
  refine ⟨K, hKfinite, hKspace, ?_, hKaffine, hKmaps⟩
  intro s hs
  obtain ⟨A, hA⟩ := hKaffine s hs
  obtain ⟨t, ht, hmaps⟩ := hKmaps s hs
  have hsource : convexHull ℝ (s : Set _) ⊆ hD.branchPreimage c := by
    rw [← hKspace]
    exact K.convexHull_subset_space hs
  have hAinj := hD.injOn_affineMap_of_eqOn_branchCoordinate c hsource hA
  have himageIndependent :
      AffineIndependent ℝ ((↑) : {u // u ∈ s.image A} →
        EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim)) :=
    affineIndependent_image_of_injOn_convexHull A (K.indep hs) hAinj
  have himageSpan :
      (s.image A : Set (EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim))) ⊆
        ((affineSpan ℝ
          (t : Set (EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim)))) :
          Set (EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim))) := by
    intro y hy
    obtain ⟨x, hxs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    have hxconv : x ∈ convexHull ℝ (s : Set _) :=
      subset_convexHull ℝ _ (Finset.mem_coe.mpr hxs)
    have hxmap := hmaps hxconv
    rw [hA hxconv] at hxmap
    exact convexHull_subset_affineSpan _ hxmap
  have hcard : (s.image A).card ≤ t.card :=
    himageIndependent.card_le_card_of_subset_affineSpan himageSpan
  have himageCard : (s.image A).card = s.card :=
    Finset.card_image_iff.mpr (hAinj.mono (subset_convexHull ℝ _))
  rw [himageCard] at hcard
  exact hcard.trans ((hD.singularSet.branchComplex_isManifoldWithBoundary c).card_le _ ht)

open Classical in
theorem exists_branchPreimage_simplicialComplex_manifold [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
      K.faces.Finite ∧ K.space = hD.branchPreimage c ∧
        IsCombinatorialManifoldWithBoundary 1 K ∧
        (∀ s ∈ K.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ]
            EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim),
          EqOn (hD.branchCoordinate c) A (convexHull ℝ (s : Set _))) ∧
        ∀ s ∈ K.faces, ∃ t ∈ (hD.singularSet.branchComplex c).faces,
          MapsTo (hD.branchCoordinate c) (convexHull ℝ (s : Set _))
            (convexHull ℝ (t : Set _)) := by
  obtain ⟨K, hKfinite, hKspace, hKcard, hKaffine, hKmaps⟩ :=
    hD.exists_branchPreimage_simplicialComplex_card_le_two c
  let _ : Finite K.faces := hKfinite.to_subtype
  refine ⟨K, hKfinite, hKspace,
    isCombinatorialManifoldWithBoundary_one_of_locally_eq K hKcard ?_, hKaffine, hKmaps⟩
  intro x hx
  obtain ⟨H, hHfinite, hHman, hxH, heq, -⟩ :=
    hD.exists_local_branchPreimage_manifold c (hKspace ▸ hx)
  refine ⟨H, hHfinite, hHman, hxH, ?_⟩
  simpa only [hKspace] using heq

open Classical in
theorem exists_branchPreimage_simplicialComplex_manifold_of_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
      K.faces.Finite ∧ K.space = hD.branchPreimage c ∧
        IsCombinatorialManifold 1 K ∧
        (∀ s ∈ K.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ]
            EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim),
          EqOn (hD.branchCoordinate c) A (convexHull ℝ (s : Set _))) ∧
        ∀ s ∈ K.faces, ∃ t ∈ (hD.singularSet.branchComplex c).faces,
          MapsTo (hD.branchCoordinate c) (convexHull ℝ (s : Set _))
            (convexHull ℝ (t : Set _)) := by
  obtain ⟨K, hKfinite, hKspace, hKman, hKaffine, hKmaps⟩ :=
    hD.exists_branchPreimage_simplicialComplex_manifold c
  let _ : Finite K.faces := hKfinite.to_subtype
  let L := hD.singularSet.branchComplex c
  let _ : Finite L.faces := (hD.singularSet.branchComplex_faces_finite c).to_subtype
  have hLman : IsCombinatorialManifold 1 L :=
    hD.singularSet.branchComplex_isManifold hc
  refine ⟨K, hKfinite, hKspace, ?_, hKaffine, hKmaps⟩
  apply (isCombinatorialManifold_one_iff K).mpr
  refine ⟨fun s hs => hKman.card_le K hs, ?_⟩
  intro x hx
  have hxK : x ∈ K.space := K.convexHull_subset_space hx (by simp)
  obtain ⟨H, hHfinite, hHman, hxH, heq, hboundary⟩ :=
    hD.exists_local_branchPreimage_manifold c (hKspace ▸ hxK)
  let _ : Finite H.faces := hHfinite.to_subtype
  have hLboundaryFaces : (boundaryComplex 1 L).faces = ∅ := by
    change (euclideanBoundaryComplexModel hD.singularSet.piece.ambientDim L).faces = ∅
    rw [euclideanBoundaryComplexModel_eq_classical]
    exact hLman.boundaryComplex_faces_eq_empty L
  have hyNot : hD.branchCoordinate c x ∉ (boundaryComplex 1 L).space := by
    intro hy
    obtain ⟨s, hs, -⟩ := (boundaryComplex 1 L).mem_space_iff.mp hy
    rw [hLboundaryFaces] at hs
    exact hs
  have hxNotH : x ∉ (boundaryComplex 1 H).space :=
    fun hxB => hyNot (hboundary.mp hxB)
  obtain ⟨R, hR, hRfinite, hxR⟩ := exists_isSubdivision_singleton_mem H hxH
  let _ : Finite R.faces := hRfinite.to_subtype
  have hRman : IsCombinatorialManifoldWithBoundary 1 R := hHman.of_isSubdivision hR
  have hxNotR : x ∉ (boundaryComplex 1 R).space := by
    intro hxB
    apply hxNotH
    have hboundaryEq :
        (boundaryComplex 1 R).space = (boundaryComplex 1 H).space := by
      change (euclideanBoundaryComplexModel 2 R).space =
        (euclideanBoundaryComplexModel 2 H).space
      rw [euclideanBoundaryComplexModel_eq_classical,
        euclideanBoundaryComplexModel_eq_classical]
      exact boundaryComplex_space_of_isSubdivision H R hHman hR
    exact hboundaryEq ▸ hxB
  have heqR : ∀ᶠ z in 𝓝 x, z ∈ K.space ↔ z ∈ R.space := by
    filter_upwards [heq] with z hz
    rw [hKspace, hR.space_eq]
    exact hz
  rcases (isCombinatorialManifoldWithBoundary_one_iff R).mp hRman |>.2 x hxR with
    hsingle | hpair
  · exfalso
    apply hxNotR
    have hxBoundaryFace : {x} ∈ (boundaryComplex 1 R).faces := by
      change {x} ∈ (euclideanBoundaryComplexModel 2 R).faces
      rw [euclideanBoundaryComplexModel_eq_classical]
      apply (hRman.mem_boundaryComplex_iff_unique_coface
        (dE := Classical.decEq _) R (by simp)).mpr
      simpa only [Finset.mem_singleton, Finset.pair_comm] using hsingle
    exact (boundaryComplex 1 R).convexHull_subset_space hxBoundaryFace (by simp)
  · apply neighbors_eq_pair_of_eventually_eq K R
      (fun s hs => hKman.card_le K hs) (fun s hs => hRman.card_le R hs)
      hx hxR heqR hpair

open Classical in
theorem branchPreimage_isPLSphere_or_exists_two_isPLSpheres_of_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c) :
    IsPLSphere 1 (hD.branchPreimage c) ∨
      ∃ S T : Set (EuclideanSpace ℝ (Fin 2)),
        IsPLSphere 1 S ∧ IsPLSphere 1 T ∧ Disjoint S T ∧
          hD.branchPreimage c = S ∪ T := by
  obtain ⟨K, hKfinite, hKspace, hKman, -, -⟩ :=
    hD.exists_branchPreimage_simplicialComplex_manifold_of_not_boundaryBranch hc
  let _ : Finite K.faces := hKfinite.to_subtype
  obtain ⟨C, hCfinite, hCsphere, hCdisjoint, hCcover⟩ :=
    exists_finite_isPLSphere_decomposition K hKman
  have hsplit : ConnectedSpace (hD.branchPreimage c) ∨
      ∃ x y : hD.branchPreimage c,
        Disjoint (connectedComponent x) (connectedComponent y) ∧
          connectedComponent x ∪ connectedComponent y = univ := by
    rcases hD.branchProjection_connected_or_two_components c with hconnected | htwo
    · exact Or.inl hconnected
    · obtain ⟨x, y, hxy, hcover, -⟩ := htwo
      exact Or.inr ⟨x, y, hxy, hcover⟩
  exact isPLSphere_or_exists_two_isPLSpheres_of_component_split
    (hD.branchPreimage_isCompact c) hCfinite hCsphere hCdisjoint
      (hKspace.symm.trans hCcover) hsplit

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
