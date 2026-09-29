/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartPolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePartition
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringLift
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.InnermostLevel
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

open Classical in
theorem exists_finite_crossing_chart_cover
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    ∃ (e : hD.singularSet.branchCarrier c →
        OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
      (t : Finset (hD.singularSet.branchCarrier c)),
      (∀ y, e y ∈ atlas (EuclideanSpace ℝ (Fin 3)) M ∧
        (y : M) ∈ (e y).source ∧
          HasPLNormalDoubleCrossingAt ((e y) ∘ D)
            (D.domain ∩ D ⁻¹' (e y).source)
            ((e y) '' ((e y).source ∩ BdM)) ((e y) y)) ∧
        hD.singularSet.branchCarrier c ⊆ ⋃ y ∈ t, (e y).source := by
  choose e he using fun y : hD.singularSet.branchCarrier c =>
    hD.crossing (y : M) (hD.singularSet.branchCarrier_subset_doublePointSet c y.property)
  have hcover : hD.singularSet.branchCarrier c ⊆
      ⋃ y : hD.singularSet.branchCarrier c, (e y).source := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, (he ⟨y, hy⟩).2.1⟩
  obtain ⟨t, ht⟩ := (hD.singularSet.branchCarrier_isCompact c).elim_finite_subcover
    (fun y : hD.singularSet.branchCarrier c => (e y).source)
    (fun y => (e y).open_source) hcover
  exact ⟨e, t, he, ht⟩

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

private theorem exists_partition_members_of_two_component_split
    {E : Type*} [NormedAddCommGroup E]
    {P : Set E} (hPcompact : IsCompact P) {C : Set (Set E)} (hCfinite : C.Finite)
    (hCconnected : ∀ S ∈ C, IsConnected S) (hCclosed : ∀ S ∈ C, IsClosed S)
    (hCdisjoint : C.PairwiseDisjoint id) (hcover : P = ⋃₀ C)
    {x y : P} (hxy : Disjoint (connectedComponent x) (connectedComponent y))
    (hcomponents : connectedComponent x ∪ connectedComponent y = univ) :
    ∃ S T : Set E, S ∈ C ∧ T ∈ C ∧
      ((↑) : P → E) '' connectedComponent x = S ∧
      ((↑) : P → E) '' connectedComponent y = T := by
  let _ : CompactSpace P := isCompact_iff_compactSpace.mp hPcompact
  let A : Set E := ((↑) : P → E) '' connectedComponent x
  let B : Set E := ((↑) : P → E) '' connectedComponent y
  have hAconnected : IsConnected A :=
    isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn
  have hBconnected : IsConnected B :=
    isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn
  have hAclosed : IsClosed A :=
    (isClosed_connectedComponent.isCompact.image continuous_subtype_val).isClosed
  have hBclosed : IsClosed B :=
    (isClosed_connectedComponent.isCompact.image continuous_subtype_val).isClosed
  have hAne : A.Nonempty := ⟨x, ⟨x, mem_connectedComponent, rfl⟩⟩
  have hBne : B.Nonempty := ⟨y, ⟨y, mem_connectedComponent, rfl⟩⟩
  have hABdisjoint : Disjoint A B :=
    (Set.disjoint_image_iff Subtype.val_injective).mpr hxy
  have hABcover : A ∪ B = P := by
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
  have hAsub : A ⊆ ⋃₀ C := by
    intro z hz
    rw [← hcover]
    exact hABcover.subset (Or.inl hz)
  have hBsub : B ⊆ ⋃₀ C := by
    intro z hz
    rw [← hcover]
    exact hABcover.subset (Or.inr hz)
  obtain ⟨S, ⟨hSC, hAS⟩, -⟩ :=
    existsUnique_subset_of_isConnected_of_finite_closed_partition hAconnected hCfinite
      hCclosed hCdisjoint hAsub
  obtain ⟨T, ⟨hTC, hBT⟩, -⟩ :=
    existsUnique_subset_of_isConnected_of_finite_closed_partition hBconnected hCfinite
      hCclosed hCdisjoint hBsub
  have hSA : S ⊆ A := by
    have hScover : S ⊆ A ∪ B := by
      rw [hABcover, hcover]
      exact subset_sUnion_of_mem hSC
    rcases subset_or_subset_of_isPreconnected_of_isClosed
        (hCconnected S hSC).isPreconnected hAclosed hBclosed hABdisjoint hScover with h | h
    · exact h
    · obtain ⟨z, hz⟩ := hAne
      exact False.elim (Set.disjoint_left.mp hABdisjoint hz (h (hAS hz)))
  have hTB : T ⊆ B := by
    have hTcover : T ⊆ A ∪ B := by
      rw [hABcover, hcover]
      exact subset_sUnion_of_mem hTC
    rcases subset_or_subset_of_isPreconnected_of_isClosed
        (hCconnected T hTC).isPreconnected hAclosed hBclosed hABdisjoint hTcover with h | h
    · obtain ⟨z, hz⟩ := hBne
      exact False.elim (Set.disjoint_left.mp hABdisjoint (h (hBT hz)) hz)
    · exact h
  exact ⟨S, T, hSC, hTC, Subset.antisymm hAS hSA, Subset.antisymm hBT hTB⟩

private theorem bijOn_componentImage_of_homeomorph
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {P : Set E} {Q : Set F} (f : E → F) (p : P → Q)
    (hp : ∀ z : P, (p z : F) = f z) {x : P}
    (e : connectedComponent x ≃ₜ Q)
    (he : ∀ z : connectedComponent x, e z = p z) :
    BijOn f (((↑) : P → E) '' connectedComponent x) Q := by
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨w, -, rfl⟩
    rw [← hp]
    exact (p w).2
  · rintro z ⟨a, ha, rfl⟩ w ⟨b, hb, rfl⟩ hab
    have hpab : p a = p b := by
      apply Subtype.ext
      rw [hp, hp]
      exact hab
    have heab : e ⟨a, ha⟩ = e ⟨b, hb⟩ := by
      rw [he, he]
      exact hpab
    exact congrArg (fun q : connectedComponent x => ((q : P) : E)) (e.injective heab)
  · intro z hz
    obtain ⟨w, hw⟩ := e.surjective ⟨z, hz⟩
    refine ⟨w.1, ⟨w.1, w.2, rfl⟩, ?_⟩
    calc
      f w.1 = (p w.1 : F) := (hp w.1).symm
      _ = (e w : F) := congrArg Subtype.val (he w).symm
      _ = z := congrArg Subtype.val hw

def branchPreimage (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) : Set (EuclideanSpace ℝ (Fin 2)) :=
  D.domain ∩ D ⁻¹' hD.singularSet.branchCarrier c

theorem pairwise_disjoint_branchPreimage
    (hD : NormalSingularCellData D BdM B) :
    Pairwise fun c d : hD.singularSet.Branch =>
      Disjoint (hD.branchPreimage c) (hD.branchPreimage d) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro x hxc hxd
  exact Set.disjoint_left.mp (hD.singularSet.pairwise_disjoint_branchCarrier hcd)
    hxc.2 hxd.2

theorem branchPreimage_subset_interior_of_not_boundaryBranch
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c) :
    hD.branchPreimage c ⊆ interior D.domain := by
  intro x hx
  apply (mem_interior_iff_notMem_frontier hx.1).mpr
  intro hxfrontier
  have hxrange : D x ∈ Set.range D.boundary := ⟨⟨x, hxfrontier⟩, rfl⟩
  have hxBdM : D x ∈ BdM := (hD.image_inter_boundary.symm.subset hxrange).2
  exact Set.disjoint_left.mp
    (hD.singularSet.branchCarrier_disjoint_boundary_of_not_isBoundaryBranch hc) hx.2 hxBdM

private theorem isPLBall_subset_of_frontier_subset_interior
    {Q P : Set (EuclideanSpace ℝ (Fin 2))}
    (hQ : IsPLBall 2 Q) (hP : IsPLBall 2 P)
    (hfrontier : frontier Q ⊆ interior P) : Q ⊆ P := by
  have hQclosure : closure (Schoenflies.inside (frontier Q)) = Q :=
    PlanarJordan.closure_inside_frontier_eq_of_isCompact hQ.isPolyhedron.isCompact
      (isJordanCurve_of_isPLSphere_one hQ.isPLSphere_frontier) hQ.interior_nonempty
  have hPclosure : closure (Schoenflies.inside (frontier P)) = P :=
    PlanarJordan.closure_inside_frontier_eq_of_isCompact hP.isPolyhedron.isCompact
      (isJordanCurve_of_isPLSphere_one hP.isPLSphere_frontier) hP.interior_nonempty
  have hfrontier' : frontier Q ⊆ closure (Schoenflies.inside (frontier P)) := by
    rw [← hP.interior_eq_inside_frontier]
    exact hfrontier.trans subset_closure
  have hinside : Schoenflies.inside (frontier Q) ⊆
      Schoenflies.inside (frontier P) :=
    PlanarJordan.inside_subset_of_subset_closure_inside
      (Schoenflies.jordan_curve_theorem
        (isJordanCurve_of_isPLSphere_one hP.isPLSphere_frontier))
      (Schoenflies.jordan_curve_theorem
        (isJordanCurve_of_isPLSphere_one hQ.isPLSphere_frontier)) hfrontier'
  rw [← hQclosure, ← hPclosure]
  exact closure_mono hinside

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

theorem iUnion_branchPreimage
    (hD : NormalSingularCellData D BdM B) :
    ⋃ c : hD.singularSet.Branch, hD.branchPreimage c =
      doublePointPreimage D D.domain := by
  apply Subset.antisymm
  · exact iUnion_subset fun c => hD.branchPreimage_subset_doublePointPreimage c
  · rintro x ⟨hxD, hxdouble⟩
    have hxunion : D x ∈ ⋃ c : hD.singularSet.Branch,
        hD.singularSet.branchCarrier c := by
      rw [hD.singularSet.iUnion_branchCarrier]
      exact hxdouble
    obtain ⟨c, hxc⟩ := mem_iUnion.mp hxunion
    exact mem_iUnion.mpr ⟨c, hxD, hxc⟩

theorem injOn_of_doublePointPreimage_inter_eq_of_branchCoordinate
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {J Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hJsub : J ⊆ hD.branchPreimage c) (hQsub : Q ⊆ D.domain)
    (hinter : doublePointPreimage D D.domain ∩ Q = J)
    (hcoordinate : IsPLHomeomorphOn (hD.branchCoordinate c) J
      (hD.singularSet.branchComplex c).space) :
    InjOn D Q := by
  intro x hxQ y hyQ hxy
  by_contra hne
  have hxD : x ∈ D.domain := hQsub hxQ
  have hyD : y ∈ D.domain := hQsub hyQ
  have hxDouble : x ∈ doublePointPreimage D D.domain :=
    ⟨hxD, x, hxD, y, hyD, hne, rfl, hxy.symm⟩
  have hyDouble : y ∈ doublePointPreimage D D.domain :=
    ⟨hyD, y, hyD, x, hxD, Ne.symm hne, rfl, hxy⟩
  have hxJ : x ∈ J := hinter.subset ⟨hxDouble, hxQ⟩
  have hyJ : y ∈ J := hinter.subset ⟨hyDouble, hyQ⟩
  apply hne
  apply hcoordinate.bijOn.injOn hxJ hyJ
  apply (hD.singularSet.branchPieceIn c).bijOn.injOn
  · exact hD.branchCoordinate_mem c (hJsub hxJ)
  · exact hD.branchCoordinate_mem c (hJsub hyJ)
  · exact (hD.branchPieceIn_map_branchCoordinate c (hJsub hxJ)).trans
      (hxy.trans (hD.branchPieceIn_map_branchCoordinate c (hJsub hyJ)).symm)

theorem restrict_isNonsingular_of_doublePointPreimage_inter_eq_of_branchCoordinate
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {J Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hJsub : J ⊆ hD.branchPreimage c) (hQ : IsPLBall 2 Q)
    (hQsub : Q ⊆ D.domain) (hfrontier : frontier Q = J)
    (hinter : doublePointPreimage D D.domain ∩ Q = J)
    (hcoordinate : IsPLHomeomorphOn (hD.branchCoordinate c) J
      (hD.singularSet.branchComplex c).space) :
    (D.restrict hQ hQsub).IsNonsingular ∧
      Set.range (D.restrict hQ hQsub).boundary = D '' J := by
  constructor
  · exact (D.restrict_isNonsingular_iff hQ hQsub).mpr
      (hD.injOn_of_doublePointPreimage_inter_eq_of_branchCoordinate hJsub hQsub
        hinter hcoordinate)
  · exact (D.range_boundary_restrict hQ hQsub).trans
      (congrArg (fun S => D '' S) hfrontier)

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
theorem branchPreimage_nonempty
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    (hD.branchPreimage c).Nonempty := by
  let L := hD.singularSet.branchComplex c
  let _ : ConnectedSpace L.space :=
    Subtype.connectedSpace (hD.singularSet.branchComplex_space_isConnected c)
  let y : L.space := Classical.arbitrary L.space
  obtain ⟨a, -, -, -⟩ := encard_eq_two.mp (hD.branchProjection_fiber_encard_eq_two c y)
  exact ⟨a, a.property⟩

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
theorem exists_finite_isPLSphere_decomposition_branchPreimage_of_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ C : Set (Set (EuclideanSpace ℝ (Fin 2))),
      C.Finite ∧ C.Nonempty ∧ (∀ J ∈ C, IsPLSphere 1 J) ∧
        C.PairwiseDisjoint id ∧ hD.branchPreimage c = ⋃₀ C := by
  obtain ⟨K, hKfinite, hKspace, hKman, -, -⟩ :=
    hD.exists_branchPreimage_simplicialComplex_manifold_of_not_boundaryBranch hc
  let _ : Finite K.faces := hKfinite.to_subtype
  obtain ⟨C, hCfinite, hCsphere, hCdisjoint, hCcover⟩ :=
    exists_finite_isPLSphere_decomposition K hKman
  have hcover : hD.branchPreimage c = ⋃₀ C := hKspace.symm.trans hCcover
  have hCnonempty : C.Nonempty := by
    by_contra hC
    rw [not_nonempty_iff_eq_empty] at hC
    have hempty : ¬(hD.branchPreimage c).Nonempty := by
      rw [hcover, hC, sUnion_empty]
      exact not_nonempty_empty
    exact hempty (hD.branchPreimage_nonempty c)
  exact ⟨C, hCfinite, hCnonempty, hCsphere, hCdisjoint, hcover⟩

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

open Classical in
theorem branchPreimage_isPLSphere_or_exists_two_isPLSpheres_with_coordinate_of_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c) :
    IsPLSphere 1 (hD.branchPreimage c) ∨
      ∃ S T : Set (EuclideanSpace ℝ (Fin 2)),
        IsPLSphere 1 S ∧ IsPLSphere 1 T ∧ Disjoint S T ∧
          hD.branchPreimage c = S ∪ T ∧
            IsPLHomeomorphOn (hD.branchCoordinate c) S
              (hD.singularSet.branchComplex c).space ∧
            IsPLHomeomorphOn (hD.branchCoordinate c) T
              (hD.singularSet.branchComplex c).space := by
  let P := hD.branchPreimage c
  let L := hD.singularSet.branchComplex c
  let f := hD.branchCoordinate c
  let p := hD.branchProjection c
  obtain ⟨K, hKfinite, hKspace, hKman, -, -⟩ :=
    hD.exists_branchPreimage_simplicialComplex_manifold_of_not_boundaryBranch hc
  let _ : Finite K.faces := hKfinite.to_subtype
  obtain ⟨C, hCfinite, hCsphere, hCdisjoint, hCcover⟩ :=
    exists_finite_isPLSphere_decomposition K hKman
  have hcover : P = ⋃₀ C := hKspace.symm.trans hCcover
  rcases hD.branchProjection_connected_or_two_components c with hconnected | hsplit
  · left
    change IsPLSphere 1 P
    rw [hcover]
    apply (isPLSphere_one_sUnion_iff_isConnected hCfinite hCsphere hCdisjoint).mpr
    rw [← hcover]
    exact isConnected_iff_connectedSpace.mpr hconnected
  · obtain ⟨x, y, hxy, hcomponents, ⟨eS, heS⟩, ⟨eT, heT⟩⟩ := hsplit
    have hCconnected : ∀ S ∈ C, IsConnected S := by
      intro S hS
      exact (hCsphere S hS).isConnected_one
    have hCclosed : ∀ S ∈ C, IsClosed S := by
      intro S hS
      exact (hCsphere S hS).isPolyhedron.isClosed
    obtain ⟨S, T, hSC, hTC, hAS, hBT⟩ :=
      exists_partition_members_of_two_component_split (hD.branchPreimage_isCompact c)
        hCfinite hCconnected hCclosed hCdisjoint hcover hxy hcomponents
    let A : Set (EuclideanSpace ℝ (Fin 2)) :=
      ((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent x
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      ((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent y
    have hApoly : IsPolyhedron A := by
      change IsPolyhedron (((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent x)
      rw [hAS]
      exact (hCsphere S hSC).isPolyhedron
    have hRpoly : IsPolyhedron R := by
      change IsPolyhedron (((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent y)
      rw [hBT]
      exact (hCsphere T hTC).isPolyhedron
    have hAsub : A ⊆ P := by
      rintro z ⟨w, -, rfl⟩
      exact w.2
    have hRsub : R ⊆ P := by
      rintro z ⟨w, -, rfl⟩
      exact w.2
    have hp (z : P) :
        (p z : EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim)) = f z := rfl
    have hAbij : BijOn f A L.space :=
      bijOn_componentImage_of_homeomorph f p hp eS heS
    have hRbij : BijOn f R L.space :=
      bijOn_componentImage_of_homeomorph f p hp eT heT
    have hAPL : IsPLHomeomorphOn f A L.space :=
      isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hApoly
        ((hD.branchCoordinate_isPiecewiseAffineOn c).mono_of_isPolyhedron hApoly hAsub) hAbij
    have hRPL : IsPLHomeomorphOn f R L.space :=
      isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hRpoly
        ((hD.branchCoordinate_isPiecewiseAffineOn c).mono_of_isPolyhedron hRpoly hRsub) hRbij
    have hAsphere : IsPLSphere 1 A := by
      change IsPLSphere 1
        (((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent x)
      rw [hAS]
      exact hCsphere S hSC
    have hRsphere : IsPLSphere 1 R := by
      change IsPLSphere 1
        (((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent y)
      rw [hBT]
      exact hCsphere T hTC
    have hdisjoint : Disjoint A R :=
      (Set.disjoint_image_iff Subtype.val_injective).mpr hxy
    have hARcover : A ∪ R = P := by
      apply Subset.antisymm
      · exact union_subset hAsub hRsub
      · intro z hz
        let w : P := ⟨z, hz⟩
        have hw : w ∈ connectedComponent x ∪ connectedComponent y := by
          rw [hcomponents]
          exact mem_univ w
        rcases hw with hw | hw
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
    exact Or.inr ⟨A, R, hAsphere, hRsphere, hdisjoint, hARcover.symm, hAPL, hRPL⟩

open Classical in
theorem
  branchPreimage_isPLSphere_or_exists_two_isPLSpheres_with_innermost_disk_of_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c) :
    IsPLSphere 1 (hD.branchPreimage c) ∨
      ∃ J T Q : Set (EuclideanSpace ℝ (Fin 2)),
        IsPLSphere 1 J ∧ IsPLSphere 1 T ∧ Disjoint J T ∧
          hD.branchPreimage c = J ∪ T ∧ IsPLBall 2 Q ∧
            frontier Q = J ∧ hD.branchPreimage c ∩ Q = J := by
  rcases hD.branchPreimage_isPLSphere_or_exists_two_isPLSpheres_of_not_boundaryBranch hc with
    hsingle | ⟨S, T, hS, hT, hdisjoint, hcover⟩
  · exact Or.inl hsingle
  · right
    let C : Set (Set (EuclideanSpace ℝ (Fin 2))) := {S, T}
    have hCfinite : C.Finite := by simp [C]
    have hCnonempty : C.Nonempty := ⟨S, by simp [C]⟩
    have hCsphere : ∀ J ∈ C, IsPLSphere 1 J := by
      intro J hJ
      simp only [C, mem_insert_iff, mem_singleton_iff] at hJ
      rcases hJ with rfl | rfl
      · exact hS
      · exact hT
    have hCinter : ∀ J ∈ C, ∀ R ∈ C, J ≠ R → J ∩ R ⊆ ({0} : Set _) := by
      intro J hJ R hR hne
      simp only [C, mem_insert_iff, mem_singleton_iff] at hJ hR
      rcases hJ with rfl | rfl <;> rcases hR with rfl | rfl
      · exact (hne rfl).elim
      · exact hdisjoint.le_bot.trans (empty_subset _)
      · exact hdisjoint.symm.le_bot.trans (empty_subset _)
      · exact (hne rfl).elim
    obtain ⟨J, hJC, Q, hQ, hfrontier, hinter⟩ :=
      exists_innermost_isPLBall hCfinite hCnonempty hCsphere 0 hCinter
    have hJ : J = S ∨ J = T := by
      simpa only [C, mem_insert_iff, mem_singleton_iff] using hJC
    have hinter' : (S ∪ T) ∩ Q = J := by
      simpa only [C, sUnion_insert, sUnion_singleton] using hinter
    rcases hJ with hJS | hJT
    · exact ⟨S, T, Q, hS, hT, hdisjoint, hcover, hQ, hfrontier.trans hJS, by
        rw [hcover]
        exact hinter'.trans hJS⟩
    · exact ⟨T, S, Q, hT, hS, hdisjoint.symm, hcover.trans (union_comm S T), hQ,
        hfrontier.trans hJT, by
          rw [hcover]
          exact hinter'.trans hJT⟩

open Classical in
theorem exists_innermost_isPLBall_branchPreimage_of_exists_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch,
      ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch,
    ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧
        J ⊆ hD.branchPreimage c ∧ IsPLBall 2 Q ∧ Q ⊆ interior D.domain ∧ frontier Q = J ∧
          (⋃ d : {d : hD.singularSet.Branch //
              ¬hD.singularSet.IsBoundaryBranch d}, hD.branchPreimage d.1) ∩ Q = J := by
  let I := {c : hD.singularSet.Branch // ¬hD.singularSet.IsBoundaryBranch c}
  obtain ⟨c₀, hc₀⟩ := hclosed
  let i₀ : I := ⟨c₀, hc₀⟩
  let _ : Nonempty I := ⟨i₀⟩
  let _ : Finite hD.singularSet.complex.faces :=
    hD.singularSet.finite_faces.to_subtype
  let _ : Finite hD.singularSet.complex.vertices :=
    (SimplicialComplex.finite_vertices hD.singularSet.complex).to_subtype
  let _ : Finite hD.singularSet.Branch := inferInstance
  let _ : Finite I := inferInstance
  have hdecomp : ∀ i : I,
      ∃ C : Set (Set (EuclideanSpace ℝ (Fin 2))),
        C.Finite ∧ C.Nonempty ∧ (∀ J ∈ C, IsPLSphere 1 J) ∧
          C.PairwiseDisjoint id ∧ hD.branchPreimage i.1 = ⋃₀ C :=
    fun i => hD.exists_finite_isPLSphere_decomposition_branchPreimage_of_not_boundaryBranch i.2
  choose circles hfinite hnonempty hsphere hdisjoint hcover using hdecomp
  let C : Set (Set (EuclideanSpace ℝ (Fin 2))) := ⋃ i : I, circles i
  have hCfinite : C.Finite := by
    exact Set.finite_iUnion hfinite
  have hCnonempty : C.Nonempty := by
    obtain ⟨J, hJ⟩ := hnonempty i₀
    exact ⟨J, mem_iUnion.mpr ⟨i₀, hJ⟩⟩
  have hCsphere : ∀ J ∈ C, IsPLSphere 1 J := by
    intro J hJ
    obtain ⟨i, hJi⟩ := mem_iUnion.mp hJ
    exact hsphere i J hJi
  have hCdisjoint : C.PairwiseDisjoint id := by
    intro J hJ R hR hJR
    obtain ⟨i, hJi⟩ := mem_iUnion.mp hJ
    obtain ⟨k, hRk⟩ := mem_iUnion.mp hR
    by_cases hik : i = k
    · subst k
      exact hdisjoint i hJi hRk hJR
    · have hik' : (i : hD.singularSet.Branch) ≠ k :=
        fun h => hik (Subtype.ext h)
      have hJsub : J ⊆ hD.branchPreimage i.1 := by
        rw [hcover i]
        exact subset_sUnion_of_mem hJi
      have hRsub : R ⊆ hD.branchPreimage k.1 := by
        rw [hcover k]
        exact subset_sUnion_of_mem hRk
      exact Disjoint.mono hJsub hRsub (hD.pairwise_disjoint_branchPreimage hik')
  have hCcover : ⋃₀ C = ⋃ i : I, hD.branchPreimage i.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨J, hJC, hxJ⟩ := mem_sUnion.mp hx
      obtain ⟨i, hJi⟩ := mem_iUnion.mp hJC
      apply mem_iUnion.mpr
      exact ⟨i, (hcover i).symm.subset (mem_sUnion.mpr ⟨J, hJi, hxJ⟩)⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      obtain ⟨J, hJi, hxJ⟩ := mem_sUnion.mp ((hcover i).subset hxi)
      exact mem_sUnion.mpr ⟨J, mem_iUnion.mpr ⟨i, hJi⟩, hxJ⟩
  have hCinter : ∀ J ∈ C, ∀ R ∈ C, J ≠ R → J ∩ R ⊆ ({0} : Set _) := by
    intro J hJ R hR hJR
    exact (hCdisjoint hJ hR hJR).le_bot.trans (empty_subset _)
  obtain ⟨J, hJC, Q, hQ, hfrontier, hinter⟩ :=
    exists_innermost_isPLBall hCfinite hCnonempty hCsphere 0 hCinter
  obtain ⟨i, hJi⟩ := mem_iUnion.mp hJC
  have hJsub : J ⊆ hD.branchPreimage i.1 := by
    rw [hcover i]
    exact subset_sUnion_of_mem hJi
  have hQsub : Q ⊆ D.domain := by
    apply isPLBall_subset_of_frontier_subset_interior hQ D.isPLBall_domain
    rw [hfrontier]
    exact hJsub.trans (hD.branchPreimage_subset_interior_of_not_boundaryBranch i.2)
  have hQsubInterior : Q ⊆ interior D.domain := by
    intro x hxQ
    by_cases hxfrontier : x ∈ frontier Q
    · rw [hfrontier] at hxfrontier
      exact hD.branchPreimage_subset_interior_of_not_boundaryBranch i.2
        (hJsub hxfrontier)
    · exact interior_mono hQsub ((mem_interior_iff_notMem_frontier hxQ).mpr hxfrontier)
  refine ⟨i.1, J, Q, i.2, hsphere i J hJi, hJsub, hQ, hQsubInterior,
    hfrontier, ?_⟩
  · change (⋃ i : I, hD.branchPreimage i.1) ∩ Q = J
    rw [← hCcover]
    exact hinter

open Classical in
theorem exists_innermost_isPLBall_branchPreimage_decomposition_of_exists_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch,
      ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch,
    ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧
        IsPLBall 2 Q ∧ Q ⊆ interior D.domain ∧ frontier Q = J ∧
          (⋃ d : {d : hD.singularSet.Branch //
              ¬hD.singularSet.IsBoundaryBranch d}, hD.branchPreimage d.1) ∩ Q = J ∧
            (hD.branchPreimage c = J ∨
              ∃ T : Set (EuclideanSpace ℝ (Fin 2)),
                IsPLSphere 1 T ∧ Disjoint J T ∧ hD.branchPreimage c = J ∪ T) := by
  obtain ⟨c, J, Q, hc, hJ, hJsub, hQ, hQsub, hfrontier, hinter⟩ :=
    hD.exists_innermost_isPLBall_branchPreimage_of_exists_not_boundaryBranch hclosed
  refine ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hinter, ?_⟩
  rcases hD.branchPreimage_isPLSphere_or_exists_two_isPLSpheres_of_not_boundaryBranch hc with
    hsingle | ⟨S, T, hS, hT, hdisjoint, hcover⟩
  · exact Or.inl (eq_of_subset_of_isPLSphere_one hJ hsingle hJsub).symm
  · have hsub : J ⊆ S ∪ T := hJsub.trans hcover.subset
    rcases subset_or_subset_of_isPreconnected_of_isClosed hJ.isConnected_one.isPreconnected
        hS.isPolyhedron.isClosed hT.isPolyhedron.isClosed hdisjoint hsub with hJS | hJT
    · have hJS' : J = S := eq_of_subset_of_isPLSphere_one hJ hS hJS
      exact Or.inr ⟨T, hT, hJS' ▸ hdisjoint, hcover.trans (hJS' ▸ rfl)⟩
    · have hJT' : J = T := eq_of_subset_of_isPLSphere_one hJ hT hJT
      exact Or.inr ⟨S, hS, hJT' ▸ hdisjoint.symm,
        hcover.trans ((hJT' ▸ union_comm S T))⟩

open Classical in
theorem exists_innermost_isPLBall_branchPreimage_decomposition_with_coordinate
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch,
      ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch,
    ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧
        IsPLBall 2 Q ∧ Q ⊆ interior D.domain ∧ frontier Q = J ∧
          (⋃ d : {d : hD.singularSet.Branch //
              ¬hD.singularSet.IsBoundaryBranch d}, hD.branchPreimage d.1) ∩ Q = J ∧
            (hD.branchPreimage c = J ∨
              ∃ T : Set (EuclideanSpace ℝ (Fin 2)),
                IsPLSphere 1 T ∧ Disjoint J T ∧ hD.branchPreimage c = J ∪ T ∧
                  IsPLHomeomorphOn (hD.branchCoordinate c) J
                    (hD.singularSet.branchComplex c).space ∧
                  IsPLHomeomorphOn (hD.branchCoordinate c) T
                    (hD.singularSet.branchComplex c).space) := by
  obtain ⟨c, J, Q, hc, hJ, hJsub, hQ, hQsub, hfrontier, hinter⟩ :=
    hD.exists_innermost_isPLBall_branchPreimage_of_exists_not_boundaryBranch hclosed
  refine ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hinter, ?_⟩
  rcases
      hD.branchPreimage_isPLSphere_or_exists_two_isPLSpheres_with_coordinate_of_not_boundaryBranch
        hc with hsingle | ⟨S, T, hS, hT, hdisjoint, hcover, hScoord, hTcoord⟩
  · exact Or.inl (eq_of_subset_of_isPLSphere_one hJ hsingle hJsub).symm
  · have hsub : J ⊆ S ∪ T := hJsub.trans hcover.subset
    rcases subset_or_subset_of_isPreconnected_of_isClosed hJ.isConnected_one.isPreconnected
        hS.isPolyhedron.isClosed hT.isPolyhedron.isClosed hdisjoint hsub with hJS | hJT
    · have hJS' : J = S := eq_of_subset_of_isPLSphere_one hJ hS hJS
      exact Or.inr ⟨T, hT, hJS' ▸ hdisjoint, hcover.trans (hJS' ▸ rfl),
        hJS' ▸ hScoord, hTcoord⟩
    · have hJT' : J = T := eq_of_subset_of_isPLSphere_one hJ hT hJT
      exact Or.inr ⟨S, hS, hJT' ▸ hdisjoint.symm,
        hcover.trans ((hJT' ▸ union_comm S T)), hJT' ▸ hTcoord, hScoord⟩

open Classical in
theorem exists_two_isPLBalls_branchPreimage_of_boundaryBranch_with_coordinate
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
        hD.branchPreimage c = A ∪ C ∧
        IsPLHomeomorphOn (hD.branchCoordinate c) A
          (hD.singularSet.branchComplex c).space ∧
        IsPLHomeomorphOn (hD.branchCoordinate c) C
          (hD.singularSet.branchComplex c).space := by
  let P := hD.branchPreimage c
  let L := hD.singularSet.branchComplex c
  let f := hD.branchCoordinate c
  let p := hD.branchProjection c
  have hLball : IsPLBall 1 L.space := hD.singularSet.branchComplex_isPLBall hc
  let _ : SimplyConnectedSpace L.space := hLball.simplyConnectedSpace
  let _ : LocallyPathConnectedSpace L.space := hLball.locallyPathConnectedSpace
  have htwo : ∃ x y : P,
      Disjoint (connectedComponent x) (connectedComponent y) ∧
      connectedComponent x ∪ connectedComponent y = univ ∧
      (∃ e : connectedComponent x ≃ₜ L.space,
        ∀ z : connectedComponent x, e z = p z) ∧
      ∃ e : connectedComponent y ≃ₜ L.space,
        ∀ z : connectedComponent y, e z = p z := by
    rcases hD.branchProjection_connected_or_two_components c with hconnected | hsplit
    · let _ : ConnectedSpace P := hconnected
      have hinj : Function.Injective p :=
        (hD.branchProjection_isCoveringMap c).injective_of_simplyConnected
      let q : L.space := Classical.arbitrary L.space
      obtain ⟨a, b, hab, hfiber⟩ := encard_eq_two.mp (hD.branchProjection_fiber_encard_eq_two c q)
      have ha : p a = q := by
        change a ∈ p ⁻¹' {q}
        rw [hfiber]
        exact Or.inl rfl
      have hb : p b = q := by
        change b ∈ p ⁻¹' {q}
        rw [hfiber]
        exact Or.inr rfl
      exact False.elim (hab (hinj (ha.trans hb.symm)))
    · exact hsplit
  obtain ⟨x, y, hxy, hcomponents, ⟨eA, heA⟩, ⟨eC, heC⟩⟩ := htwo
  obtain ⟨K, hKfinite, hKspace, hKman, -, -⟩ :=
    hD.exists_branchPreimage_simplicialComplex_manifold c
  let _ : Finite K.faces := hKfinite.to_subtype
  obtain ⟨Q, hQfinite, hQshape, hQdisjoint, hQcover⟩ :=
    exists_finite_isPLSphere_or_isPLBall_decomposition K hKman
  have hQconnected : ∀ S ∈ Q, IsConnected S := by
    intro S hS
    exact (hQshape S hS).elim (fun h => h.isConnected_one) (fun h => h.isConnected)
  have hQclosed : ∀ S ∈ Q, IsClosed S := by
    intro S hS
    exact (hQshape S hS).elim
      (fun h => h.isPolyhedron.isClosed) (fun h => h.isPolyhedron.isClosed)
  obtain ⟨S, T, hSQ, hTQ, hAS, hCT⟩ :=
    exists_partition_members_of_two_component_split (hD.branchPreimage_isCompact c)
      hQfinite hQconnected hQclosed hQdisjoint (hKspace.symm.trans hQcover)
        hxy hcomponents
  let A : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent x
  let C : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent y
  have hApoly : IsPolyhedron A := by
    change IsPolyhedron (((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent x)
    rw [hAS]
    exact (hQshape S hSQ).elim (fun h => h.isPolyhedron) (fun h => h.isPolyhedron)
  have hCpoly : IsPolyhedron C := by
    change IsPolyhedron (((↑) : P → EuclideanSpace ℝ (Fin 2)) '' connectedComponent y)
    rw [hCT]
    exact (hQshape T hTQ).elim (fun h => h.isPolyhedron) (fun h => h.isPolyhedron)
  have hAsub : A ⊆ P := by
    rintro z ⟨w, -, rfl⟩
    exact w.2
  have hCsub : C ⊆ P := by
    rintro z ⟨w, -, rfl⟩
    exact w.2
  have hp (z : P) : (p z : EuclideanSpace ℝ (Fin hD.singularSet.piece.ambientDim)) = f z := rfl
  have hAbij : BijOn f A L.space :=
    bijOn_componentImage_of_homeomorph f p hp eA heA
  have hCbij : BijOn f C L.space :=
    bijOn_componentImage_of_homeomorph f p hp eC heC
  have hAPL : IsPLHomeomorphOn f A L.space :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hApoly
      ((hD.branchCoordinate_isPiecewiseAffineOn c).mono_of_isPolyhedron hApoly hAsub) hAbij
  have hCPL : IsPLHomeomorphOn f C L.space :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hCpoly
      ((hD.branchCoordinate_isPiecewiseAffineOn c).mono_of_isPolyhedron hCpoly hCsub) hCbij
  have hAdisjointC : Disjoint A C :=
    (Set.disjoint_image_iff Subtype.val_injective).mpr hxy
  have hACcover : A ∪ C = P := by
    apply Subset.antisymm
    · exact union_subset hAsub hCsub
    · intro z hz
      let w : P := ⟨z, hz⟩
      have hw : w ∈ connectedComponent x ∪ connectedComponent y := by
        rw [hcomponents]
        exact mem_univ w
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · exact Or.inr ⟨w, hw, rfl⟩
  exact ⟨A, C, hLball.of_isPLHomeomorphOn hAPL.symm,
    hLball.of_isPLHomeomorphOn hCPL.symm, hAdisjointC, hACcover.symm, hAPL, hCPL⟩

open Classical in
theorem exists_isPLHomeomorphOn_eqOn_of_branchCoordinate
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hAsub : A ⊆ hD.branchPreimage c) (hCsub : C ⊆ hD.branchPreimage c)
    (hAcoord : IsPLHomeomorphOn (hD.branchCoordinate c) A
      (hD.singularSet.branchComplex c).space)
    (hCcoord : IsPLHomeomorphOn (hD.branchCoordinate c) C
      (hD.singularSet.branchComplex c).space) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn g A C ∧ EqOn D (D ∘ g) A := by
  let g := Function.invFunOn (hD.branchCoordinate c) C ∘ hD.branchCoordinate c
  have hg : IsPLHomeomorphOn g A C := hAcoord.trans hCcoord.symm
  refine ⟨g, hg, ?_⟩
  intro x hxA
  have hgC : g x ∈ C := hg.bijOn.mapsTo hxA
  have hcoord : hD.branchCoordinate c (g x) = hD.branchCoordinate c x :=
    hCcoord.bijOn.invOn_invFunOn.2 (hAcoord.bijOn.mapsTo hxA)
  calc
    D x = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c x) :=
      (hD.branchPieceIn_map_branchCoordinate c (hAsub hxA)).symm
    _ = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c (g x)) :=
      congrArg (hD.singularSet.branchPieceIn c).map hcoord.symm
    _ = D (g x) := hD.branchPieceIn_map_branchCoordinate c (hCsub hgC)

open Classical in
theorem exists_replacement_disk_of_two_branch_sheets
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J T Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hJsub : J ⊆ hD.branchPreimage c) (hTsub : T ⊆ hD.branchPreimage c)
    (hT : IsPLSphere 1 T) (hQ : IsPLBall 2 Q) (hfrontier : frontier Q = J)
    (hJcoordinate : IsPLHomeomorphOn (hD.branchCoordinate c) J
      (hD.singularSet.branchComplex c).space)
    (hTcoordinate : IsPLHomeomorphOn (hD.branchCoordinate c) T
      (hD.singularSet.branchComplex c).space) :
    ∃ (R : Set (EuclideanSpace ℝ (Fin 2)))
        (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 R ∧ R ⊆ D.domain ∧ frontier R = T ∧
        IsPLHomeomorphOn G R Q ∧ EqOn D (D ∘ G) (frontier R) := by
  obtain ⟨R, hR, hRfrontier, -⟩ := isPLBall_of_isPLSphere_one hT
  have hRsub : R ⊆ D.domain := by
    apply isPLBall_subset_of_frontier_subset_interior hR D.isPLBall_domain
    rw [hRfrontier]
    exact hTsub.trans (hD.branchPreimage_subset_interior_of_not_boundaryBranch hc)
  obtain ⟨g, hg, hcompat⟩ :=
    hD.exists_isPLHomeomorphOn_eqOn_of_branchCoordinate c hTsub hJsub
      hTcoordinate hJcoordinate
  have hgfrontier : IsPLHomeomorphOn g (frontier R) (frontier Q) := by
    rw [hRfrontier, hfrontier]
    exact hg
  obtain ⟨G, hG, hGg⟩ := exists_isPLHomeomorphOn_of_frontier hR hQ hgfrontier
  refine ⟨R, G, hR, hRsub, hRfrontier, hG, ?_⟩
  intro x hx
  have hxT : x ∈ T := hRfrontier ▸ hx
  change D x = D (G x)
  exact (hcompat hxT).trans (congrArg D (hGg hx).symm)

open Classical in
theorem exists_innermost_isPLBall_branchPreimage_with_replacement_of_exists_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch,
      ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch,
    ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧
        IsPLBall 2 Q ∧ Q ⊆ interior D.domain ∧ frontier Q = J ∧
          (⋃ d : {d : hD.singularSet.Branch //
              ¬hD.singularSet.IsBoundaryBranch d}, hD.branchPreimage d.1) ∩ Q = J ∧
            (hD.branchPreimage c = J ∨
              ∃ (T R : Set (EuclideanSpace ℝ (Fin 2)))
                  (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
                IsPLSphere 1 T ∧ Disjoint J T ∧ hD.branchPreimage c = J ∪ T ∧
                  IsPLHomeomorphOn (hD.branchCoordinate c) J
                    (hD.singularSet.branchComplex c).space ∧
                  IsPLHomeomorphOn (hD.branchCoordinate c) T
                    (hD.singularSet.branchComplex c).space ∧
                  IsPLBall 2 R ∧ R ⊆ D.domain ∧ frontier R = T ∧
                  IsPLHomeomorphOn G R Q ∧ EqOn D (D ∘ G) (frontier R)) := by
  obtain ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hinter, hsplit⟩ :=
    hD.exists_innermost_isPLBall_branchPreimage_decomposition_with_coordinate
      hclosed
  refine ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hinter, ?_⟩
  rcases hsplit with hsingle | ⟨T, hT, hdisjoint, hcover, hJcoordinate, hTcoordinate⟩
  · exact Or.inl hsingle
  · have hJsub : J ⊆ hD.branchPreimage c := by
      rw [hcover]
      exact subset_union_left
    have hTsub : T ⊆ hD.branchPreimage c := by
      rw [hcover]
      exact subset_union_right
    obtain ⟨R, G, hR, hRsub, hRfrontier, hG, hcompat⟩ :=
      hD.exists_replacement_disk_of_two_branch_sheets hc hJsub hTsub hT hQ hfrontier
        hJcoordinate hTcoordinate
    exact Or.inr ⟨T, R, G, hT, hdisjoint, hcover, hJcoordinate, hTcoordinate,
      hR, hRsub, hRfrontier, hG, hcompat⟩

open Classical in
theorem exists_isPLHomeomorphOn_branch_sheets
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
        hD.branchPreimage c = A ∪ C ∧
        ∃ g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
          IsPLHomeomorphOn g A C ∧ EqOn D (D ∘ g) A := by
  obtain ⟨A, C, hA, hC, hdisjoint, hcover, hAcoord, hCcoord⟩ :=
    hD.exists_two_isPLBalls_branchPreimage_of_boundaryBranch_with_coordinate hc
  have hAsub : A ⊆ hD.branchPreimage c := by
    rw [hcover]
    exact subset_union_left
  have hCsub : C ⊆ hD.branchPreimage c := by
    rw [hcover]
    exact subset_union_right
  obtain ⟨g, hg, hcompat⟩ :=
    hD.exists_isPLHomeomorphOn_eqOn_of_branchCoordinate c hAsub hCsub hAcoord hCcoord
  exact ⟨A, C, hA, hC, hdisjoint, hcover, g, hg, hcompat⟩

open Classical in
theorem exists_two_isPLBalls_branchPreimage_of_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
        hD.branchPreimage c = A ∪ C := by
  obtain ⟨A, C, hA, hC, hdisjoint, hcover, -, -⟩ :=
    hD.exists_two_isPLBalls_branchPreimage_of_boundaryBranch_with_coordinate hc
  exact ⟨A, C, hA, hC, hdisjoint, hcover⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
