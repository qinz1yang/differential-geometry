/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CoverReductionOrientable

open Set Topology

private noncomputable local instance euclideanDecidableEqOrientable (N : ℕ) :
    DecidableEq (EuclideanSpace ℝ (Fin N)) := Classical.decEq _

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
private theorem not_conjugacyClassMeets_comap_of_comp
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (γ : freeLoop X) (q : Path x (γ 0))
    (N : Subgroup (FundamentalGroup Y y)) [N.Normal]
    (havoid : ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass y (f.comp γ) ((q.map f.continuous).cast h.symm rfl)) N) :
    ¬conjugacyClassMeets (normalSystemLoopConjugacyClass x γ q)
      (N.comap (FundamentalGroup.mapOfEq f h)) := by
  intro hmeet
  have hmem := (conjugacyClassMeets_iff_carrier_subset _
    (N.comap (FundamentalGroup.mapOfEq f h))).mp hmeet
      (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl)
  change FundamentalGroup.mapOfEq f h (loopRepresentativeAlong q ⟨γ, rfl⟩) ∈ N at hmem
  rw [mapOfEq_loopRepresentativeAlong] at hmem
  exact havoid ⟨_, ConjClasses.mem_carrier_iff_mk_eq.mpr rfl, hmem⟩

namespace NormalSystem

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_doubleCoverReduction_isOrientableManifold_of_isCoveringMap
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0) (hor : S.IsOrientableManifold)
    {X : Type} [TopologicalSpace X] [PreconnectedSpace X]
    (p : X → S.manifoldComplex.space) (hp : IsCoveringMap p)
    (hcard : ∀ y, (p ⁻¹' {y}).encard = 2) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N)))
      (R : DoubleCoverReduction S T),
      T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space ∧
      T.IsOrientableManifold ∧
      ∀ x ∈ T.boundaryNeighborhood.space,
        S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x) := by
  let K := S.manifoldComplex
  let D := S.sourceComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ : Finite D.faces := S.finite_source.to_subtype
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  have hfin (y : K.space) : (p ⁻¹' {y}).Finite := finite_of_encard_eq_coe (hcard y)
  let _ : Finite (coveringVertex K p) := coveringVertex.finite K hfin
  have hD : IsPLBall 2 D.space := S.source_isPLBall
  have hfront : frontier D.space = (PiecewiseLinear.boundaryComplex 2 D).space :=
    frontier_space_eq_boundaryComplex_space hD.isCombinatorialManifoldWithBoundary
  have hfrontsub : frontier D.space ⊆ D.space := by
    simpa only [hD.isPolyhedron.isClosed.closure_eq] using
      (frontier_subset_closure : frontier D.space ⊆ closure D.space)
  have hφ : ∀ s ∈ D.faces, s.image S.vertexMap ∈ K.faces :=
    fun s hs => S.image_faces_subset_manifoldComplex (S.source_faces_map s hs)
  have hboundary :
      D.space ∩ simplicialMap D S.vertexMap ⁻¹' (PiecewiseLinear.boundaryComplex 3 K).space =
      (PiecewiseLinear.boundaryComplex 2 D).space := hproper.trans hfront
  let x₀ : D.space := ⟨S.boundaryParam 0, hfrontsub (S.boundaryParam 0).2⟩
  let y₀ : K.space := ⟨S.singularMap x₀, S.singularMap_mapsTo_manifoldComplex x₀.2⟩
  obtain ⟨e₀, he₀⟩ := nonempty_of_encard_ne_zero (s := p ⁻¹' {y₀}) (by rw [hcard]; norm_num)
  have h₀ : p e₀ =
      ⟨simplicialMap D S.vertexMap x₀, simplicialMap_mapsTo D K S.vertexMap hφ x₀.2⟩ := he₀
  let O := (closure (S.boundaryComplex.space \ S.boundaryNeighborhood.space))ᶜ
  have hO : IsOpen O := isClosed_closure.isOpen_compl
  have hloopO : S.loopComplex.space ⊆ O := by
    intro x hx hxcl
    have hnhds : S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] x :=
      derivedNeighborhood_mem_nhdsWithin (K := S.boundaryComplex)
        S.loop_faces_subset_boundary hx
    obtain ⟨U, hU, hUB⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
    obtain ⟨y, hyU, hybd, hyB⟩ := mem_closure_iff_nhds.mp hxcl U hU
    exact hyB (hUB ⟨hyU, hybd⟩)
  have hOB : O ∩ S.boundaryComplex.space ⊆ S.boundaryNeighborhood.space := by
    rintro x ⟨hxO, hxbd⟩
    by_contra hxB
    exact hxO (subset_closure ⟨hxbd, hxB⟩)
  have hV : O ∩ S.boundaryNeighborhood.space ∈
      𝓝ˢ[(PiecewiseLinear.boundaryComplex 3 K).space]
        (simplicialMap D S.vertexMap '' (PiecewiseLinear.boundaryComplex 2 D).space) := by
    rw [← hfront]
    change O ∩ S.boundaryNeighborhood.space ∈ 𝓝ˢ[S.boundaryComplex.space]
      (S.singularMap '' frontier D.space)
    have hloop : S.singularMap '' frontier D.space = S.loopComplex.space := S.loop_space.symm
    rw [hloop]
    exact mem_nhdsSetWithin.mpr ⟨O, hO, hloopO, fun x hx => ⟨hx.1, hOB hx⟩⟩
  obtain ⟨ψ, hψ, A, C, T₀, hAL, -, hfaces, hAspace, hCspace,
    hT₀, hCT₀, htrace, hproperT₀, hmapB, hproj, -⟩ :=
    exists_simplicialMap_lift_derivedNeighborhood K p S.isManifold D hD S.vertexMap hφ
      hboundary hp x₀ e₀ h₀ hV
  let L := coveringComplex K p
  let q := coveringBaseMap K p
  let g := simplicialMap D ψ
  let B := normalSystemBoundaryNeighborhood T₀ C
  let _ : Finite L.faces := (coveringComplex_faces_finite K p).to_subtype
  let _ : Finite T₀.complex.faces := T₀.finite_faces.to_subtype
  let _ : Finite (PiecewiseLinear.boundaryComplex 3 T₀.complex).faces :=
    (PiecewiseLinear.boundaryComplex_faces_finite 3 T₀.complex).to_subtype
  have hCB : C.space ⊆ B.space := by
    change C.space ⊆ (derivedNeighborhood (PiecewiseLinear.boundaryComplex 3 T₀.complex) C).space
    exact subcomplex_space_subset_derivedNeighborhood hCT₀
  have hBL : B.space ⊆ L.space := by
    intro x hx
    have hxT := boundaryComplex_space_subset 3 T₀.complex
      (derivedNeighborhood_space_subset (PiecewiseLinear.boundaryComplex 3 T₀.complex) C hx)
    rw [T₀.space_eq] at hxT
    exact derivedNeighborhood_space_subset L A hxT
  have hCfront : C.space = g '' frontier D.space :=
    hCspace.trans (congrArg (g '' ·) hfront.symm)
  have hgbd (θ : loopCircle) : g (S.boundaryParam θ) ∈ B.space :=
    hCB (hCfront.symm ▸ mem_image_of_mem g (S.boundaryParam θ).2)
  let a : C(loopCircle, D.space) :=
    ⟨fun θ => ⟨S.boundaryParam θ, hfrontsub (S.boundaryParam θ).2⟩,
      (continuous_subtype_val.comp S.boundaryParam.continuous).subtype_mk _⟩
  let γ : freeLoop B.space :=
    ⟨fun θ => ⟨g (S.boundaryParam θ), hgbd θ⟩,
      (((isPiecewiseAffineOn_simplicialMap D ψ).continuousOn.domRestrict).comp
        a.continuous).subtype_mk _⟩
  let β : C(B.space, S.boundaryNeighborhoodSpace) :=
    ⟨fun x => ⟨q x, (hmapB x.2).2⟩,
      ((isPiecewiseAffineOn_coveringBaseMap K p).continuousOn.mono hBL).domRestrict.subtype_mk _⟩
  have hβγ : β.comp γ = S.boundaryLoop := by
    ext θ
    exact (hproj (hfrontsub (S.boundaryParam θ).2)).trans (S.boundaryLoop_eq θ).symm
  have hb₀ : β (γ 0) = S.basepoint :=
    (congrArg (fun δ : freeLoop S.boundaryNeighborhoodSpace => δ 0) hβγ).trans hbase.symm
  let H := S.normalSubgroup.comap (FundamentalGroup.mapOfEq β hb₀)
  let _ : S.normalSubgroup.Normal := S.normal
  have havoidMapped (δ : freeLoop S.boundaryNeighborhoodSpace) (hδ : δ = S.boundaryLoop)
      (r : Path S.basepoint (δ 0)) :
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint δ r) S.normalSubgroup := by
    subst δ
    rw [S.loopConjugacyClass_eq_of_connector r]
    exact S.loopClass_avoids_normal
  have havoid : ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass (γ 0) γ (Path.refl (γ 0))) H :=
    not_conjugacyClassMeets_comap_of_comp β hb₀ γ (Path.refl (γ 0)) S.normalSubgroup
      (havoidMapped _ hβγ _)
  let T : NormalSystem (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
    { ambientComplex := L
      imageComplex := A
      loopComplex := C
      sourceComplex := D
      finite_ambient := coveringComplex_faces_finite K p
      finite_source := S.finite_source
      source_isPLBall := hD
      vertexMap := ψ
      source_faces_map := hfaces
      image_space := hAspace
      image_faces_subset_ambient := hAL
      neighborhood := T₀
      isManifold := hT₀
      loop_space := hCfront
      loop_faces_subset_boundary := hCT₀
      image_inter_boundary := htrace
      basepoint := γ 0
      boundaryLoop := γ
      boundaryParam := S.boundaryParam
      boundaryLoop_eq := fun _ => rfl
      connector := Path.refl _
      normalSubgroup := H
      normal := inferInstance
      loopClass_avoids_normal := havoid }
  let R : DoubleCoverDiagram S T :=
    { projection := q
      projection_mapsTo := coveringBaseMap_mapsTo K p
      isCoveringMap := isCoveringMap_coveringBaseMap_restrict K p hp
      fiber_card := fun y => (encard_preimage_coveringBaseMap_restrict K p hp y).trans (hcard y)
      isPiecewiseAffineOn_projection := isPiecewiseAffineOn_coveringBaseMap K p
      sourceComplex_eq := rfl
      source_lift := hproj
      boundaryMap := β
      boundaryMap_eq := fun _ => rfl
      basepoint_eq := hb₀
      normalSubgroup_eq := rfl }
  have hconn : IsPreconnected T.ambientComplex.space := isPreconnected_coveringComplex_space K p hp
  have hLman : IsCombinatorialManifoldWithBoundary 3 L :=
    isCombinatorialManifoldWithBoundary_coveringComplex K p hp S.isManifold
  have horL : IsOrientable 3 L := IsOrientable.coveringComplex hp S.isManifold hor
  have horT : T.IsOrientableManifold :=
    T.isOrientableManifold_of_isSubdivision hLman (IsSubdivision.refl L) horL
  refine ⟨Nat.card (coveringVertex K p), T,
    { toDoubleCoverDiagram := R, complexity_lt := R.complexity_lt_of_isPreconnected hconn },
    rfl, hproperT₀.trans hfront.symm, horT, ?_⟩
  intro x hx
  have hxO : q x ∈ O := (hmapB hx).1
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hxO), self_mem_nhdsWithin]
    with y hyO hybd
  exact hOB ⟨hyO, hybd⟩

end NormalSystem

open Classical in
theorem orientableCoverReductionStatement : OrientableCoverReductionStatement := by
  intro E _ _ _ S hproper hbase hor hnot
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  let _ : ConnectedSpace K.space :=
    isConnected_iff_connectedSpace.mp S.isConnected_manifoldComplex_space
  have hx : (S.boundaryLoop 0 : E) ∈ (PiecewiseLinear.boundaryComplex 3 K).space :=
    derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (S.boundaryLoop 0).2
  let c := ConnectedComponents.mk
    (⟨(S.boundaryLoop 0 : E), hx⟩ : (PiecewiseLinear.boundaryComplex 3 K).space)
  have hc : (connectedComponentComplex (PiecewiseLinear.boundaryComplex 3 K) c).space =
      S.boundaryComponent := by
    dsimp only [c]
    rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
    rfl
  obtain ⟨ε, -, -, -, hε, -, -, -, -, -⟩ :=
    exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere
      K S.isManifold hor c (hc ▸ hnot)
  let _ : ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace :=
    ε.connectedSpace_iff.mpr hε
  apply S.exists_doubleCoverReduction_isOrientableManifold_of_isCoveringMap hproper hbase hor
    ε.toBoolCocycle.toFiberBundleCore.proj ε.isCoveringMap
  intro y
  rw [← (ε.finite_fiber y).cast_ncard_eq, ← Nat.card_coe_set_eq, ε.card_fiber]
  rfl

theorem moise252_of_lemmaTwoOrientable (lemmaTwo : LemmaTwoBufferedOrientableStatement) :
    Moise252 :=
  moise252_of_lemmaTwoBufferedOrientable orientableCoverReductionStatement lemmaTwo

theorem moise304_of_lemmaTwoOrientable (lemmaTwo : LemmaTwoBufferedOrientableStatement) :
    Moise304 :=
  moise304_of_lemmaTwoBufferedOrientable orientableCoverReductionStatement lemmaTwo

theorem moise305_tame_of_lemmaTwoOrientable (lemmaTwo : LemmaTwoBufferedOrientableStatement) :
    Moise305Tame :=
  moise305_tame_of_lemmaTwoBufferedOrientable orientableCoverReductionStatement lemmaTwo

theorem moise304_of_generalPositionBuffered_of_descentStepOrientable
    (generalPosition : GeneralPositionInDoubleBufferedStatement)
    (descentStep : DescentStepOrientableStatement) : Moise304 :=
  moise304_of_generalPosition_of_descentStepOrientable orientableCoverReductionStatement
    generalPosition descentStep

end DifferentialGeometry.Topology.PiecewiseLinear
