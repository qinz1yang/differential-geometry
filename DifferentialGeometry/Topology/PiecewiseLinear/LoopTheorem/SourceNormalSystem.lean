/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDisk
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSimplexBoundaryNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialImageIn

open Set Topology

private noncomputable local instance euclideanDecidableEq (N : ℕ) :
    DecidableEq (EuclideanSpace ℝ (Fin N)) := Classical.decEq _

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_simplicialMap_derivedNeighborhood_of_isPiecewiseAffineOn
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P)
    {f : EuclideanSpace ℝ (Fin 2) → E} (hf : IsPiecewiseAffineOn f P)
    (hmap : MapsTo f P K.space)
    (hboundary : MapsTo f (frontier P) (boundaryComplex 3 K).space)
    {V : Set E} (hV : V ∈ 𝓝ˢ[(boundaryComplex 3 K).space] (f '' frontier P)) :
    ∃ (D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (L A C : Geometry.SimplicialComplex ℝ E) (g : EuclideanSpace ℝ (Fin 2) → E)
      (T : DerivedNeighborhoodTriangulation L A),
      D.faces.Finite ∧ L.faces.Finite ∧ D.space = P ∧ IsSubdivision L K ∧
      A.faces ⊆ L.faces ∧ C.faces ⊆ A.faces ∧
      (∀ s ∈ D.faces, s.image g ∈ A.faces) ∧
      A.space = simplicialMap D g '' D.space ∧
      C.space = simplicialMap D g '' frontier P ∧
      EqOn (simplicialMap D g) f (frontier P) ∧
      IsCombinatorialManifoldWithBoundary 3 T.complex ∧
      C.faces ⊆ (boundaryComplex 3 T.complex).faces ∧
      A.space ∩ (boundaryComplex 3 T.complex).space = C.space ∧
      D.space ∩ (simplicialMap D g) ⁻¹' (boundaryComplex 3 T.complex).space = frontier P ∧
      (derivedNeighborhood (boundaryComplex 3 T.complex) C).space ⊆
        (boundaryComplex 3 K).space ∩ V := by
  have hfront : IsPolyhedron (frontier P) := hP.isPLSphere_frontier.isPolyhedron
  have hfrontP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  obtain ⟨g, hg, hgmap, hgfix, hgpre, -⟩ :=
    hK.exists_isPiecewiseAffineOn_eqOn_preimage_boundary K hP.isPolyhedron hfront
      hfrontP hf hmap hboundary
  obtain ⟨D₀, hD₀fin, hD₀space⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite D₀.faces := hD₀fin.to_subtype
  have hgD : IsPiecewiseAffineOn g D₀.space := hD₀space.symm ▸ hg
  obtain ⟨D, L, hDfin, hLfin, hD, hL, hfaces, hfg⟩ :=
    hgD.exists_isSubdivision_simplicialMap D₀ K (hD₀space.symm ▸ hgmap)
  let _ : Finite D.faces := hDfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hDspace : D.space = P := hD.space_eq.trans hD₀space
  have hDball : IsPLBall 2 D.space := hDspace.symm ▸ hP
  have hDfront : frontier P = (boundaryComplex 2 D).space := by
    rw [← hDspace]
    exact frontier_space_eq_boundaryComplex_space hDball.isCombinatorialManifoldWithBoundary
  have hLmanifold := hK.of_isSubdivision hL
  have hid : IsPLHomeomorphOn id K.space L.space := by
    rw [hL.space_eq]
    exact (isPolyhedron_space K).isPLHomeomorphOn_id
  have hLbd : (boundaryComplex 3 L).space = (boundaryComplex 3 K).space := by
    simpa only [image_id] using boundaryComplex_space_of_isPLHomeomorphOn K L hK hid
  have heq : EqOn (simplicialMap D g) g P := hD₀space ▸ hfg
  have hfix : EqOn (simplicialMap D g) f (frontier P) :=
    (heq.mono hfrontP).trans hgfix
  have hproper : D.space ∩ (simplicialMap D g) ⁻¹' (boundaryComplex 3 L).space =
      frontier P := by
    rw [hDspace, hLbd, ← hgpre]
    ext x
    apply and_congr_right
    intro hx
    change simplicialMap D g x ∈ (boundaryComplex 3 K).space ↔
      g x ∈ (boundaryComplex 3 K).space
    rw [heq hx]
  obtain ⟨A, hAfin, hAL, hAfaces, hAspace⟩ :=
    exists_finite_subcomplex_space_eq_image_simplicialMap D L g hfaces
  let B := boundaryComplex 2 D
  let _ : Finite B.faces := (boundaryComplex_faces_finite 2 D).to_subtype
  obtain ⟨C, hCfin, hCL, hCfaces, hCspace⟩ :=
    exists_finite_subcomplex_space_eq_image_simplicialMap B L g
      (fun s hs => hfaces s (boundaryComplex_faces_subset 2 D hs))
  have hCA : C.faces ⊆ A.faces := by
    rw [hCfaces, hAfaces]
    rintro t ⟨s, hs, rfl⟩
    exact ⟨s, boundaryComplex_faces_subset 2 D hs, rfl⟩
  have hCspace' : C.space = simplicialMap D g '' frontier P := by
    rw [hDfront]
    exact hCspace.trans (simplicialMap_eqOn_of_faces_subset D B
      (boundaryComplex_faces_subset 2 D) g).image_eq.symm
  have hCimage : C.space = f '' frontier P := hCspace'.trans hfix.image_eq
  have htrace : A.space ∩ (boundaryComplex 3 L).space = C.space := by
    rw [hAspace, hCspace']
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, rfl⟩, hxb⟩
      exact ⟨x, hproper.subset ⟨hx, hxb⟩, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨⟨x, hDspace.symm ▸ hfrontP hx, rfl⟩, (hproper.superset hx).2⟩
  have hVC : V ∈ 𝓝ˢ[(boundaryComplex 3 L).space] C.space := by
    rw [hLbd, hCimage]
    exact hV
  obtain ⟨T, hCT, hTV⟩ := hLmanifold.exists_derivedNeighborhoodTriangulation_boundary_mem
    L A C hAL hCA htrace hVC
  have htraceT : A.space ∩ (boundaryComplex 3 T.complex).space = C.space :=
    (T.inter_boundaryComplex_space hLmanifold hAL).trans htrace
  have hproperT : D.space ∩ (simplicialMap D g) ⁻¹'
      (boundaryComplex 3 T.complex).space = frontier P := by
    rw [← hproper]
    ext x
    apply and_congr_right
    intro hx
    exact T.mem_boundaryComplex_iff hLmanifold hAL
      (hAspace.symm ▸ mem_image_of_mem (simplicialMap D g) hx)
  refine ⟨D, L, A, C, g, T, hDfin, hLfin, hDspace, hL, hAL, hCA, ?_, hAspace,
    hCspace', hfix, T.isCombinatorialManifoldWithBoundary hLmanifold, hCT,
    htraceT, hproperT, fun x hx => ⟨hLbd ▸ (hTV hx).1, (hTV hx).2⟩⟩
  intro s hs
  rw [hAfaces]
  exact ⟨s, hs, rfl⟩

open Classical in
theorem exists_normalSystem_of_isPiecewiseAffineOn
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P)
    {f : EuclideanSpace ℝ (Fin 2) → E} (hf : IsPiecewiseAffineOn f P)
    (hmap : MapsTo f P K.space)
    (hboundary : MapsTo f (frontier P) (boundaryComplex 3 K).space)
    {V : Set E} (hV : V ∈ 𝓝ˢ[(boundaryComplex 3 K).space] (f '' frontier P))
    (e : loopCircle ≃ₜ frontier P) (γ : freeLoop V)
    (hγ : ∀ θ, (γ θ : E) = f (e θ))
    (N : Subgroup (FundamentalGroup V (γ 0))) [N.Normal]
    (havoid : ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass (γ 0) γ (Path.refl (γ 0))) N) :
    ∃ S : NormalSystem E,
      S.sourceComplex.space = P ∧ IsSubdivision S.ambientComplex K ∧
      EqOn S.singularMap f (frontier P) ∧
      (∀ θ, (S.boundaryParam θ : EuclideanSpace ℝ (Fin 2)) = e θ) ∧
      S.basepoint = S.boundaryLoop 0 ∧
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space = frontier P ∧
      S.boundaryNeighborhood.space ⊆ (boundaryComplex 3 K).space ∩ V ∧
      ∃ (β : C(S.boundaryNeighborhoodSpace, V)) (hb : β S.basepoint = γ 0),
        (∀ x, (β x : E) = (x : E)) ∧ β.comp S.boundaryLoop = γ ∧
        S.normalSubgroup = N.comap (FundamentalGroup.mapOfEq β hb) := by
  obtain ⟨D, L, A, C, g, T, hDfin, hLfin, hDspace, hL, hAL, -, hfaces, hAspace,
    hCspace, hfix, hT, hCT, htrace, hproper, hTV⟩ :=
    exists_simplicialMap_derivedNeighborhood_of_isPiecewiseAffineOn
      K hK hP hf hmap hboundary hV
  let _ : Finite D.faces := hDfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite (boundaryComplex 3 T.complex).faces :=
    (boundaryComplex_faces_finite 3 T.complex).to_subtype
  let B := normalSystemBoundaryNeighborhood T C
  let φ := simplicialMap D g
  let e' : loopCircle ≃ₜ frontier D.space :=
    e.trans (Homeomorph.setCongr (congrArg frontier hDspace.symm))
  have he' (θ : loopCircle) : (e' θ : EuclideanSpace ℝ (Fin 2)) = e θ := rfl
  have hfront : frontier D.space ⊆ D.space := (isPolyhedron_space D).isClosed.frontier_subset
  have hCB : C.space ⊆ B.space := by
    change C.space ⊆ (derivedNeighborhood (boundaryComplex 3 T.complex) C).space
    exact subcomplex_space_subset_derivedNeighborhood hCT
  have hφbd (θ : loopCircle) : φ (e' θ) ∈ B.space := by
    rw [he']
    exact hCB (hCspace.symm ▸ mem_image_of_mem φ (e θ).2)
  let a : C(loopCircle, D.space) :=
    ⟨fun θ => ⟨e' θ, hfront (e' θ).2⟩,
      (continuous_subtype_val.comp e'.continuous).subtype_mk _⟩
  let δ : freeLoop B.space :=
    ⟨fun θ => ⟨φ (e' θ), hφbd θ⟩,
      (((isPiecewiseAffineOn_simplicialMap D g).continuousOn.domRestrict).comp
        a.continuous).subtype_mk _⟩
  let β : C(B.space, V) :=
    ⟨fun x => ⟨x, (hTV x.2).2⟩, continuous_subtype_val.subtype_mk _⟩
  have hβδ : β.comp δ = γ := by
    ext θ
    change φ (e' θ) = (γ θ : E)
    rw [he']
    exact (hfix (e θ).2).trans (hγ θ).symm
  have hb : β (δ 0) = γ 0 := congrArg (fun α : freeLoop V => α 0) hβδ
  let H := N.comap (FundamentalGroup.mapOfEq β hb)
  have havoidMapped (η : freeLoop V) (hη : η = γ) (r : Path (γ 0) (η 0)) :
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass (γ 0) η r) N := by
    subst η
    have heq : normalSystemLoopConjugacyClass (γ 0) γ r =
        normalSystemLoopConjugacyClass (γ 0) γ (Path.refl (γ 0)) :=
      ConjClasses.mk_eq_mk_iff_isConj.mpr
        (loopRepresentativeAlong_isConj r (Path.refl (γ 0)) ⟨γ, rfl⟩)
    rw [heq]
    exact havoid
  have havoid' : ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass (δ 0) δ (Path.refl (δ 0))) H := by
    intro hmeet
    have hmem := (conjugacyClassMeets_iff_carrier_subset _ H).mp hmeet
      (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl)
    change FundamentalGroup.mapOfEq β hb
      (loopRepresentativeAlong (Path.refl (δ 0)) ⟨δ, rfl⟩) ∈ N at hmem
    rw [mapOfEq_loopRepresentativeAlong] at hmem
    exact havoidMapped (β.comp δ) hβδ
      (((Path.refl (δ 0)).map β.continuous).cast hb.symm rfl)
      ⟨_, ConjClasses.mem_carrier_iff_mk_eq.mpr rfl, hmem⟩
  let S : NormalSystem E :=
    { ambientComplex := L
      imageComplex := A
      loopComplex := C
      sourceComplex := D
      finite_ambient := hLfin
      finite_source := hDfin
      source_isPLBall := hDspace.symm ▸ hP
      vertexMap := g
      source_faces_map := hfaces
      image_space := hAspace
      image_faces_subset_ambient := hAL
      neighborhood := T
      isManifold := hT
      loop_space := hCspace.trans (congrArg (φ '' ·) (congrArg frontier hDspace).symm)
      loop_faces_subset_boundary := hCT
      image_inter_boundary := htrace
      basepoint := δ 0
      boundaryLoop := δ
      boundaryParam := e'
      boundaryLoop_eq := fun _ => rfl
      connector := Path.refl _
      normalSubgroup := H
      normal := inferInstance
      loopClass_avoids_normal := havoid' }
  exact ⟨S, hDspace, hL, hfix, he', rfl, hproper, hTV,
    β, hb, fun _ => rfl, hβδ, rfl⟩
namespace NormalSystem

open Classical in
theorem NonsingularCell.exists_isPLHomeomorphOn_boundaryLoop_of_comap
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {S : NormalSystem E} (D : NonsingularCell S)
    (hSK : S.manifoldComplex.space ⊆ K.space)
    (hBK : S.boundaryNeighborhood.space ⊆ (PiecewiseLinear.boundaryComplex 3 K).space)
    {V : Set E} (β : C(S.boundaryNeighborhoodSpace, V))
    (hβ : ∀ x, (β x : E) = (x : E)) {y : V} (hb : β S.basepoint = y)
    (N : Subgroup (FundamentalGroup V y)) [N.Normal]
    (hN : S.normalSubgroup = N.comap (FundamentalGroup.mapOfEq β hb)) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → E) (γ : freeLoop V) (q : Path y (γ 0)),
      IsPLHomeomorphOn f D.sourceComplex.space (f '' D.sourceComplex.space) ∧
      MapsTo f D.sourceComplex.space K.space ∧
      EqOn f (simplicialMap D.sourceComplex D.vertexMap) (frontier D.sourceComplex.space) ∧
      D.sourceComplex.space ∩ f ⁻¹' (PiecewiseLinear.boundaryComplex 3 K).space =
        frontier D.sourceComplex.space ∧
      f '' D.sourceComplex.space ∩ (PiecewiseLinear.boundaryComplex 3 K).space =
        f '' frontier D.sourceComplex.space ∧
      range (fun θ => (γ θ : E)) = f '' frontier D.sourceComplex.space ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass y γ q) N := by
  let A := D.embeddedDisk
  obtain ⟨γ, r, hrange, havoid⟩ := A.exists_boundaryLoop_of_comap β hβ hb N hN
  have hpre := A.preimage_boundaryComplex_eq K hK hSK hBK
  have hinter : A.map '' A.domain ∩ (PiecewiseLinear.boundaryComplex 3 K).space =
      A.map '' frontier A.domain := by
    rw [← image_inter_preimage, hpre]
  exact ⟨A.map, γ, r, A.isPLHomeomorphOn, A.mapsTo.mono_right hSK,
    D.embeddedDisk_eqOn_boundary, hpre, hinter, hrange, havoid⟩

end NormalSystem
end DifferentialGeometry.Topology.PiecewiseLinear
