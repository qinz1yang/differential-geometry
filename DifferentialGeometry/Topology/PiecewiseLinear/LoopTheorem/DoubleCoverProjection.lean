/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.EmbeddedProjection
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaThree

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem mapOfEq_loopRepresentativeAlong
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (γ : freeLoop X) (q : Path x (γ 0)) :
    FundamentalGroup.mapOfEq f h (loopRepresentativeAlong q ⟨γ, rfl⟩) =
      loopRepresentativeAlong ((q.map f.continuous).cast h.symm rfl) ⟨f.comp γ, rfl⟩ := by
  subst y
  rw [FundamentalGroup.mapOfEq_apply]
  unfold loopRepresentativeAlong basedCircleFundamentalGroupClass
  rw [fundamentalGroupChangeBasepoint_apply, fundamentalGroupChangeBasepoint_apply]
  change Path.Homotopic.Quotient.mk
      (((q.trans (circleToPath ⟨γ, rfl⟩)).trans q.symm).map f.continuous) =
    Path.Homotopic.Quotient.mk
      (((q.map f.continuous).trans (circleToPath ⟨f.comp γ, rfl⟩)).trans
        (q.map f.continuous).symm)
  congr 1
  rw [Path.map_trans, Path.map_trans, Path.map_symm]
  rfl

open Classical in
theorem normalSystemLoopConjugacyClass_map_avoids
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (γ : freeLoop X) (q : Path x (γ 0))
    (N : Subgroup (FundamentalGroup Y y)) [N.Normal]
    (havoid : ¬conjugacyClassMeets (normalSystemLoopConjugacyClass x γ q)
      (N.comap (FundamentalGroup.mapOfEq f h))) :
    ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass y (f.comp γ) ((q.map f.continuous).cast h.symm rfl))
      N := by
  intro hmeet
  have hmem := (conjugacyClassMeets_iff_carrier_subset _ N).mp hmeet
    (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl)
  apply havoid
  refine ⟨loopRepresentativeAlong q ⟨γ, rfl⟩,
    ConjClasses.mem_carrier_iff_mk_eq.mpr rfl, ?_⟩
  change FundamentalGroup.mapOfEq f h (loopRepresentativeAlong q ⟨γ, rfl⟩) ∈ N
  rw [mapOfEq_loopRepresentativeAlong]
  exact hmem

namespace NormalSystem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem manifoldComplex_space_subset_ambient (S : NormalSystem E) :
    S.manifoldComplex.space ⊆ S.ambientComplex.space := by
  rw [S.manifold_space]
  exact derivedNeighborhood_space_subset S.ambientComplex S.imageComplex

open Classical in
theorem DoubleCoverDiagram.complexity_le {S : NormalSystem E} {T : NormalSystem F}
    (R : DoubleCoverDiagram S T) : T.complexity ≤ S.complexity := by
  let _ : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  let _ : Finite T.sourceComplex.faces := T.finite_source.to_subtype
  have hfactor : ∀ v ∈ S.sourceComplex.vertices, R.projection (T.vertexMap v) = S.vertexMap v := by
    intro v hv
    have hvT : v ∈ T.sourceComplex.vertices := R.sourceComplex_eq.symm ▸ hv
    have h := R.source_lift (S.sourceComplex.vertices_subset_space hv)
    change R.projection (simplicialMap T.sourceComplex T.vertexMap v) =
      simplicialMap S.sourceComplex S.vertexMap v at h
    rwa [simplicialMap_vertex T.sourceComplex T.vertexMap hvT,
      simplicialMap_vertex S.sourceComplex S.vertexMap hv] at h
  change simplicialComplexity T.sourceComplex T.vertexMap ≤
    simplicialComplexity S.sourceComplex S.vertexMap
  have h := simplicialComplexity_le_of_factorization S.sourceComplex
    S.vertexMap T.vertexMap R.projection hfactor
  simpa only [R.sourceComplex_eq] using h

open Classical in
theorem DoubleCoverDiagram.exists_projected_disk_of_embedding
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : NonsingularCell T) {g : EuclideanSpace ℝ (Fin 2) → F}
    (hg : IsPiecewiseAffineOn g D.sourceComplex.space) (hginj : InjOn g D.sourceComplex.space)
    (hgmap : MapsTo g D.sourceComplex.space T.manifoldComplex.space)
    (hgfix : EqOn g (simplicialMap D.sourceComplex D.vertexMap) (frontier D.sourceComplex.space)) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → E) (γ : freeLoop S.boundaryNeighborhoodSpace)
      (q : Path S.basepoint (γ 0)),
      f = R.projection ∘ g ∧
      IsPiecewiseAffineOn f D.sourceComplex.space ∧
      MapsTo f D.sourceComplex.space S.manifoldComplex.space ∧
      (∀ x ∈ D.sourceComplex.space, ∃ U ∈ 𝓝[D.sourceComplex.space] x, InjOn f U) ∧
      (∀ y, (D.sourceComplex.space ∩ f ⁻¹' {y}).encard ≤ 2) ∧
      range (fun θ => (γ θ : E)) = f '' frontier D.sourceComplex.space ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup := by
  have hmap : MapsTo g D.sourceComplex.space T.ambientComplex.space := fun _ hx =>
    T.manifoldComplex_space_subset_ambient
      (hgmap hx)
  have hpl : IsPiecewiseAffineOn (R.projection ∘ g) D.sourceComplex.space := by
    have h := R.isPiecewiseAffineOn_projection.comp hg
    have hinter : D.sourceComplex.space ∩ g ⁻¹' T.ambientComplex.space =
        D.sourceComplex.space := inter_eq_left.mpr hmap
    rwa [hinter] at h
  obtain ⟨hloc, htwo⟩ := Covering.locally_injective_fiber_le_of_isCoveringMap_restrict
    R.isCoveringMap (fun _ => rfl) hg.continuousOn hginj hmap
    (fun y => (R.fiber_card y).le)
  let γ := R.boundaryMap.comp D.boundaryLoop
  let q : Path S.basepoint (γ 0) :=
    (D.connector.map R.boundaryMap.continuous).cast R.basepoint_eq.symm rfl
  have hboundary : range (fun θ => (γ θ : E)) =
      (R.projection ∘ g) '' frontier D.sourceComplex.space := by
    calc
      range (fun θ => (γ θ : E)) =
          range (R.projection ∘ fun θ => (D.boundaryLoop θ : F)) := by
        congr 1
        funext θ
        exact R.boundaryMap_eq (D.boundaryLoop θ)
      _ = R.projection '' range (fun θ => (D.boundaryLoop θ : F)) := range_comp _ _
      _ = R.projection '' (g '' frontier D.sourceComplex.space) := by
        rw [D.boundary_range, ← hgfix.image_eq]
      _ = (R.projection ∘ g) '' frontier D.sourceComplex.space := (image_comp _ _ _).symm
  let _ : S.normalSubgroup.Normal := S.normal
  have havoid : ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass T.basepoint D.boundaryLoop D.connector)
      (S.normalSubgroup.comap (FundamentalGroup.mapOfEq R.boundaryMap R.basepoint_eq)) := by
    rw [← R.normalSubgroup_eq]
    exact D.loopClass_avoids_normal
  exact ⟨R.projection ∘ g, γ, q, rfl, hpl, R.projection_mapsTo.comp hmap,
    hloc, htwo, hboundary, normalSystemLoopConjugacyClass_map_avoids
      R.boundaryMap R.basepoint_eq D.boundaryLoop D.connector S.normalSubgroup havoid⟩

open Classical in
theorem DoubleCoverDiagram.exists_projected_disk
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : NonsingularCell T) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → E) (γ : freeLoop S.boundaryNeighborhoodSpace)
      (q : Path S.basepoint (γ 0)),
      f = R.projection ∘ simplicialMap D.sourceComplex D.vertexMap ∧
      IsPiecewiseAffineOn f D.sourceComplex.space ∧
      MapsTo f D.sourceComplex.space S.manifoldComplex.space ∧
      (∀ x ∈ D.sourceComplex.space, ∃ U ∈ 𝓝[D.sourceComplex.space] x, InjOn f U) ∧
      (∀ y, (D.sourceComplex.space ∩ f ⁻¹' {y}).encard ≤ 2) ∧
      range (fun θ => (γ θ : E)) = f '' frontier D.sourceComplex.space ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup := by
  let _ : Finite D.sourceComplex.faces := D.finite_source.to_subtype
  exact R.exists_projected_disk_of_embedding D
    (isPiecewiseAffineOn_simplicialMap D.sourceComplex D.vertexMap) D.nonsingular
    (simplicialMap_mapsTo D.sourceComplex T.manifoldComplex D.vertexMap D.source_faces_map)
    (fun _ _ => rfl)

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
