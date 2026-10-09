/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
structure EmbeddedDisk (S : NormalSystem E) where
  domain : Set (EuclideanSpace ℝ (Fin 2))
  isPLBall_domain : IsPLBall 2 domain
  map : EuclideanSpace ℝ (Fin 2) → E
  isPLHomeomorphOn : IsPLHomeomorphOn map domain (map '' domain)
  mapsTo : MapsTo map domain S.manifoldComplex.space
  boundaryLoop : freeLoop S.boundaryNeighborhoodSpace
  boundary_range : range (fun θ => (boundaryLoop θ : E)) = map '' frontier domain
  boundary_preimage : domain ∩ map ⁻¹' S.boundaryComplex.space = frontier domain
  connector : Path S.basepoint (boundaryLoop 0)
  loopClass_avoids_normal :
    ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass S.basepoint boundaryLoop connector) S.normalSubgroup

theorem EmbeddedDisk.image_inter_boundaryComplex {S : NormalSystem E} (D : EmbeddedDisk S) :
    D.map '' D.domain ∩ S.boundaryComplex.space = D.map '' frontier D.domain := by
  rw [← image_inter_preimage, D.boundary_preimage]

open Classical in
theorem EmbeddedDisk.exists_boundaryLoop_of_comap {S : NormalSystem E} (D : EmbeddedDisk S)
    {V : Set E} (β : C(S.boundaryNeighborhoodSpace, V))
    (hβ : ∀ x, (β x : E) = (x : E)) {y : V} (hb : β S.basepoint = y)
    (N : Subgroup (FundamentalGroup V y)) [N.Normal]
    (hN : S.normalSubgroup = N.comap (FundamentalGroup.mapOfEq β hb)) :
    ∃ (γ : freeLoop V) (r : Path y (γ 0)),
      range (fun θ => (γ θ : E)) = D.map '' frontier D.domain ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass y γ r) N := by
  let γ := β.comp D.boundaryLoop
  let r : Path y (γ 0) := (D.connector.map β.continuous).cast hb.symm rfl
  have hrange : range (fun θ => (γ θ : E)) = D.map '' frontier D.domain := by
    rw [← D.boundary_range]
    congr 1
    funext θ
    exact hβ (D.boundaryLoop θ)
  have havoid : ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass S.basepoint D.boundaryLoop D.connector)
      (N.comap (FundamentalGroup.mapOfEq β hb)) := by
    rw [← hN]
    exact D.loopClass_avoids_normal
  exact ⟨γ, r, hrange,
    normalSystemLoopConjugacyClass_map_avoids β hb D.boundaryLoop D.connector N havoid⟩

variable [FiniteDimensional ℝ E]

theorem EmbeddedDisk.isPLBall_image {S : NormalSystem E} (D : EmbeddedDisk S) :
    IsPLBall 2 (D.map '' D.domain) :=
  D.isPLBall_domain.of_isPLHomeomorphOn D.isPLHomeomorphOn

open Classical in
noncomputable def NonsingularCell.embeddedDisk {S : NormalSystem E} (D : NonsingularCell S) :
    EmbeddedDisk S := by
  let h := D.exists_isPLHomeomorphOn_eqOn_boundary
  let f := Classical.choose h
  have hf := Classical.choose_spec h
  exact
    { domain := D.sourceComplex.space
      isPLBall_domain := D.source_isPLBall
      map := f
      isPLHomeomorphOn := hf.1
      mapsTo := hf.2.1
      boundaryLoop := D.boundaryLoop
      boundary_range := hf.2.2.2.2.2
      boundary_preimage := hf.2.2.2.1
      connector := D.connector
      loopClass_avoids_normal := D.loopClass_avoids_normal }

@[simp]
theorem NonsingularCell.embeddedDisk_domain {S : NormalSystem E} (D : NonsingularCell S) :
    D.embeddedDisk.domain = D.sourceComplex.space :=
  rfl

@[simp]
theorem NonsingularCell.embeddedDisk_boundaryLoop {S : NormalSystem E} (D : NonsingularCell S) :
    D.embeddedDisk.boundaryLoop = D.boundaryLoop :=
  rfl

open Classical in
theorem NonsingularCell.embeddedDisk_eqOn_boundary {S : NormalSystem E} (D : NonsingularCell S) :
    EqOn D.embeddedDisk.map (simplicialMap D.sourceComplex D.vertexMap)
      (frontier D.sourceComplex.space) :=
  (Classical.choose_spec D.exists_isPLHomeomorphOn_eqOn_boundary).2.2.1

open Classical in
theorem EmbeddedDisk.preimage_boundaryComplex_eq {S : NormalSystem E} (D : EmbeddedDisk S)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hSK : S.manifoldComplex.space ⊆ K.space)
    (hBK : S.boundaryNeighborhood.space ⊆ (PiecewiseLinear.boundaryComplex 3 K).space) :
    D.domain ∩ D.map ⁻¹' (PiecewiseLinear.boundaryComplex 3 K).space = frontier D.domain := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  apply Subset.antisymm
  · rintro x ⟨hx, hfx⟩
    exact D.boundary_preimage.subset ⟨hx,
      inter_boundaryComplex_space_subset_of_subset K S.manifoldComplex
        hK S.isManifold hSK ⟨D.mapsTo hx, hfx⟩⟩
  · intro x hx
    obtain ⟨θ, hθ⟩ := D.boundary_range.symm.subset (mem_image_of_mem D.map hx)
    refine ⟨D.boundary_preimage.superset hx |>.1, ?_⟩
    change D.map x ∈ (PiecewiseLinear.boundaryComplex 3 K).space
    rw [← hθ]
    exact hBK (D.boundaryLoop θ).2

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
