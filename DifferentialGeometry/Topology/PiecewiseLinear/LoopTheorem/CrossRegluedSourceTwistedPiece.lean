/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedTube
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def halfTurnSlabPiece (a : ℝ)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (hfin : K.faces.Finite) (hK : K.space ⊆ halfTurnSlab a) :
    PLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 halfTurnQuotient
      (halfTurnEuclideanProjection '' K.space) := by
  let _ : Finite K.faces := hfin.to_subtype
  let e := halfTurnSlabChart a
  have he := halfTurnSlabChart_mem_maximalAtlas a
  have hpoly : IsPolyhedron K.space := isPolyhedron_space K
  have hbij := ((halfTurnEuclideanProjection_injOn_slab a).mono hK).bijOn_image
  refine ⟨K, hfin, halfTurnEuclideanProjection, hbij,
    continuous_halfTurnEuclideanProjection.continuousOn, ?_, ?_⟩
  · intro e' he'
    have hc := (mem_plGroupoid_iff.mp
      (StructureGroupoid.compatible_of_mem_maximalAtlas he
        ((plGroupoid 3).subset_maximalAtlas he'))).1
    have h := hc.inter_of_isPolyhedron hpoly
    have hset : (e.symm.trans e').source ∩ K.space =
        K.space ∩ halfTurnEuclideanProjection ⁻¹' e'.source := by
      ext x
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hK hx.1, hx.2⟩, hx.1⟩⟩
    rw [hset] at h
    exact h.congr fun _ _ => rfl
  · intro e' he'
    have hc := (mem_plGroupoid_iff.mp
      (StructureGroupoid.compatible_of_mem_maximalAtlas
        ((plGroupoid 3).subset_maximalAtlas he') he)).1
    have h := hc.inter_preimage_of_isPolyhedron hpoly
    have himage : halfTurnEuclideanProjection '' K.space = e.source ∩ e ⁻¹' K.space :=
      e.symm_image_eq_source_inter_preimage hK
    have hset : (e'.symm.trans e).source ∩ (e'.symm.trans e) ⁻¹' K.space =
        e'.target ∩ e'.symm ⁻¹' (halfTurnEuclideanProjection '' K.space) := by
      rw [himage]
      ext x
      change ((x ∈ e'.target ∧ e'.symm x ∈ e.source) ∧ e (e'.symm x) ∈ K.space) ↔
        (x ∈ e'.target ∧ e'.symm x ∈ e.source ∧ e (e'.symm x) ∈ K.space)
      tauto
    rw [hset] at h
    refine h.congr fun x hx => ?_
    have hxy := hx.2
    rw [himage] at hxy
    change Function.invFunOn halfTurnEuclideanProjection K.space (e'.symm x) = e (e'.symm x)
    apply hbij.injOn (hbij.surjOn.mapsTo_invFunOn hx.2) hxy.2
    rw [hbij.invOn_invFunOn.2 hx.2]
    exact (e.left_inv hxy.1).symm

theorem halfTurnSlabPiece_complex (a : ℝ)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (hfin : K.faces.Finite) (hK : K.space ⊆ halfTurnSlab a) :
    (halfTurnSlabPiece a K hfin hK).complex = K := rfl

theorem halfTurnSlabPiece_map (a : ℝ)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (hfin : K.faces.Finite) (hK : K.space ⊆ halfTurnSlab a) :
    (halfTurnSlabPiece a K hfin hK).map = halfTurnEuclideanProjection := rfl

private noncomputable def twistedTubeAffine :
    ((ℝ × ℝ) × ℝ) →ᵃ[ℝ] ((ℝ × ℝ) × ℝ) :=
  let x := ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  let y := ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  let z := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
  (((1 / 16 : ℝ) • (x - y)).prod
    (AffineMap.const ℝ _ (-1 / 2) + (1 / 16 : ℝ) • (x + y))).prod z

private theorem twistedTubeAffine_apply (p : (ℝ × ℝ) × ℝ) :
    twistedTubeAffine p = twistedTubeLift p := by
  ext <;> dsimp [twistedTubeAffine, twistedTubeLift] <;> ring

noncomputable def twistedTubePlacement : ((ℝ × ℝ) × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
  twistedTubeLift.trans spliceEmbedding.toHomeomorph

theorem isPLHomeomorphOn_twistedTubePlacement {P : Set ((ℝ × ℝ) × ℝ)} (hP : IsPolyhedron P) :
    IsPLHomeomorphOn twistedTubePlacement P (twistedTubePlacement '' P) := by
  have hpa := (isPiecewiseAffineOn_of_affine twistedTubeAffine isOpen_univ).congr
    (fun p _ => (twistedTubeAffine_apply p).symm)
  have hcomp := hpa.affine_comp spliceEmbedding.toLinearMap.toAffineMap
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
    (hcomp.mono_of_isPolyhedron hP (subset_univ _))
    twistedTubePlacement.injective.injOn.bijOn_image

theorem halfTurnEuclideanProjection_comp_twistedTubePlacement :
    halfTurnEuclideanProjection ∘ twistedTubePlacement = twistedTubeChart := by
  funext p
  change halfTurnProjection (spliceEmbedding.symm (spliceEmbedding (twistedTubeLift p))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem nonempty_plSeamTubeChart_twistedTubeChart :
    Nonempty (PLSeamTubeChart halfTurnQuotient twistedTubeChart) := by
  obtain ⟨K, hfin, hspace⟩ := isHPolytope_spliceCylinder.isPolyhedron.exists_simplicialComplex
  have hPL := isPLHomeomorphOn_twistedTubePlacement isHPolytope_spliceCylinder.isPolyhedron
  have hpoly := isHPolytope_spliceCylinder.isPolyhedron.image_of_isPiecewiseAffineOn
    hPL.isPiecewiseAffineOn hPL.bijOn.injOn
  obtain ⟨L, hLfin, hLspace⟩ := hpoly.exists_simplicialComplex
  have hslab : L.space ⊆ halfTurnSlab 0 := by
    rw [hLspace]
    rintro _ ⟨p, hp, rfl⟩
    change (spliceEmbedding.symm (spliceEmbedding (twistedTubeLift p))).1.1 ∈
      Ioo (0 - 1 / 4) (0 + 1 / 4)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    have h := mem_spliceSquare.mp hp.1
    change 0 - 1 / 4 < (p.1.1 - p.1.2) / 16 ∧
      (p.1.1 - p.1.2) / 16 < 0 + 1 / 4
    constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
  let T := halfTurnSlabPiece 0 L hLfin hslab
  have hparam : IsPLHomeomorphOn twistedTubePlacement K.space T.complex.space := by
    change IsPLHomeomorphOn twistedTubePlacement K.space L.space
    rw [hspace, hLspace]
    exact hPL
  let S := T.precomp K hfin hparam
  have hmap : S.map = twistedTubeChart := halfTurnEuclideanProjection_comp_twistedTubePlacement
  have himage : halfTurnEuclideanProjection '' L.space = twistedTubeChart '' spliceCylinder := by
    rw [hLspace, ← image_comp, halfTurnEuclideanProjection_comp_twistedTubePlacement]
  have hbij : BijOn twistedTubeChart K.space (twistedTubeChart '' spliceCylinder) := by
    rw [hspace]
    exact twistedTubeChart_injOn.bijOn_image
  refine ⟨⟨⟨K, hfin, twistedTubeChart, hbij, ?_, ?_, ?_⟩, hspace, rfl⟩⟩
  · rw [hspace]
    exact continuous_twistedTubeChart.continuousOn
  · intro e he
    have h := S.isPiecewiseAffineOn_chart e he
    change IsPiecewiseAffineOn (e ∘ S.map) (K.space ∩ S.map ⁻¹' e.source) at h
    rwa [hmap] at h
  · intro e he
    have h := S.isPiecewiseAffineOn_chart_symm e he
    change IsPiecewiseAffineOn (Function.invFunOn S.map K.space ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' (halfTurnEuclideanProjection '' L.space)) at h
    rwa [hmap, himage] at h

theorem twistedStripCell_exists_boundaryTube :
    ∃ C : PLSeamTubeChart halfTurnQuotient twistedTubeChart,
      C.piece.map = twistedTubeChart ∧
      CrossSeamTubeCore twistedTubeChart
        (⇑twistedStripCell '' twistedStripCell.domain)
        (doublePointSet (⇑twistedStripCell) twistedStripCell.domain)
        (doublePointSet (⇑twistedStripCell) twistedStripCell.domain)
        (halfTurnSlabChart 0).source ∧
      twistedTubeChart '' spliceCylinder ⊆ twistedStripSide ∧
      twistedTubeChart '' spliceCylinder ∩ frontier twistedStripSide =
        twistedTubeChart '' spliceEndDisks ∧
      twistedTubeChart '' crossingFigure ⊂ ⇑twistedStripCell '' twistedStripCell.domain := by
  obtain ⟨C⟩ := nonempty_plSeamTubeChart_twistedTubeChart
  exact ⟨C, C.map_eq, crossSeamTubeCore_twistedStripCell, twistedTubeChart_side,
    twistedTubeChart_boundary, twistedTubeChart_crossingFigure_ssubset_image⟩

theorem isPLHomeomorphOn_twistedTubeLift :
    IsPLHomeomorphOn twistedTubeLift univ univ := by
  have hpa := (isPiecewiseAffineOn_of_affine twistedTubeAffine isOpen_univ).congr
    (fun p _ => (twistedTubeAffine_apply p).symm)
  exact isPLHomeomorphOn_openPartialHomeomorph twistedTubeLift.toOpenPartialHomeomorph hpa

end DifferentialGeometry.Topology.PiecewiseLinear
