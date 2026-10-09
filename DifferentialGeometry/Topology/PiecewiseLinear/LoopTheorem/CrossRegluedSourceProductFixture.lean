/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductCut
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductSide
import
  DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductTubeReading

open Set Topology
open DifferentialGeometry.Topology.Homotopy

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem crossingProductCell_doublePointSet_resolved {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (C : PLSeamTubeChart (EuclideanSpace ℝ (Fin 3)) (crossingProductTubeChart r hr.ne')) :
    doublePointSet ((crossRegluedProductTubeReading hr hr1).resolvedCell C)
      ((crossRegluedProductTubeReading hr hr1).resolvedCell C).domain =
        crossingProductBranchCarrier true := by
  obtain ⟨hD, c, _, _, _, _, _, _, hc, _, hG, _⟩ :=
    crossingProductCell_exists_crossReading (subset_univ (Set.range crossingProductCell.boundary))
  let T : CrossSeamTubeData hD c (spliceEmbedding '' tubeWitnessTube) := {
    chart := crossingProductTubeChart r hr.ne'
    isTube := by
      rw [hc]
      exact crossSeamTubeCore_crossingProductTubeChart hr hr1 }
  have hGD := hD.doublePointSet_eq_of_isCrossRegluedCell hG
  have hres := CrossSeamRegluedData.doublePointSet_cell_eq
    ((crossRegluedProductTubeReading hr hr1).toCrossSeamRegluedData T C)
      (congrArg (fun S => S \ T.chart '' spliceCylinder) hGD)
  change doublePointSet ((crossRegluedProductTubeReading hr hr1).resolvedCell C)
      ((crossRegluedProductTubeReading hr hr1).resolvedCell C).domain = _ at hres
  rw [hres, hc, ← iUnion_crossingProductBranchCarrier]
  have hcore : spliceEmbedding '' spliceCore = crossingProductBranchCarrier false := rfl
  rw [hcore]
  ext z
  constructor
  · rintro ⟨hz, hnot⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    cases i
    · exact False.elim (hnot hi)
    · exact hi
  · intro hz
    exact ⟨mem_iUnion.mpr ⟨true, hz⟩,
      Set.disjoint_right.mp (pairwise_disjoint_crossingProductBranchCarrier
        (by decide : false ≠ true)) hz⟩

theorem crossingProductCell_exists_buffered_preserving_boundaryWordWitnesses :
    ∃ (B : Set (EuclideanSpace ℝ (Fin 3)))
      (hD : NormalSingularCellData crossingProductCell (frontier crossingProductSide) B)
      (c d : hD.singularSet.Branch) (r : ℝ) (hr : 0 < r)
      (T : CrossSeamTubeData hD c (spliceEmbedding '' tubeWitnessTube))
      (R : PLCrossSeamReading T.chart crossRegluedProductCell)
      (C : PLSeamTubeChart (EuclideanSpace ℝ (Fin 3)) T.chart)
      (f : frontier crossingProductCell.domain → B)
      (a b : B) (σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a)
      (Gd : SingularTwoCell (EuclideanSpace ℝ (Fin 3))),
      IsPolyhedron B ∧ B ⊆ frontier crossingProductSide ∧
      Nonempty (StrongDeformationRetract {z : B | (z : EuclideanSpace ℝ (Fin 3)) ∈
        Set.range crossingProductCell.boundary}) ∧
      IsPLBoundarySide crossingProductCell crossingProductSide (frontier crossingProductSide) ∧
      hD.singularSet.complexity = 2 ∧ c ≠ d ∧
      hD.singularSet.IsBoundaryBranch c ∧ hD.singularSet.IsBoundaryBranch d ∧
      hD.singularSet.branchCarrier c = spliceEmbedding '' spliceCore ∧
      hD.singularSet.branchCarrier d = crossingProductBranchCarrier true ∧
      r ≤ 1 ∧ T.chart = ⇑(crossingProductTubeChart r hr.ne') ∧
      R.tubeSource ⊂ crossRegluedProductCell.domain ∧
      T.chart '' spliceCylinder ⊆ crossingProductSide ∧
      T.chart '' spliceCylinder ∩ frontier crossingProductSide = T.chart '' spliceEndDisks ∧
      (∀ z ∈ Set.range crossingProductCell.boundary,
        B ∈ 𝓝[frontier crossingProductSide] z) ∧
      (∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[frontier crossingProductSide] z) ∧
      Continuous f ∧ (∀ z, (f z : EuclideanSpace ℝ (Fin 3)) = crossingProductCell z) ∧
      hD.IsBoundarySurgeryCell c Gd ∧ hD.IsCrossRegluedCell c crossRegluedProductCell ∧
      doublePointSet (R.resolvedCell C) (R.resolvedCell C).domain =
        hD.singularSet.branchCarrier d ∧
      Nonempty (BoundaryWordWitness Gd (Subtype.val : B → EuclideanSpace ℝ (Fin 3))
        (pathToCircle (σ.trans υ))) ∧
      Nonempty (BoundaryWordWitness crossRegluedProductCell
        (Subtype.val : B → EuclideanSpace ℝ (Fin 3))
        (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))) ∧
      ∃ (p q u v : frontier crossingProductCell.domain)
        (σ₀ : Path p q) (τ₀ : Path q u) (υ₀ : Path u v) (φ₀ : Path v p)
        (e : loopCircle ≃ₜ frontier crossingProductCell.domain),
        (p : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (3 / 2, 0) ∧
        (q : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (3 / 2, 1) ∧
        (u : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (7 / 2, 1) ∧
        (v : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (7 / 2, 0) ∧
        (∀ θ, e θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ) ∧
        Function.Injective σ₀ ∧ Function.Injective τ₀ ∧
        Function.Injective υ₀ ∧ Function.Injective φ₀ ∧
        (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧
        (∀ t, υ t = f (υ₀ t)) ∧ (∀ t, φ t = f (φ₀ t)) := by
  obtain ⟨B, hBpoly, hBside, hBcore, hBbuf, hBret⟩ :=
    crossingProductCell_exists_boundary_regularNeighborhood
  obtain ⟨hD, c, d, _, hcomplexity, hcd, hcbd, hdbd, hc, hd, hG, _⟩ :=
    crossingProductCell_exists_crossReading hBcore
  obtain ⟨r, hr, hr1, hendbuf⟩ := crossingProductCell_exists_tube_end_buffer hBbuf
  let T : CrossSeamTubeData hD c (spliceEmbedding '' tubeWitnessTube) := {
    chart := crossingProductTubeChart r hr.ne'
    isTube := by
      rw [hc]
      exact crossSeamTubeCore_crossingProductTubeChart hr hr1 }
  let R : PLCrossSeamReading T.chart crossRegluedProductCell :=
    crossRegluedProductTubeReading hr hr1
  obtain ⟨C⟩ := nonempty_plSeamTubeChart_crossingProductTubeChart hr.ne'
  let f : frontier crossingProductCell.domain → B :=
    fun z => ⟨crossingProductCell z, hBcore ⟨z, rfl⟩⟩
  have hf : Continuous f := crossingProductCell.boundary.continuous.subtype_mk _
  have hfρ : ∀ z, (f z : EuclideanSpace ℝ (Fin 3)) = crossingProductCell z := fun _ => rfl
  obtain ⟨p, q, u, v, σ₀, τ₀, υ₀, φ₀, e, a, b, σ, τ, υ, φ, Gd,
    hp, hq, hu, hv, he, hσinj, hτinj, hυinj, hφinj, hσ, hτ, hυ, hφ, hGd, Wd, Wc⟩ :=
    crossingProductCell_exists_preserving_boundaryWordWitnesses hD hc
      IsEmbedding.subtypeVal f hf hfρ
  refine ⟨B, hD, c, d, r, hr, T, R, C, f, a, b, σ, τ, υ, φ, Gd,
    hBpoly, hBside, hBret, isPLBoundarySide_crossingProductCell,
    hcomplexity, hcd, hcbd, hdbd, hc, hd, hr1, rfl,
    crossRegluedProductTubeReading_tubeSource_ssubset hr hr1,
    crossingProductTubeChart_side hr hr1, crossingProductTubeChart_boundary hr hr1,
    hBbuf, hendbuf, hf, hfρ, hGd, hG, ?_, Wd, Wc,
    p, q, u, v, σ₀, τ₀, υ₀, φ₀, e, hp, hq, hu, hv, he,
    hσinj, hτinj, hυinj, hφinj, hσ, hτ, hυ, hφ⟩
  exact (crossingProductCell_doublePointSet_resolved hr hr1 C).trans hd.symm

end DifferentialGeometry.Topology.PiecewiseLinear
