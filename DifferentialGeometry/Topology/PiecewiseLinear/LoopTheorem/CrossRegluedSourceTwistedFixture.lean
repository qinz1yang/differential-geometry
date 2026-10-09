/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedWords

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem twistedStripCell_exists_reversing_boundaryWordData {B : Set halfTurnQuotient}
    (hB : Set.range twistedStripCell.boundary ⊆ B) :
    ∃ (hD : NormalSingularCellData twistedStripCell (frontier twistedStripSide) B)
      (c : hD.singularSet.Branch)
      (T : CrossSeamTubeData hD c (halfTurnSlabChart 0).source)
      (R : PLCrossSeamReading T.chart crossRegluedTwistedCell)
      (C : PLSeamTubeChart halfTurnQuotient T.chart)
      (f : frontier twistedStripCell.domain → B)
      (a b : B) (σ υ : Path a b) (τ φ : Path b a)
      (Gd : SingularTwoCell halfTurnQuotient),
      hD.singularSet.complexity = 1 ∧ hD.singularSet.IsBoundaryBranch c ∧
      T.chart = twistedTubeChart ∧ R.tubeSource ⊂ crossRegluedTwistedCell.domain ∧
      IsPLBoundarySide twistedStripCell twistedStripSide (frontier twistedStripSide) ∧
      T.chart '' spliceCylinder ⊆ twistedStripSide ∧
      T.chart '' spliceCylinder ∩ frontier twistedStripSide = T.chart '' spliceEndDisks ∧
      Continuous f ∧ (∀ z, (f z : halfTurnQuotient) = twistedStripCell z) ∧
      hD.IsBoundarySurgeryCell c Gd ∧ hD.IsCrossRegluedCell c crossRegluedTwistedCell ∧
      doublePointSet (R.resolvedCell C) (R.resolvedCell C).domain = ∅ ∧
      Nonempty (BoundaryWordWitness Gd (Subtype.val : B → halfTurnQuotient)
        (pathToCircle (σ.trans υ.symm))) ∧
      ∃ (p q u v : frontier twistedStripCell.domain)
        (σ₀ : Path p q) (τ₀ : Path q u) (υ₀ : Path u v) (φ₀ : Path v p)
        (e : loopCircle ≃ₜ frontier twistedStripCell.domain)
        (W : BoundaryWordWitness crossRegluedTwistedCell (Subtype.val : B → halfTurnQuotient)
          (pathToCircle (σ.trans (φ.trans (υ.trans τ))))),
        W.param = e ∧
        (p : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (0, 0) ∧
        (q : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (0, 1) ∧
        (u : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (1, 1) ∧
        (v : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (1, 0) ∧
        (∀ θ, e θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ) ∧
        Function.Injective σ₀ ∧ Function.Injective τ₀ ∧
        Function.Injective υ₀ ∧ Function.Injective φ₀ ∧
        (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧
        (∀ t, υ t = f (υ₀ t)) ∧ (∀ t, φ t = f (φ₀ t)) := by
  obtain ⟨hD⟩ := twistedStripCell_nonempty_normalSingularCellData hB
  obtain ⟨c, T, hn, hb, hc, hT, ⟨C⟩, hside, hbd, -⟩ := twistedStripCell_exists_branchTube hD
  have hR : Nonempty (PLCrossSeamReading T.chart crossRegluedTwistedCell) := by
    rw [hT]
    exact ⟨crossRegluedTwistedReading⟩
  obtain ⟨R⟩ := hR
  have hG := crossRegluedTwistedCell_isCrossRegluedCell hD hc
  let f : frontier twistedStripCell.domain → B :=
    fun z => ⟨twistedStripCell z, hB ⟨z, rfl⟩⟩
  have hf : Continuous f := twistedStripCell.boundary.continuous.subtype_mk _
  have hfρ : ∀ z, (f z : halfTurnQuotient) = twistedStripCell z := fun _ => rfl
  obtain ⟨p, q, u, v, σ₀, τ₀, υ₀, φ₀, e, a, b, σ, υ, τ, φ, Gd,
    hp, hq, hu, hv, he, hσinj, hτinj, hυinj, hφinj, hσ, hτ, hυ, hφ, hGd, Wd, W, hWe⟩ :=
    twistedStripCell_exists_reversing_boundaryWordWitnesses hD hc
      IsEmbedding.subtypeVal f hf hfρ
  have hGD := hD.doublePointSet_eq_of_isCrossRegluedCell hG
  have hres := CrossSeamRegluedData.doublePointSet_cell_eq (R.toCrossSeamRegluedData T C)
    (congrArg (fun S => S \ T.chart '' spliceCylinder) hGD)
  have hempty : doublePointSet (R.resolvedCell C) (R.resolvedCell C).domain = ∅ := by
    change doublePointSet (R.resolvedCell C) (R.resolvedCell C).domain = _ at hres
    rw [hres, hc, sdiff_self]
  exact ⟨hD, c, T, R, C, f, a, b, σ, υ, τ, φ, Gd, hn, hb, hT, R.source_ssubset_domain,
    isPLBoundarySide_twistedStripCell, hside, hbd, hf, hfρ, hGd, hG, hempty, Wd,
    p, q, u, v, σ₀, τ₀, υ₀, φ₀, e, W, hWe, hp, hq, hu, hv, he,
    hσinj, hτinj, hυinj, hφinj, hσ, hτ, hυ, hφ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
