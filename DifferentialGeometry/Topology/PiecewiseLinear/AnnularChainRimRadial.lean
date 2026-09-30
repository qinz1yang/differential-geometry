/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import DifferentialGeometry.Topology.Simplex.Coordinates
import Mathlib.Tactic

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Simplex

private noncomputable def rimRadialMidpoint (b : boundary (Fin 3)) : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
  ⟨fun i => (b.val.val i + (3 : ℝ)⁻¹) / 2, by
    constructor
    · intro i
      have hi := b.val.property.1 i
      positivity
    · rw [← Finset.sum_div, Finset.sum_add_distrib, b.val.property.2]
      norm_num⟩

private theorem rimRadialMidpoint_pos (b : boundary (Fin 3)) (i : Fin 3) :
    0 < (rimRadialMidpoint b).val i := by
  dsimp [rimRadialMidpoint]
  have hi := b.val.property.1 i
  positivity

private theorem rimRadialMidpoint_ne (b : boundary (Fin 3)) :
    rimRadialMidpoint b ≠ Convexity.StdSimplex.coordinateBarycenter := by
  obtain ⟨i, hi⟩ := b.property
  intro he
  have hei := congrArg (fun x : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) => x.val i) he
  simp only [rimRadialMidpoint, Convexity.StdSimplex.coordinateBarycenter_apply, Fintype.card_fin] at hei
  rw [hi] at hei
  norm_num at hei

private theorem rimRadialMidpoint_minimum (b : boundary (Fin 3)) :
    minimumCoordinate (rimRadialMidpoint b) = (6 : ℝ)⁻¹ := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := b.property
    have h := minimumCoordinate_le (rimRadialMidpoint b) i
    change minimumCoordinate (rimRadialMidpoint b) ≤ (b.val.val i + (3 : ℝ)⁻¹) / 2 at h
    norm_num [hi] at h
    simpa only [one_div] using h
  · obtain ⟨i, hi⟩ := exists_minimumCoordinate (rimRadialMidpoint b)
    rw [hi]
    change (6 : ℝ)⁻¹ ≤ (b.val.val i + (3 : ℝ)⁻¹) / 2
    linarith [b.val.property.1 i]

theorem exists_open_simplex_radial_section :
    ∃ s : C(boundary (Fin 3), {x : punctured (Fin 3) | ∀ i, 0 < x.val.val i}),
      ∀ b, radialRetraction (s b).val = b := by
  let s : C(boundary (Fin 3), {x : punctured (Fin 3) | ∀ i, 0 < x.val.val i}) :=
    ⟨fun b => ⟨⟨rimRadialMidpoint b, rimRadialMidpoint_ne b⟩,
      rimRadialMidpoint_pos b⟩, by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      exact (((continuous_apply i).comp
        (continuous_subtype_val.comp continuous_subtype_val)).add continuous_const).div_const 2⟩
  refine ⟨s, fun b => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change ((rimRadialMidpoint b).val i - minimumCoordinate (rimRadialMidpoint b)) /
    (1 - (Fintype.card (Fin 3) : ℝ) * minimumCoordinate (rimRadialMidpoint b)) = b.val.val i
  rw [rimRadialMidpoint_minimum]
  simp only [rimRadialMidpoint, Fintype.card_fin]
  ring

end DifferentialGeometry.Topology.PiecewiseLinear
