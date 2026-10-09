/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonDrag
import Mathlib.Data.Set.Card

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem bigonDrag_crossing_points_ne {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsupp : slideSupport ⊆ e.target) :
    e.symm (0, -1 / 2, 0) ≠ e.symm (0, 1 / 2, 0) := by
  have hneg : (0, -1 / 2, 0) ∈ e.target := hsupp (by norm_num [slideSupport])
  have hpos : (0, 1 / 2, 0) ∈ e.target := hsupp (by norm_num [slideSupport])
  intro h
  have he := congrArg e h
  rw [e.right_inv hneg, e.right_inv hpos] at he
  have hu := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) he
  norm_num at hu

theorem bigonDrag_crossings_in_source {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsupp : slideSupport ⊆ e.target)
    {C Tr : Set X} (hC : ∀ x ∈ e.source, x ∈ C ↔ (e x).1 = 0 ∧ (e x).2.2 = 0)
    (hTr : ∀ x ∈ e.source,
      x ∈ Tr ↔ (e x).2.2 = 0 ∧ (e x).1 = (1 / 2 - |(e x).2.1|) / 2) :
    (Tr ∩ C) ∩ e.source = {e.symm (0, -1 / 2, 0), e.symm (0, 1 / 2, 0)} := by
  have hneg : (0, -1 / 2, 0) ∈ e.target := hsupp (by norm_num [slideSupport])
  have hpos : (0, 1 / 2, 0) ∈ e.target := hsupp (by norm_num [slideSupport])
  ext x
  constructor
  · rintro ⟨⟨hxTr, hxC⟩, hxs⟩
    obtain ⟨hz, hv⟩ := (hTr x hxs).mp hxTr
    have hzero := ((hC x hxs).mp hxC).1
    have hu : |(e x).2.1| = 1 / 2 := by linarith
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hu with hu | hu
    · have he : e x = (0, 1 / 2, 0) := Prod.ext hzero (Prod.ext hu hz)
      apply mem_insert_of_mem
      rw [mem_singleton_iff, ← he, e.left_inv hxs]
    · have he : e x = (0, -1 / 2, 0) := by
        apply Prod.ext hzero
        apply Prod.ext _ hz
        linarith
      apply mem_insert_iff.mpr
      left
      rw [← he, e.left_inv hxs]
  · intro hx
    rcases mem_insert_iff.mp hx with hx | hx
    · subst x
      have hxs := e.map_target hneg
      refine ⟨⟨(hTr _ hxs).mpr ?_, (hC _ hxs).mpr ?_⟩, hxs⟩ <;>
        rw [e.right_inv hneg] <;> norm_num
    · rw [mem_singleton_iff] at hx
      subst x
      have hxs := e.map_target hpos
      refine ⟨⟨(hTr _ hxs).mpr ?_, (hC _ hxs).mpr ?_⟩, hxs⟩ <;>
        rw [e.right_inv hpos] <;> norm_num

theorem bigonDrag_ncard_crossings_add_two {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsupp : slideSupport ⊆ e.target)
    {C Tr : Set X} (hC : ∀ x ∈ e.source, x ∈ C ↔ (e x).1 = 0 ∧ (e x).2.2 = 0)
    (hTr : ∀ x ∈ e.source,
      x ∈ Tr ↔ (e x).2.2 = 0 ∧ (e x).1 = (1 / 2 - |(e x).2.1|) / 2)
    (hfin : (Tr ∩ C).Finite) :
    (e.conjugateMap slideMap '' Tr ∩ C).ncard + 2 = (Tr ∩ C).ncard := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross⟩ := exists_bigonDrag e hsupp
    (Sf := {x | (e x).2.2 = 0}) (Y := {x | 0 ≤ (e x).2.2})
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) hC hTr
  have hcard := ncard_inter_add_ncard_sdiff_eq_ncard (Tr ∩ C) e.source hfin
  rw [bigonDrag_crossings_in_source e hsupp hC hTr,
    ncard_pair (bigonDrag_crossing_points_ne e hsupp)] at hcard
  rw [hcross]
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
