/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set Metric Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isPLPath_of_isOpen {S : Set E} (hS : IsOpen S)
    (hconn : IsPreconnected S) (x y : S) : ∃ γ : Path x y, IsPLPath γ := by
  let R : Set S := {z | ∃ γ : Path x z, IsPLPath γ}
  have hRopen : IsOpen R := by
    apply Metric.isOpen_iff.mpr
    rintro z ⟨γ, hγ⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hS z z.property
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have hseg : segment ℝ (z : E) (w : E) ⊆ S :=
      ((convex_ball (z : E) δ).segment_subset (mem_ball_self hδ) hw).trans hball
    exact ⟨γ.trans (segmentPath z w hseg), hγ.trans (isPLPath_segmentPath z w hseg)⟩
  have hRcompl : IsOpen Rᶜ := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hS z z.property
    refine ⟨δ, hδ, fun w hw => ?_⟩
    rintro ⟨γ, hγ⟩
    have hseg : segment ℝ (w : E) (z : E) ⊆ S :=
      ((convex_ball (z : E) δ).segment_subset hw (mem_ball_self hδ)).trans hball
    exact hz ⟨γ.trans (segmentPath w z hseg), hγ.trans (isPLPath_segmentPath w z hseg)⟩
  have hx : x ∈ R := by
    refine ⟨Path.refl x, isPLPath_of_forall_eq _ (z := (x : E)) ?_⟩
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl
  let _ : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn
  have heq : R = univ := (show IsClopen R from ⟨isOpen_compl_iff.mp hRcompl, hRopen⟩).eq_univ ⟨x,
      hx⟩
  exact (heq.symm ▸ mem_univ y : y ∈ R)

theorem exists_piecewiseAffine_path_of_isOpen {S : Set E} (hS : IsOpen S)
    (hconn : IsPreconnected S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ f : ℝ → E, IsPiecewiseAffineOn f (Icc 0 1) ∧ f 0 = x ∧ f 1 = y ∧
      MapsTo f (Icc 0 1) S := by
  obtain ⟨γ, hγ⟩ := exists_isPLPath_of_isOpen hS hconn (⟨x, hx⟩ : S) ⟨y, hy⟩
  exact ⟨fun t => (γ.extend t : E), hγ, by simp, by simp, fun t _ => (γ.extend t).property⟩

end DifferentialGeometry.Topology.PiecewiseLinear
