/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RadialSolidTorusShell
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientPointMove
import Mathlib.Topology.MetricSpace.Thickening

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Disk" => Metric.closedBall (0 : Plane) 1
local notation "Circle" => Metric.sphere (0 : Plane) 1

theorem IsSpine.exists_centered_parametrisation {Y J : Set E3} (hJ : IsSpine Y J) :
    ∃ φ : (Disk × Circle) ≃ₜ Y,
      J = Subtype.val '' (φ '' {z | (z.1 : Plane) = 0}) := by
  obtain ⟨φ, p, hp, hJ⟩ := hJ
  have hp' : p ∈ Metric.ball (0 : Plane) 1 := by
    simpa only [interior_closedBall _ one_ne_zero] using hp
  obtain ⟨e, -, hfix, he0⟩ := exists_isPLHomeomorphOn_map_point_eqOn_compl Metric.isOpen_ball
    (convex_ball (0 : Plane) 1).isPreconnected (Metric.mem_ball_self zero_lt_one) hp'
  have heB : e '' Metric.ball (0 : Plane) 1 = Metric.ball (0 : Plane) 1 := by
    have ht := e.image_compl (Metric.ball (0 : Plane) 1)ᶜ
    rw [compl_compl, hfix.image_eq, image_id, compl_compl] at ht
    exact ht
  have hclosed : e '' Disk = Disk := by
    rw [← closure_ball (0 : Plane) one_ne_zero, e.image_closure, heB]
  let d : Disk ≃ₜ Disk := (e.image Disk).trans (Homeomorph.setCongr hclosed)
  have hd0 (z : Disk) : (d z : Plane) = p ↔ (z : Plane) = 0 := by
    change e z = p ↔ (z : Plane) = 0
    rw [← he0, e.injective.eq_iff]
  let φ₀ := (d.prodCongr (Homeomorph.refl Circle)).trans φ
  refine ⟨φ₀, ?_⟩
  rw [hJ, image_image, image_image]
  apply Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    let w : Disk × Circle := (d.symm z.1, z.2)
    have hw : (w.1 : Plane) = 0 := by
      apply (hd0 (d.symm z.1)).mp
      rw [d.apply_symm_apply]
      exact hz
    refine ⟨w, hw, ?_⟩
    change (φ (d (d.symm z.1), z.2) : E3) = φ z
    rw [d.apply_symm_apply, Prod.mk.eta]
  · rintro x ⟨z, hz, rfl⟩
    exact ⟨(d z.1, z.2), (hd0 z.1).mpr hz, rfl⟩

theorem IsSpine.exists_inner_torus_of_isOpen {Y J O : Set E3}
    (hJ : IsSpine Y J) (hO : IsOpen O) (hJO : J ⊆ O) :
    ∃ S₁ : Set E3, IsTopologicalSolidTorus S₁ ∧ S₁ ⊆ O ∧ S₁ ⊆ interior Y ∧
      IsToroidalShell (closure (Y \ S₁)) (frontier S₁) (frontier Y) ∧ IsSpine S₁ J := by
  obtain ⟨φ, hJφ⟩ := hJ.exists_centered_parametrisation
  let Ψ : Disk × Circle → E3 := fun z => φ z
  have hΨ : Continuous Ψ := continuous_subtype_val.comp φ.continuous
  let A : Set (Disk × Circle) := {z | (z.1 : Plane) = 0}
  have hA : IsCompact A :=
    (isClosed_eq (continuous_subtype_val.comp continuous_fst) continuous_const).isCompact
  have hAO : A ⊆ Ψ ⁻¹' O := by
    intro z hz
    apply hJO
    rw [hJφ]
    exact ⟨φ z, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨ε, hε, hsmall⟩ := hA.exists_thickening_subset_open (hO.preimage hΨ) hAO
  let r := min ε 1 / 2
  have hr0 : 0 < r := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hr1 : r < 1 := by
    have ht := min_le_right ε (1 : ℝ)
    dsimp [r]
    linarith
  have hrε : r < ε := by
    have ht := min_le_left ε (1 : ℝ)
    dsimp [r]
    linarith
  obtain ⟨S₁, hS₁, hS₁Y, hshell, hradial, hspine⟩ :=
    exists_radial_inner_torus_with_spine φ.symm hr0 hr1
  have hS₁O : S₁ ⊆ O := by
    intro x hx
    obtain ⟨z, hz⟩ := φ.surjective ⟨x, interior_subset (hS₁Y hx)⟩
    have hzx : (φ z : E3) = x := congrArg Subtype.val hz
    have hnorm : ‖(z.1 : Plane)‖ ≤ r := (hradial z).mp (hzx.symm ▸ hx)
    let z₀ : Disk × Circle := (⟨0, by simp⟩, z.2)
    have hdist : dist z z₀ < ε := by
      change max (dist (z.1 : Plane) 0) (dist z.2 z.2) < ε
      simpa only [dist_zero_right, dist_self, max_eq_left (norm_nonneg _)] using hnorm.trans_lt hrε
    have ht := hsmall (Metric.mem_thickening_iff.mpr ⟨z₀, rfl, hdist⟩)
    change (φ z : E3) ∈ O at ht
    exact hzx ▸ ht
  refine ⟨S₁, hS₁, hS₁O, hS₁Y, hshell, ?_⟩
  rw [hJφ]
  exact hspine

end DifferentialGeometry.Topology.PiecewiseLinear
