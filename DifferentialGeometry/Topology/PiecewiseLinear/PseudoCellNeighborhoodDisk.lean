/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralDiskRecognition
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_neighborhood_subdisk {Ec Eint Ebd : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Dc Dcint : Set E3, IsTopologicalCellWithInterior 2 Dc Dcint ∧ Dc ⊆ Eint ∧
      Dc ⊆ ball P δ ∧ P ∈ Dcint ∧ ∃ ε > 0, ball P ε ∩ Ec ⊆ Dc := by
  obtain ⟨ψ⟩ := hE.isOpenCell
  let e : E2 ≃ₜ Eint := Homeomorph.unitBall.trans ψ.symm
  let c : E2 := e.symm ⟨P, hE.centerMem⟩
  have hec : (e c : E3) = P := congrArg Subtype.val (e.apply_symm_apply _)
  have hopen : IsOpen ((fun x : E2 => (e x : E3)) ⁻¹' ball P δ) :=
    isOpen_ball.preimage (continuous_subtype_val.comp e.continuous)
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hopen c (by
    change (e c : E3) ∈ ball P δ
    rw [hec]
    exact mem_ball_self hδ)
  let a : E2 ≃ₜ E2 :=
    (Homeomorph.smulOfNeZero (r / 2) (by positivity)).trans (Homeomorph.addRight c)
  let g : E2 ≃ₜ Eint := a.trans e
  let F : E2 → E3 := fun x => g x
  have hF : Continuous F := continuous_subtype_val.comp g.continuous
  have hFi : Function.Injective F := fun x y hxy => g.injective (Subtype.ext hxy)
  have hFzero : F 0 = P := by
    change (e ((r / 2) • (0 : E2) + c) : E3) = P
    simpa only [smul_zero, zero_add] using hec
  have hunit : IsTopologicalCellWithInterior 2 (closedBall (0 : E2) 1) (ball 0 1) := by
    refine ⟨Homeomorph.refl _, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, ball_subset_closedBall hx⟩,
        ⟨⟨x, ball_subset_closedBall hx⟩, mem_ball_zero_iff.mp hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact mem_ball_zero_iff.mpr hq
  have hcell := hunit.image_of_injOn hF.continuousOn hFi.injOn
  have hPD : P ∈ F '' ball (0 : E2) 1 :=
    ⟨0, mem_ball_self one_pos, hFzero⟩
  have hDE : F '' closedBall (0 : E2) 1 ⊆ Eint := by
    rintro _ ⟨x, -, rfl⟩
    exact (g x).2
  have hDδ : F '' closedBall (0 : E2) 1 ⊆ ball P δ := by
    rintro _ ⟨x, hx, rfl⟩
    apply hrs
    change dist ((r / 2) • x + c) c < r
    rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg (by positivity)]
    have hx' := mem_closedBall_zero_iff.mp hx
    nlinarith [norm_nonneg x]
  have hrel : IsOpen ((Subtype.val : Eint → E3) ⁻¹' (F '' ball (0 : E2) 1)) := by
    have heq : (Subtype.val : Eint → E3) ⁻¹' (F '' ball (0 : E2) 1) =
        g '' ball (0 : E2) 1 := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [heq]
    exact g.isOpenMap _ isOpen_ball
  obtain ⟨V, hV, hVI⟩ := isOpen_induced_iff.mp hrel
  have hPV : P ∈ V := by
    have hp : (⟨P, hE.centerMem⟩ : Eint) ∈
        (Subtype.val : Eint → E3) ⁻¹' (F '' ball (0 : E2) 1) := hPD
    rwa [← hVI] at hp
  have hbd : IsClosed Ebd := by
    obtain ⟨b⟩ := hE.isSphere
    exact (isCompact_iff_compactSpace.mpr b.symm.compactSpace).isClosed
  have hPbd : P ∉ Ebd := fun hp => disjoint_left.mp hE.disjointRim hE.centerMem hp
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp (hV.inter hbd.isOpen_compl) P ⟨hPV, hPbd⟩
  refine ⟨F '' closedBall (0 : E2) 1, F '' ball (0 : E2) 1,
    hcell, hDE, hDδ, hPD, ε, hε, ?_⟩
  rintro x ⟨hxε, hxEc⟩
  have hxV := hεV hxε
  have hxE : x ∈ Eint := by
    rw [hE.carrierEq] at hxEc
    exact hxEc.resolve_right hxV.2
  have hxI : (⟨x, hxE⟩ : Eint) ∈ (Subtype.val : Eint → E3) ⁻¹' V := hxV.1
  rw [hVI] at hxI
  exact image_mono ball_subset_closedBall hxI

end DifferentialGeometry.Topology.PiecewiseLinear
