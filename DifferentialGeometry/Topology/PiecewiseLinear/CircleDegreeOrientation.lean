/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusOrientation
import DifferentialGeometry.Topology.LocalDegree.OrthogonalDegree
import Mathlib.Analysis.Complex.OperatorNorm

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.LocalDegree

local notation "S1" => sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

theorem euclideanSphereDegree_sphereReflection :
    euclideanSphereDegree sphereReflection.toHomotopyEquiv.toFun = -1 := by
  have heq : sphereReflection.toHomotopyEquiv.toFun =
      linearSphereMap planarReflection.toContinuousLinearEquiv := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    rw [linearSphereMap_apply]
    change planarReflection z = ‖planarReflection z‖⁻¹ • planarReflection z
    rw [planarReflection.norm_map, norm_eq_of_mem_sphere z, inv_one, one_smul]
  have hdet : LinearMap.det planarReflection.toLinearMap = -1 := by
    have he := LinearMap.det_conj Complex.conjLIE.toLinearMap
      Complex.orthonormalBasisOneI.repr.toLinearEquiv
    exact he.trans Complex.det_conjLIE
  rw [heq, euclideanSphereDegree_linearIsometryEquiv, hdet]
  norm_num

theorem euclideanSphereDegree_eq_one_of_hasIncreasingCircleLift
    (τ : S1 ≃ₜ S1)
    (hτ : HasIncreasingCircleLift
      (fun θ => planarCircleParam.symm (τ (planarCircleParam θ)))) :
    euclideanSphereDegree τ.toHomotopyEquiv.toFun = 1 := by
  let ψ : loopCircle ≃ₜ loopCircle :=
    (planarCircleParam.trans τ).trans planarCircleParam.symm
  obtain ⟨H, hH, -, hH0, hH1⟩ := exists_isotopy_circle_of_hasIncreasingCircleLift ψ hτ
  let K : (ContinuousMap.id S1).Homotopy τ.toHomotopyEquiv.toFun := {
    toFun := fun p => planarCircleParam (H p.1 (planarCircleParam.symm p.2))
    continuous_toFun := planarCircleParam.continuous.comp
      (hH.comp (continuous_fst.prodMk (planarCircleParam.symm.continuous.comp continuous_snd)))
    map_zero_left := fun z => by
      rw [hH0]
      exact planarCircleParam.apply_symm_apply z
    map_one_left := fun z => by
      rw [hH1]
      change planarCircleParam (planarCircleParam.symm
        (τ (planarCircleParam (planarCircleParam.symm z)))) = τ z
      rw [planarCircleParam.apply_symm_apply, planarCircleParam.apply_symm_apply] }
  exact (euclideanSphereDegree_eq_of_homotopy K).symm.trans euclideanSphereDegree_id

theorem euclideanSphereDegree_eq_one_iff_hasIncreasingCircleLift
    (τ : S1 ≃ₜ S1) :
    euclideanSphereDegree τ.toHomotopyEquiv.toFun = 1 ↔
      HasIncreasingCircleLift
        (fun θ => planarCircleParam.symm (τ (planarCircleParam θ))) := by
  constructor
  · intro hdeg
    by_contra hneg
    have hp := (hasIncreasingCircleLift_reflect_iff τ).mpr hneg
    have h := euclideanSphereDegree_eq_one_of_hasIncreasingCircleLift
      (τ.trans sphereReflection) hp
    have heq : (τ.trans sphereReflection).toHomotopyEquiv.toFun =
        sphereReflection.toHomotopyEquiv.toFun.comp τ.toHomotopyEquiv.toFun := rfl
    rw [heq, euclideanSphereDegree_comp, euclideanSphereDegree_sphereReflection, hdeg] at h
    norm_num at h
  · exact euclideanSphereDegree_eq_one_of_hasIncreasingCircleLift τ

noncomputable def circleSphereHomeomorph {F : Type*} [NormedAddCommGroup F]
    {S : Set F} {g : loopCircle → F} (hgc : Continuous g) (hgb : BijOn g univ S)
    {u : F → F} (hcu : ContinuousOn u S) (hbu : BijOn u S S) : S1 ≃ₜ S1 :=
  (planarCircleParam.symm.trans (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (circleConj g u) (bijective_circleConj hgb hbu))
    (continuous_circleConj hgc hgb hcu hbu.mapsTo))).trans planarCircleParam

theorem isPLCirclePositive_iff_euclideanSphereDegree_eq_one
    {F : Type*} [NormedAddCommGroup F]
    {S : Set F} {g : loopCircle → F} (hgc : Continuous g) (hgb : BijOn g univ S)
    {u : F → F} (hcu : ContinuousOn u S) (hbu : BijOn u S S) :
    IsPLCirclePositive S u ↔
      euclideanSphereDegree (circleSphereHomeomorph hgc hgb hcu hbu).toHomotopyEquiv.toFun = 1 := by
  have heq : (fun θ => planarCircleParam.symm
      (circleSphereHomeomorph hgc hgb hcu hbu (planarCircleParam θ))) = circleConj g u := by
    funext θ
    change planarCircleParam.symm (planarCircleParam
      (circleConj g u (planarCircleParam.symm (planarCircleParam θ)))) = circleConj g u θ
    rw [planarCircleParam.symm_apply_apply, planarCircleParam.symm_apply_apply]
  rw [euclideanSphereDegree_eq_one_iff_hasIncreasingCircleLift, heq]
  exact ⟨fun hpos => hpos.forall_param hbu.mapsTo hgc hgb, fun hpos => ⟨g, hgc, hgb, hpos⟩⟩
end DifferentialGeometry.Topology.PiecewiseLinear
