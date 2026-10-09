/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleDegreeOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePositiveConjugation
import Mathlib.Data.ZMod.Basic

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def circleOrientationParity (S : Set E) (u : E → E) : ZMod 2 := by
  classical
  exact if IsPLCirclePositive S u then 0 else 1

theorem circleOrientationParity_eq_zero_iff {S : Set E} {u : E → E} :
    circleOrientationParity S u = 0 ↔ IsPLCirclePositive S u := by
  classical
  simp [circleOrientationParity]

theorem circleOrientationParity_eq_of_positive_iff {S : Set E} {u : E → E} {a : ZMod 2}
    (h : IsPLCirclePositive S u ↔ a = 0) : circleOrientationParity S u = a := by
  classical
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) a with ha | ha
  · simp [circleOrientationParity, h, ha]
  · simp [circleOrientationParity, h, ha]

theorem circleOrientationParity_congr {S : Set E} {u v : E → E} (h : EqOn u v S) :
    circleOrientationParity S u = circleOrientationParity S v := by
  classical
  have he : IsPLCirclePositive S u ↔ IsPLCirclePositive S v :=
    ⟨fun hu => hu.of_eqOn h.symm, fun hv => hv.of_eqOn h⟩
  simp only [circleOrientationParity, he]

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem circleOrientationParity_id {S : Set E} (hS : IsPLSphere 1 S) :
    circleOrientationParity S id = 0 := circleOrientationParity_eq_zero_iff.mpr
      (isPLCirclePositive_id hS)

theorem circleOrientationParity_comp {S : Set E} (hS : IsPLSphere 1 S)
    {u v : E → E} (hu : IsPLHomeomorphOn u S S) (hv : IsPLHomeomorphOn v S S) :
    circleOrientationParity S (u ∘ v) =
      circleOrientationParity S u + circleOrientationParity S v := by
  classical
  obtain ⟨g, hgc, hgb⟩ := exists_loopCircle_param_of_isPLSphere_one hS
  let τu := circleSphereHomeomorph hgc hgb hu.isPiecewiseAffineOn.continuousOn hu.bijOn
  let τv := circleSphereHomeomorph hgc hgb hv.isPiecewiseAffineOn.continuousOn hv.bijOn
  have huv := hv.trans hu
  let τuv := circleSphereHomeomorph hgc hgb huv.isPiecewiseAffineOn.continuousOn huv.bijOn
  have heq : τuv.toHomotopyEquiv.toFun =
      τu.toHomotopyEquiv.toFun.comp τv.toHomotopyEquiv.toFun := by
    apply ContinuousMap.ext
    intro θ
    change planarCircleParam (circleConj g (u ∘ v) (planarCircleParam.symm θ)) =
      planarCircleParam (circleConj g u (planarCircleParam.symm
        (planarCircleParam (circleConj g v (planarCircleParam.symm θ)))))
    rw [planarCircleParam.symm_apply_apply, circleConj_comp hgb hv.bijOn.mapsTo]
  have hdeg := congrArg DifferentialGeometry.LocalDegree.euclideanSphereDegree heq
  rw [DifferentialGeometry.LocalDegree.euclideanSphereDegree_comp] at hdeg
  have hpu := isPLCirclePositive_iff_euclideanSphereDegree_eq_one hgc hgb
    hu.isPiecewiseAffineOn.continuousOn hu.bijOn
  have hpv := isPLCirclePositive_iff_euclideanSphereDegree_eq_one hgc hgb
    hv.isPiecewiseAffineOn.continuousOn hv.bijOn
  have hpuv := isPLCirclePositive_iff_euclideanSphereDegree_eq_one hgc hgb
    huv.isPiecewiseAffineOn.continuousOn huv.bijOn
  have huu := Int.isUnit_iff.mp
    (DifferentialGeometry.LocalDegree.euclideanSphereDegree_isUnit τu.toHomotopyEquiv)
  have hvv := Int.isUnit_iff.mp
    (DifferentialGeometry.LocalDegree.euclideanSphereDegree_isUnit τv.toHomotopyEquiv)
  dsimp only [τu] at huu
  dsimp only [τv] at hvv
  unfold circleOrientationParity
  rw [hpu, hpv, hpuv, hdeg]
  dsimp only [τu, τv]
  rcases huu with hu | hu
  · rcases hvv with hv | hv
    · simp [hu, hv]
    · simp [hu, hv]
  · rcases hvv with hv | hv
    · simp [hu, hv]
    · simp [hu, hv, show (1 : ZMod 2) + 1 = 0 from by decide]

theorem circleOrientationParity_invFunOn {S : Set E} (hS : IsPLSphere 1 S)
    {u : E → E} (hu : IsPLHomeomorphOn u S S) :
    circleOrientationParity S (Function.invFunOn u S) = circleOrientationParity S u := by
  have heq : EqOn (u ∘ Function.invFunOn u S) id S := hu.bijOn.invOn_invFunOn.2
  have hc := circleOrientationParity_comp hS hu hu.symm
  rw [circleOrientationParity_congr heq, circleOrientationParity_id hS] at hc
  have hz : ∀ a : ZMod 2, a + a = 0 := by decide
  exact add_left_cancel (hc.symm.trans (hz (circleOrientationParity S u)).symm)

end DifferentialGeometry.Topology.PiecewiseLinear
