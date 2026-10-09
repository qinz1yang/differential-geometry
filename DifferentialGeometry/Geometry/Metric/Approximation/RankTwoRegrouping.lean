import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual coordinate regrouping of a rank-two L2 splitting

Each coordinate is made the first real coordinate by an isometry, with the
other real coordinate retained in the residual factor. Supplied anchors are unchanged.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry

private def rankTwoPair (j : Fin 2) :
    EuclideanSpace ℝ (Fin 2) ≃ᵢ WithLp 2 (ℝ × ℝ) where
  toFun x := WithLp.toLp 2 (x j, x j.rev)
  invFun x := WithLp.toLp 2 (fun i => if i = j then x.fst else x.snd)
  left_inv x := by
    ext i
    fin_cases j <;> fin_cases i <;> simp
  right_inv x := by
    apply (WithLp.equiv 2 _).injective
    fin_cases j <;> simp <;> rfl
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro x y
    have hp := WithLp.prod_dist_sq_eq_add_sq
      (WithLp.toLp 2 (x j, x j.rev)) (WithLp.toLp 2 (y j, y j.rev))
    have he : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
      rw [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sq_abs] at hp
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    fin_cases j
    · change dist (WithLp.toLp 2 (x 0, x 1)) (WithLp.toLp 2 (y 0, y 1)) ^ 2 = _
      exact hp.trans he.symm
    · change dist (WithLp.toLp 2 (x 1, x 0)) (WithLp.toLp 2 (y 1, y 0)) ^ 2 = _
      exact hp.trans ((add_comm _ _).trans he.symm)

def rankTwoAxisPoint {Y : Type*} (j : Fin 2) (t : ℝ) (y : Y) :
    WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y) :=
  WithLp.toLp 2 (WithLp.toLp 2 (Pi.single j t), y)

def rankTwoRegroup (Y : Type*) [MetricSpace Y] (j : Fin 2) :
    WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y) ≃ᵢ WithLp 2 (ℝ × WithLp 2 (ℝ × Y)) :=
  ((rankTwoPair j).withLpProdCongr 2 (IsometryEquiv.refl Y)).trans
    (IsometryEquiv.withLpProdAssoc 2 ℝ ℝ Y)

theorem rankTwoRegroup_fst {Y : Type*} [MetricSpace Y] (j : Fin 2)
    (x : WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y)) :
    (rankTwoRegroup Y j x).fst = x.fst j := rfl

theorem rankTwoRegroup_residual {Y : Type*} [MetricSpace Y] (j : Fin 2)
    (x : WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y)) :
    (rankTwoRegroup Y j x).snd.snd = x.snd := rfl

theorem rankTwoRegroup_axisPoint {Y : Type*} [MetricSpace Y] (j : Fin 2)
    (t : ℝ) (y : Y) :
    rankTwoRegroup Y j (rankTwoAxisPoint j t y) =
      WithLp.toLp 2 (t, WithLp.toLp 2 ((0 : ℝ), y)) := by
  apply (WithLp.equiv 2 _).injective
  fin_cases j <;> simp [rankTwoRegroup, rankTwoAxisPoint, rankTwoPair,
    IsometryEquiv.withLpProdCongr, IsometryEquiv.withLpProdAssoc] <;> rfl

theorem rankTwoRegroup_zero {Y : Type*} [MetricSpace Y] (j : Fin 2) (y : Y) :
    rankTwoRegroup Y j (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y)) =
      WithLp.toLp 2 ((0 : ℝ), WithLp.toLp 2 ((0 : ℝ), y)) := by
  have h := rankTwoRegroup_axisPoint j 0 y
  simpa only [rankTwoAxisPoint, Pi.single_zero, WithLp.toLp_zero] using h

namespace KleinerLottApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {q : X} {y : Y} {ν : ℝ}

def coordinateSplitting
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y)) ν)
    (j : Fin 2) :
    KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), WithLp.toLp 2 ((0 : ℝ), y))) ν :=
  F.mapTargetIsometryAt (rankTwoRegroup Y j) _ (rankTwoRegroup_zero j y)

theorem coordinateSplitting_fst
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y)) ν)
    (j : Fin 2) (x : X) : ((F.coordinateSplitting j).toFun x).fst = (F.toFun x).fst j := rfl

theorem coordinateSplitting_anchor_dist
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y)) ν)
    (j : Fin 2) (a : X) (t : ℝ) :
    dist ((F.coordinateSplitting j).toFun a)
      (WithLp.toLp 2 (t, WithLp.toLp 2 ((0 : ℝ), y))) =
        dist (F.toFun a) (rankTwoAxisPoint j t y) := by
  rw [coordinateSplitting, mapTargetIsometryAt_apply, ← rankTwoRegroup_axisPoint j t y,
    (rankTwoRegroup Y j).dist_eq]

end KleinerLottApprox

end GC.MetricGeometry
