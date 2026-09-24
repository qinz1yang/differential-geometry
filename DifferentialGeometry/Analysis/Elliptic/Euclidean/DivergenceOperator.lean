import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Minimum
import DifferentialGeometry.Analysis.Parabolic.Euclidean.Duhamel.FrozenPositiveDefinite
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.SmoothRepresentative
import DifferentialGeometry.Analysis.Elliptic.Euclidean.ScalarOperator.Basic
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients

section

noncomputable section
open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis
open Parabolic.Euclidean

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

private theorem second_fderiv_nonpos_of_localMax
    {u : V → ℝ} {x : V} (hu : ContDiffAt ℝ 2 u x) (hm : IsLocalMax u x) (v : V) :
    fderiv ℝ (fderiv ℝ u) x v v ≤ 0 := by
  have hh := secondDirectional_nonneg_of_localMin hu.neg hm.neg v
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : fderiv ℝ (fun q => fderiv ℝ u q v) x v = fderiv ℝ (fderiv ℝ u) x v v := by
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  have hfn : (fun q => fderiv ℝ (fun y => -u y) q v) =
      fun q => -(fderiv ℝ u q v) := by
    funext q
    rw [fderiv_fun_neg]
    rfl
  rw [hfn, fderiv_fun_neg] at hh
  change 0 ≤ -(fderiv ℝ (fun q => fderiv ℝ u q v) x v) at hh
  rw [he] at hh
  linarith

theorem matrixLap_fderiv_nonpos_of_localMax
    {u : V → ℝ} {x : V} (hu : ContDiffAt ℝ 2 u x) (hm : IsLocalMax u x)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    matrixLap A (fderiv ℝ (fderiv ℝ u) x) ≤ 0 := by
  let H := fderiv ℝ (fderiv ℝ u) x
  have hε (ε : ℝ) (hε : 0 < ε) : matrixLap (A + ε • 1) H ≤ 0 := by
    have hp : (A + ε • 1).PosDef :=
      Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε)
    rw [← spd_factorLap (A + ε • 1) hp]
    exact Finset.sum_nonpos (fun _ _ => second_fderiv_nonpos_of_localMax hu hm _)
  have heq (ε : ℝ) : matrixLap (A + ε • 1) H = matrixLap A H + ε * matrixLap 1 H := by
    simp only [matrixLap, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  by_contra hn
  have hp : 0 < matrixLap A H := lt_of_not_ge hn
  let ε := matrixLap A H / (2 * (|matrixLap 1 H| + 1))
  have hεp : 0 < ε := div_pos hp (by positivity)
  have hh := hε ε hεp
  rw [heq] at hh
  have he : ε * (2 * (|matrixLap 1 H| + 1)) = matrixLap A H :=
    div_mul_cancel₀ _ (by positivity)
  have hab := abs_le.mp (le_refl |matrixLap 1 H|)
  have hb := mul_le_mul_of_nonneg_left hab.1 hεp.le
  nlinarith

theorem divergence_nonpos_of_localMax
    {u : V → ℝ} {x : V} (hu : ContDiffAt ℝ 2 u x) (hm : IsLocalMax u x)
    (a : V → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x) (hpos : (a x).PosSemidef) :
    (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (a y) (DeGiorgi.smoothGradField u y) i) x
      (EuclideanSpace.single i 1)) ≤ 0 := by
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG (j : Fin d) : DifferentiableAt ℝ
      (fun y => DeGiorgi.smoothGradField u y j) x :=
    hd.clm_apply (differentiableAt_const _)
  have hGx (j : Fin d) : DeGiorgi.smoothGradField u x j = 0 := by
    change fderiv ℝ u x (EuclideanSpace.single j 1) = 0
    rw [hm.fderiv_eq_zero, zero_apply]
  have hDG (i j : Fin d) :
      fderiv ℝ (fun y => DeGiorgi.smoothGradField u y j) x (EuclideanSpace.single i 1) =
        fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    change fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x _ = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hpart (i j : Fin d) :
      fderiv ℝ (fun y => a y i j * DeGiorgi.smoothGradField u y j) x
        (EuclideanSpace.single i 1) = a x i j *
          fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    have hh := ((ha i j).hasFDerivAt.mul (hG j).hasFDerivAt).fderiv
    change fderiv ℝ (fun y : V => a y i j * DeGiorgi.smoothGradField u y j) x = _ at hh
    rw [hh]
    simp only [add_apply, smul_apply, smul_eq_mul, hGx, zero_mul, add_zero, hDG]
  have heq : (∑ i, fderiv ℝ
      (fun y => DeGiorgi.matMulE (a y) (DeGiorgi.smoothGradField u y) i) x
        (EuclideanSpace.single i 1)) = matrixLap (a x) (fderiv ℝ (fderiv ℝ u) x) := by
    apply Finset.sum_congr rfl
    intro i _
    change fderiv ℝ (fun y => ∑ j, a y i j * DeGiorgi.smoothGradField u y j) x
      (EuclideanSpace.single i 1) = _
    have hh := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => ((ha i j).mul (hG j)).hasFDerivAt)
    have hh' := hh.fderiv
    change fderiv ℝ (fun y : V => ∑ j, a y i j * DeGiorgi.smoothGradField u y j) x = _ at hh'
    rw [hh']
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hfun : ((fun y : V => a y i j) * (fun y => DeGiorgi.smoothGradField u y j)) =
        (fun y => a y i j * DeGiorgi.smoothGradField u y j) := by funext y; rfl
    rw [hfun, hpart]
    simp only [EuclideanSpace.basisFun_apply, smul_eq_mul]
  rw [heq]
  exact matrixLap_fderiv_nonpos_of_localMax hu hm (a x) hpos

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

private theorem flux_differentiableAt
    {a : V → Matrix (Fin d) (Fin d) ℝ} {u : V → ℝ} {x : V}
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hu : ContDiffAt ℝ 2 u x) (i : Fin d) :
    DifferentiableAt ℝ (fun y => DeGiorgi.matMulE (a y) (DeGiorgi.smoothGradField u y) i) x := by
  change DifferentiableAt ℝ (fun y => ∑ j, a y i j *
    fderiv ℝ u y (EuclideanSpace.single j 1)) x
  exact DifferentiableAt.fun_sum (fun j _ => (ha i j).mul
    (((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)))

theorem divergence_matMulE_smoothGradField_add_smul
    {a : V → Matrix (Fin d) (Fin d) ℝ} {u v : V → ℝ} {x : V}
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (c : ℝ) :
    (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (a y)
      (DeGiorgi.smoothGradField (fun z => u z + c * v z) y) i) x (EuclideanSpace.single i 1)) =
    (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (a y)
      (DeGiorgi.smoothGradField u y) i) x (EuclideanSpace.single i 1)) +
    c * (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (a y)
      (DeGiorgi.smoothGradField v y) i) x (EuclideanSpace.single i 1)) := by
  have hnear : ∀ᶠ y in 𝓝 x, DeGiorgi.smoothGradField (fun z => u z + c * v z) y =
      DeGiorgi.smoothGradField u y + c • DeGiorgi.smoothGradField v y := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hyu hyv
    ext j
    change fderiv ℝ (fun z => u z + c * v z) y (EuclideanSpace.single j 1) = _
    have hh := ((hyu.differentiableAt (by norm_num)).hasFDerivAt.add
      ((hyv.differentiableAt (by norm_num)).hasFDerivAt.const_mul c)).fderiv
    change fderiv ℝ (fun z => u z + c * v z) y = _ at hh
    rw [hh]
    rfl
  have hpart (i : Fin d) :
      fderiv ℝ (fun y => DeGiorgi.matMulE (a y)
        (DeGiorgi.smoothGradField (fun z => u z + c * v z) y) i) x =
      fderiv ℝ (fun y => DeGiorgi.matMulE (a y) (DeGiorgi.smoothGradField u y) i) x +
        c • fderiv ℝ (fun y => DeGiorgi.matMulE (a y) (DeGiorgi.smoothGradField v y) i) x := by
    have hf : (fun y => DeGiorgi.matMulE (a y)
        (DeGiorgi.smoothGradField (fun z => u z + c * v z) y) i) =ᶠ[𝓝 x]
        (fun y => DeGiorgi.matMulE (a y) (DeGiorgi.smoothGradField u y) i +
          c * DeGiorgi.matMulE (a y) (DeGiorgi.smoothGradField v y) i) := by
      filter_upwards [hnear] with y hy
      rw [hy]
      simp only [DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hf.fderiv_eq]
    have hh := ((flux_differentiableAt ha hu i).hasFDerivAt.add
      ((flux_differentiableAt ha hv i).hasFDerivAt.const_mul c)).fderiv
    exact hh
  simp_rw [hpart, add_apply, smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

namespace DifferentialGeometry.Analysis

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem divergence_matMulE_smoothGradField_eq_scalarEllipticOperator
    (A : V → Matrix (Fin d) (Fin d) ℝ) {u : V → ℝ} {x : V}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hu : ContDiffAt ℝ 2 u x) :
    (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (A y) (DeGiorgi.smoothGradField u y) i) x
      (EuclideanSpace.single i 1)) =
      scalarEllipticOperator A
        (fun y j => ∑ i, fderiv ℝ (fun z => A z i j) y (EuclideanSpace.single i 1)) u x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG (j : Fin d) : DifferentiableAt ℝ
      (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x :=
    hD.clm_apply (differentiableAt_const _)
  have hflux (i : Fin d) :
      fderiv ℝ (fun y => DeGiorgi.matMulE (A y) (DeGiorgi.smoothGradField u y) i) x
        (EuclideanSpace.single i 1) =
        ∑ j, (fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single i 1) *
          fderiv ℝ u x (EuclideanSpace.single j 1) +
          A x i j * fderiv ℝ (fderiv ℝ u) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
    change fderiv ℝ (fun y => ∑ j, A y i j *
      fderiv ℝ u y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_sum (fun j _ => (hA i j).fun_mul (hG j))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (hA i j) (hG j),
      fderiv_clm_apply hD (differentiableAt_const _)]
    simp only [add_apply, smul_apply, smul_eq_mul, fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
    ring
  simp_rw [hflux]
  simp only [scalarEllipticOperator, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun i j =>
    fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single i 1) *
      fderiv ℝ u x (EuclideanSpace.single j 1))]
  ring

end DifferentialGeometry.Analysis

end

end
