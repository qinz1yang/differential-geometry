import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FiniteTime.CurvatureBlowupRateIntrinsic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.BernsteinMaximum
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff BigOperators Bundle Topology

section ScalarAbsorption

theorem shi_first_cross_absorption {a v s : Real} (ha : 32 ≤ a) :
    8 * v * s ≤ a * s ^ 2 + v ^ 2 / 2 := by
  have hapos : (0 : Real) < a := by linarith
  nlinarith [sq_nonneg (a * s - 4 * v),
    mul_nonneg (sq_nonneg v) (by linarith : (0 : Real) ≤ a - 32), hapos]

theorem shi_first_reaction_le {a u v s cr K0 K1 X : Real}
    (ha : 32 ≤ a) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hK1 : 0 ≤ K1)
    (hcr : cr ≤ 8 * v * s)
    (hX : X ≤ (a + u) * (-2 * s ^ 2 + K1 * v) + v * (-2 * v + K0) + cr) :
    X ≤ -(1 / (a + 1) ^ 2) * ((a + u) * v) ^ 2 + (K0 + K1 * (a + 1)) ^ 2 / 2 := by
  have hapos : (0 : Real) < a := by linarith
  have hsq1 : (0 : Real) < (a + 1) ^ 2 := by positivity
  have habs : cr ≤ a * s ^ 2 + v ^ 2 / 2 :=
    hcr.trans (shi_first_cross_absorption ha)
  have hw2 : (a + u) * (-2 * s ^ 2) + a * s ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg hapos.le (sq_nonneg s), mul_nonneg hu0 (sq_nonneg s)]
  have hlin : (a + u) * (K1 * v) ≤ K1 * (a + 1) * v := by
    nlinarith [mul_nonneg (mul_nonneg hK1 hv) (sub_nonneg.mpr hu1)]
  have hstep : X ≤ -2 * v ^ 2 + v ^ 2 / 2 + (K0 + K1 * (a + 1)) * v := by
    have hexp : (a + u) * (-2 * s ^ 2 + K1 * v) + v * (-2 * v + K0) + cr =
        ((a + u) * (-2 * s ^ 2) + a * s ^ 2) + (a + u) * (K1 * v) +
          (-2 * v ^ 2) + K0 * v + (cr - a * s ^ 2) := by ring
    rw [hexp] at hX
    nlinarith [hw2, hlin, habs]
  have hquad : X ≤ -(v ^ 2) + (K0 + K1 * (a + 1)) ^ 2 / 2 := by
    nlinarith [sq_nonneg (K0 + K1 * (a + 1) - v)]
  have hFnn : 0 ≤ (a + u) * v := mul_nonneg (by linarith) hv
  have hFle : (a + u) * v ≤ (a + 1) * v := by
    nlinarith [mul_nonneg hv (sub_nonneg.mpr hu1)]
  have hFsq : ((a + u) * v) ^ 2 ≤ (a + 1) ^ 2 * v ^ 2 := by
    nlinarith [mul_self_le_mul_self hFnn hFle]
  have hdiv : 1 / (a + 1) ^ 2 * ((a + u) * v) ^ 2 ≤ v ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hsq1]
    nlinarith [hFsq]
  nlinarith [hquad, hdiv]

theorem shi_first_time_le {c C t T F X : Real}
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t) (htT : t ≤ T)
    (hX : X ≤ F + t * (-c * F ^ 2 + C)) :
    X ≤ -(c / 2 / t) * (t * F) ^ 2 + (1 / (2 * c) + C * T ^ 2) / t := by
  have h2c : (0 : Real) < 2 * c := by linarith
  have hT0 : (0 : Real) ≤ T := le_trans ht.le htT
  have htT2 : t ^ 2 ≤ T ^ 2 := by nlinarith [hT0, htT, ht.le]
  have hCT : C * t ^ 2 ≤ C * T ^ 2 := mul_le_mul_of_nonneg_left htT2 hC
  have hquad : t * F - c / 2 * (t * F) ^ 2 ≤ 1 / (2 * c) := by
    rw [le_div_iff₀ h2c]
    nlinarith [sq_nonneg (c * (t * F) - 1)]
  have hXt : X * t ≤ (F + t * (-c * F ^ 2 + C)) * t :=
    mul_le_mul_of_nonneg_right hX ht.le
  have hgoal : -(c / 2 / t) * (t * F) ^ 2 + (1 / (2 * c) + C * T ^ 2) / t =
      (-(c / 2) * (t * F) ^ 2 + (1 / (2 * c) + C * T ^ 2)) / t := by
    field_simp
  rw [hgoal, le_div_iff₀ ht]
  nlinarith [hquad, hCT, hXt]

end ScalarAbsorption

section Constants

def shiFirstReactionCoeff (d : Nat) (a : Real) : Real :=
  rmTowerCost d 0 + 2 * rmTowerCost d 1 * (a + 1)

def shiFirstBernsteinCoeff (a : Real) : Real := 1 / (a + 1) ^ 2


def shiFirstBernsteinConst (d : Nat) (a : Real) : Real :=
  shiFirstReactionCoeff d a ^ 2 / 2

def shiFirstTimeCoeff (a : Real) : Real := shiFirstBernsteinCoeff a / 2

def shiFirstTimeConst (d : Nat) (a T : Real) : Real :=
  (a + 1) ^ 2 / 2 + shiFirstBernsteinConst d a * T ^ 2


theorem shiFirstReactionCoeff_nonneg {a : Real} (ha : 32 ≤ a) (d : Nat) :
    0 ≤ shiFirstReactionCoeff d a := by
  have h0 := rmTowerCost_nonneg d 0
  have h1 := rmTowerCost_nonneg d 1
  have : (0 : Real) ≤ a + 1 := by linarith
  unfold shiFirstReactionCoeff
  positivity


theorem shiFirstBernsteinCoeff_pos {a : Real} (ha : 32 ≤ a) :
    0 < shiFirstBernsteinCoeff a := by
  have h : (0 : Real) < (a + 1) ^ 2 := by positivity
  unfold shiFirstBernsteinCoeff
  positivity


theorem shiFirstBernsteinConst_nonneg (d : Nat) (a : Real) :
    0 ≤ shiFirstBernsteinConst d a := by
  unfold shiFirstBernsteinConst
  positivity


theorem shiFirstTimeCoeff_pos {a : Real} (ha : 32 ≤ a) :
    0 < shiFirstTimeCoeff a := by
  have h := shiFirstBernsteinCoeff_pos ha
  unfold shiFirstTimeCoeff
  linarith


theorem shiFirstTimeConst_nonneg {a : Real} (ha : 32 ≤ a) (d : Nat) (T : Real) :
    0 ≤ shiFirstTimeConst d a T := by
  have h := shiFirstBernsteinConst_nonneg d a
  have h1 : (0 : Real) ≤ (a + 1) ^ 2 / 2 := by positivity
  have h2 : (0 : Real) ≤ shiFirstBernsteinConst d a * T ^ 2 := by positivity
  unfold shiFirstTimeConst
  linarith

theorem one_div_two_mul_shiFirstBernsteinCoeff {a : Real} (ha : 32 ≤ a) :
    1 / (2 * shiFirstBernsteinCoeff a) = (a + 1) ^ 2 / 2 := by
  have h : (a + 1) ≠ 0 := by
    intro hcon
    linarith
  unfold shiFirstBernsteinCoeff
  field_simp

end Constants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

section ParabolicAlgebra

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [BoundarylessManifold I M] in
theorem parabolicOperatorWithDrift_const_add_mul
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u v : Real -> M -> Real) (a t : Real) (x : M)
    (hu_time : DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hv_time : DifferentiableWithinAt Real (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hu_smooth : ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hv_smooth : ContMDiff I 𝓘(Real, Real) ∞ (v t)) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => (a + u s y) * v s y) t x =
      (a + u t x) * parabolicOperatorWithDrift (I := I) G T X v t x +
        v t x * parabolicOperatorWithDrift (I := I) G T X u t x -
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t (u t) x)
            (gradientAt (I := I) G t (v t) x) := by
  have hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y :=
    fun y => hu_smooth.contMDiffAt.mdifferentiableAt (by simp)
  have hv_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (v t) y :=
    fun y => hv_smooth.contMDiffAt.mdifferentiableAt (by simp)
  have hav_smooth : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M => a * v t y) :=
    contMDiff_const.mul hv_smooth
  have huv_smooth : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M => u t y * v t y) :=
    hu_smooth.mul hv_smooth
  have hsplit : (fun s y => (a + u s y) * v s y) =
      (fun s (y : M) => a * v s y + u s y * v s y) := by
    funext s y
    ring
  rw [hsplit]
  rw [parabolic_add (I := I) G T X (fun s (y : M) => a * v s y)
    (fun s (y : M) => u s y * v s y) t x (hv_time.const_mul a)
    (hu_time.mul hv_time)
    (fun y => (hav_smooth.contMDiffAt.mdifferentiableAt (by simp)))
    (fun y => (huv_smooth.contMDiffAt.mdifferentiableAt (by simp)))
    (gradientFun_mdiffAt (I := I) (G.metric t) hav_smooth x)
    (gradientFun_mdiffAt (I := I) (G.metric t) huv_smooth x)]
  rw [parabolic_smul (I := I) G T X a v t x hv_time hv_space
    (gradientFun_mdiffAt (I := I) (G.metric t) hv_smooth x)]
  rw [parabolic_mul (I := I) G T X u v t x hu_time hv_time hu_space hv_space
    (fun y => gradientFun_mdiffAt (I := I) (G.metric t) hu_smooth y)
    (fun y => gradientFun_mdiffAt (I := I) (G.metric t) hv_smooth y)]
  ring

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [IsManifold I 2 M] [T2Space M] [BoundarylessManifold I M] in
theorem parabolicOperatorWithDrift_time_mul
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (F : Real -> M -> Real) (t : Real) (x : M)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hF_time : DifferentiableWithinAt Real (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hF_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (F t) y)
    (hF_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (F t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X (fun s y => s * F s y) t x =
      F t x + t * parabolicOperatorWithDrift (I := I) G T X F t x := by
  have hid : DifferentiableWithinAt Real (fun s : Real => s) (Set.Icc 0 T) t :=
    differentiableWithinAt_id
  have hone : derivWithin (fun s : Real => s) (Set.Icc 0 T) t = 1 :=
    (hasDerivWithinAt_id t (Set.Icc 0 T)).derivWithin huniq
  have hderiv : derivWithin (fun s : Real => s * F s x) (Set.Icc 0 T) t =
      1 * F t x + t * derivWithin (fun s : Real => F s x) (Set.Icc 0 T) t := by
    rw [derivWithin_fun_mul hid hF_time, hone]
  have hsmul : (fun y : M => t * F t y) = t • F t := by
    funext y
    simp [smul_eq_mul]
  have hheat : heatOperatorWithDrift (I := I) G t (X t) (fun y : M => t * F t y) x =
      t * heatOperatorWithDrift (I := I) G t (X t) (F t) x := by
    rw [hsmul]
    exact heatOperatorWithDrift_const_smul (I := I) G t (X t) t hF_space hF_grad
  rw [parabolicOperatorWithDrift_eq, parabolicOperatorWithDrift_eq, hderiv]
  change _ - heatOperatorWithDrift (I := I) G t (X t) (fun y : M => t * F t y) x = _
  rw [hheat]
  ring

end ParabolicAlgebra

section TowerBounds

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem exists_hasDerivAt_nablaKRm04NormSqIntrinsic
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (k : Nat)
    {t : Real} (htreg : t ∈ D.regular) (x : M) :
    ∃ d : Real,
      HasDerivAt (fun s : Real => nablaKRm04NormSqIntrinsic (I := I) S k s x) d t ∧
        d ≤ laplacianAt (I := I) (flowG (I := I) S) t
              (nablaKRm04NormSqIntrinsic (I := I) S k t) x +
            (-2 * nablaKRm04NormSqIntrinsic (I := I) S (k + 1) t x +
              towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
                (rmTowerCost (Module.finrank Real E) k) k t x) := by
  obtain ⟨d, hd, hle⟩ := towerHeatBoundOn_of_solution (I := I) S hS k ⟨t, htreg⟩ x
  refine ⟨d, hd.hasDerivAt (D.regular_mem_nhds htreg), ?_⟩
  rw [nablaKNormLap_eq_laplacianAt (I := I) S k t x] at hle
  exact hle

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem differentiableAt_nablaKRm04NormSqIntrinsic
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (k : Nat)
    {t : Real} (htreg : t ∈ D.regular) (x : M) :
    DifferentiableAt Real
      (fun s : Real => nablaKRm04NormSqIntrinsic (I := I) S k s x) t := by
  obtain ⟨d, hd, -⟩ :=
    exists_hasDerivAt_nablaKRm04NormSqIntrinsic (I := I) S hS k htreg x
  exact hd.differentiableAt

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem parabolicOperatorWithDrift_nablaKRm04NormSqIntrinsic_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real} (hT : 0 < T) (k : Nat)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (htreg : t ∈ D.regular) (x : M) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (nablaKRm04NormSqIntrinsic (I := I) S k) t x ≤
      -2 * nablaKRm04NormSqIntrinsic (I := I) S (k + 1) t x +
        towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
          (rmTowerCost (Module.finrank Real E) k) k t x := by
  obtain ⟨d, hd, hle⟩ :=
    exists_hasDerivAt_nablaKRm04NormSqIntrinsic (I := I) S hS k htreg x
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have hderiv : derivWithin
      (fun s : Real => nablaKRm04NormSqIntrinsic (I := I) S k s x) (Set.Icc 0 T) t = d :=
    hd.hasDerivWithinAt.derivWithin huniq
  rw [parabolicOperatorWithDrift_eq, hderiv]
  simp only [heatOperatorWithDrift, driftTerm_zero_drift, add_zero]
  linarith

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem parabolicOperatorWithDrift_nablaKRm04NormSqIntrinsic_zero_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real} (hT : 0 < T)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (htreg : t ∈ D.regular) (x : M)
    (hu : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (nablaKRm04NormSqIntrinsic (I := I) S 0) t x ≤
      -2 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x +
        rmTowerCost (Module.finrank Real E) 0 := by
  have hbase :=
    parabolicOperatorWithDrift_nablaKRm04NormSqIntrinsic_le (I := I) S hS hT 0 ht htreg x
  have hnn : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S 0 t x :=
    nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x
  have hs0 : 0 ≤ Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) :=
    Real.sqrt_nonneg _
  have hs1 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hu
    simpa using h
  have hsum : towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
      (rmTowerCost (Module.finrank Real E) 0) 0 t x =
      rmTowerCost (Module.finrank Real E) 0 *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) := by
    simp [towerReactionSum]
  have hcost := rmTowerCost_nonneg (Module.finrank Real E) 0
  have hss : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) ≤ 1 := by
    nlinarith [hs0, hs1]
  have hsss : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) ≤ 1 := by
    nlinarith [hs0, hs1, hss, mul_nonneg hs0 hs0]
  have hcube : rmTowerCost (Module.finrank Real E) 0 *
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) ≤
      rmTowerCost (Module.finrank Real E) 0 := by
    nlinarith [hsss, hcost]
  rw [hsum] at hbase
  linarith

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem parabolicOperatorWithDrift_nablaKRm04NormSqIntrinsic_one_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real} (hT : 0 < T)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (htreg : t ∈ D.regular) (x : M)
    (hu : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (nablaKRm04NormSqIntrinsic (I := I) S 1) t x ≤
      -2 * nablaKRm04NormSqIntrinsic (I := I) S 2 t x +
        2 * rmTowerCost (Module.finrank Real E) 1 *
          nablaKRm04NormSqIntrinsic (I := I) S 1 t x := by
  have hbase :=
    parabolicOperatorWithDrift_nablaKRm04NormSqIntrinsic_le (I := I) S hS hT 1 ht htreg x
  have hnn0 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S 0 t x :=
    nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x
  have hnn1 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S 1 t x :=
    nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
  have hs0 : 0 ≤ Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) :=
    Real.sqrt_nonneg _
  have hs1 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hu
    simpa using h
  have hv : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) =
      nablaKRm04NormSqIntrinsic (I := I) S 1 t x := Real.mul_self_sqrt hnn1
  have hsum : towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
      (rmTowerCost (Module.finrank Real E) 1) 1 t x =
      rmTowerCost (Module.finrank Real E) 1 *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) +
        rmTowerCost (Module.finrank Real E) 1 *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) := by
    simp [towerReactionSum, Finset.sum_range_succ]
  have hcost := rmTowerCost_nonneg (Module.finrank Real E) 1
  have hbound : towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
      (rmTowerCost (Module.finrank Real E) 1) 1 t x ≤
      2 * rmTowerCost (Module.finrank Real E) 1 *
        nablaKRm04NormSqIntrinsic (I := I) S 1 t x := by
    rw [hsum]
    have heq : rmTowerCost (Module.finrank Real E) 1 *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) +
        rmTowerCost (Module.finrank Real E) 1 *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) =
        2 * rmTowerCost (Module.finrank Real E) 1 *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
          (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x)) := by ring
    rw [heq, hv]
    nlinarith [mul_nonneg
      (mul_nonneg (by linarith :
        (0 : Real) ≤ 2 * rmTowerCost (Module.finrank Real E) 1) hnn1)
      (sub_nonneg.mpr hs1)]
  linarith

end TowerBounds

section GradientCrossTerm

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem inner_gradient_nablaKRm04NormSqIntrinsic_sq_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    ((flowG (I := I) S).metric t).inner x
        (gradientAt (I := I) (flowG (I := I) S) t
          (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x)
        (gradientAt (I := I) (flowG (I := I) S) t
          (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x) ^ 2 ≤
      16 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x *
        nablaKRm04NormSqIntrinsic (I := I) S 1 t x ^ 2 *
        nablaKRm04NormSqIntrinsic (I := I) S 2 t x := by
  have hA : ((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x)
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x) ≤
      4 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x *
        nablaKRm04NormSqIntrinsic (I := I) S 1 t x := by
    simpa [flowG, gradientAt] using towerNorm_grad_le (I := I) (S := S) 0 t x
  have hB : ((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x)
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x) ≤
      4 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x *
        nablaKRm04NormSqIntrinsic (I := I) S 2 t x := by
    simpa [flowG, gradientAt] using towerNorm_grad_le (I := I) (S := S) 1 t x
  have hBB : 0 ≤ ((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x)
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x) :=
    DifferentialGeometry.metric_inner_self_nonneg
      (I := I) (M := M) ((flowG (I := I) S).metric t) x _
  have hprod : 0 ≤ 4 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x *
      nablaKRm04NormSqIntrinsic (I := I) S 1 t x := by
    have h0 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x
    have h1 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
    positivity
  have hcs := DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
    (I := I) (M := M) ((flowG (I := I) S).metric t) x
    (gradientAt (I := I) (flowG (I := I) S) t
      (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x)
    (gradientAt (I := I) (flowG (I := I) S) t
      (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x)
  have hmul := mul_le_mul hA hB hBB hprod
  nlinarith [hcs, hmul]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem neg_two_inner_gradient_nablaKRm04NormSqIntrinsic_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (hu : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1) :
    -2 * ((flowG (I := I) S).metric t).inner x
        (gradientAt (I := I) (flowG (I := I) S) t
          (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x)
        (gradientAt (I := I) (flowG (I := I) S) t
          (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x) ≤
      8 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) := by
  have h0 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x
  have h1 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
  have h2 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 2 t x
  have hs2 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) ^ 2 =
      nablaKRm04NormSqIntrinsic (I := I) S 2 t x := Real.sq_sqrt h2
  have hs0 : 0 ≤ Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) :=
    Real.sqrt_nonneg _
  have hcs := inner_gradient_nablaKRm04NormSqIntrinsic_sq_le (I := I) S t x
  have hww : (4 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x *
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x)) ^ 2 =
      16 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x ^ 2 *
        nablaKRm04NormSqIntrinsic (I := I) S 2 t x := by
    have hexp : (4 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x)) ^ 2 =
        16 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x ^ 2 *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) ^ 2 := by ring
    rw [hexp, hs2]
  have hsq : ((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x)
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x) ^ 2 ≤
      (4 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x)) ^ 2 := by
    rw [hww]
    refine hcs.trans ?_
    nlinarith [mul_nonneg
      (mul_nonneg (by positivity :
        (0 : Real) ≤ 16 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x ^ 2) h2)
      (sub_nonneg.mpr hu)]
  have habs := abs_le_of_sq_le_sq hsq (by positivity)
  have hneg := neg_le_abs (((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x)
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x))
  linarith

end GradientCrossTerm

section BernsteinQuantity

def shiFirstBernsteinQuantity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (a : Real) :
    Real -> M -> Real :=
  fun t x => (a + nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
    nablaKRm04NormSqIntrinsic (I := I) S 1 t x


def shiFirstBernsteinTimeQuantity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (a : Real) :
    Real -> M -> Real :=
  fun t x => t * shiFirstBernsteinQuantity (I := I) S a t x

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem shiFirstBernsteinQuantity_nonneg
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) {a : Real}
    (ha : 0 ≤ a) (t : Real) (x : M) :
    0 ≤ shiFirstBernsteinQuantity (I := I) S a t x := by
  have h0 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x
  have h1 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
  unfold shiFirstBernsteinQuantity
  positivity

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem shiFirstBernsteinTimeQuantity_nonneg
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) {a t : Real}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (x : M) :
    0 ≤ shiFirstBernsteinTimeQuantity (I := I) S a t x := by
  have h := shiFirstBernsteinQuantity_nonneg (I := I) S ha t x
  unfold shiFirstBernsteinTimeQuantity
  positivity

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem shiFirstBernsteinTimeQuantity_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (a : Real) (x : M) :
    shiFirstBernsteinTimeQuantity (I := I) S a 0 x = 0 := by
  unfold shiFirstBernsteinTimeQuantity
  ring

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem contMDiff_shiFirstBernsteinQuantity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (a t : Real) :
    ContMDiff I 𝓘(Real, Real) ∞ (shiFirstBernsteinQuantity (I := I) S a t) := by
  have h0 := nablaKNorm_smooth (I := I) S t 0
  have h1 := nablaKNorm_smooth (I := I) S t 1
  exact (contMDiff_const.add h0).mul h1

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem contMDiff_shiFirstBernsteinTimeQuantity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (a t : Real) :
    ContMDiff I 𝓘(Real, Real) ∞ (shiFirstBernsteinTimeQuantity (I := I) S a t) :=
  contMDiff_const.mul (contMDiff_shiFirstBernsteinQuantity (I := I) S a t)

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem differentiableAt_shiFirstBernsteinQuantity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (a : Real)
    {t : Real} (htreg : t ∈ D.regular) (x : M) :
    DifferentiableAt Real
      (fun s : Real => shiFirstBernsteinQuantity (I := I) S a s x) t := by
  have h0 := differentiableAt_nablaKRm04NormSqIntrinsic (I := I) S hS 0 htreg x
  have h1 := differentiableAt_nablaKRm04NormSqIntrinsic (I := I) S hS 1 htreg x
  exact (differentiableAt_const a |>.add h0).mul h1

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem differentiableAt_shiFirstBernsteinTimeQuantity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (a : Real)
    {t : Real} (htreg : t ∈ D.regular) (x : M) :
    DifferentiableAt Real
      (fun s : Real => shiFirstBernsteinTimeQuantity (I := I) S a s x) t :=
  differentiableAt_id.mul
    (differentiableAt_shiFirstBernsteinQuantity (I := I) S hS a htreg x)

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem parabolicOperatorWithDrift_shiFirstBernsteinQuantity_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T a : Real} (hT : 0 < T) (ha : 32 ≤ a)
    (hreg : Set.Icc 0 T ⊆ D.regular)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (x : M)
    (hu : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (shiFirstBernsteinQuantity (I := I) S a) t x ≤
      -shiFirstBernsteinCoeff a * shiFirstBernsteinQuantity (I := I) S a t x ^ 2 +
        shiFirstBernsteinConst (Module.finrank Real E) a := by
  have htreg := hreg ht
  have hut := hu
  have h0 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x
  have h1 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
  have h2 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 2 t x
  have hprod := parabolicOperatorWithDrift_const_add_mul (I := I)
    (G := flowG (I := I) S) T (fun _ y => (0 : TangentSpace I y))
    (nablaKRm04NormSqIntrinsic (I := I) S 0)
    (nablaKRm04NormSqIntrinsic (I := I) S 1) a t x
    ((differentiableAt_nablaKRm04NormSqIntrinsic (I := I) S hS 0 htreg x)
      |>.differentiableWithinAt)
    ((differentiableAt_nablaKRm04NormSqIntrinsic (I := I) S hS 1 htreg x)
      |>.differentiableWithinAt)
    (nablaKNorm_smooth (I := I) S t 0) (nablaKNorm_smooth (I := I) S t 1)
  have hLu := parabolicOperatorWithDrift_nablaKRm04NormSqIntrinsic_zero_le
    (I := I) S hS hT ht htreg x hut
  have hLv := parabolicOperatorWithDrift_nablaKRm04NormSqIntrinsic_one_le
    (I := I) S hS hT ht htreg x hut
  have hcross := neg_two_inner_gradient_nablaKRm04NormSqIntrinsic_le
    (I := I) S t x hut
  have hs2 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) ^ 2 =
      nablaKRm04NormSqIntrinsic (I := I) S 2 t x := Real.sq_sqrt h2
  have hanonneg : (0 : Real) ≤ a + nablaKRm04NormSqIntrinsic (I := I) S 0 t x := by
    linarith
  have hLv' : parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
      (fun _ y => (0 : TangentSpace I y))
      (nablaKRm04NormSqIntrinsic (I := I) S 1) t x ≤
      -2 * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) ^ 2 +
        2 * rmTowerCost (Module.finrank Real E) 1 *
          nablaKRm04NormSqIntrinsic (I := I) S 1 t x := by
    rw [hs2]
    exact hLv
  have hstep1 := mul_le_mul_of_nonneg_left hLv' hanonneg
  have hstep2 := mul_le_mul_of_nonneg_left hLu h1
  have hX : parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
      (fun _ y => (0 : TangentSpace I y))
      (shiFirstBernsteinQuantity (I := I) S a) t x ≤
      (a + nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
          (-2 * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) ^ 2 +
            2 * rmTowerCost (Module.finrank Real E) 1 *
              nablaKRm04NormSqIntrinsic (I := I) S 1 t x) +
        nablaKRm04NormSqIntrinsic (I := I) S 1 t x *
          (-2 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x +
            rmTowerCost (Module.finrank Real E) 0) +
        (-2 * ((flowG (I := I) S).metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t
            (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x)
          (gradientAt (I := I) (flowG (I := I) S) t
            (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x)) := by
    have hunfold : shiFirstBernsteinQuantity (I := I) S a =
        fun s (y : M) => (a + nablaKRm04NormSqIntrinsic (I := I) S 0 s y) *
          nablaKRm04NormSqIntrinsic (I := I) S 1 s y := rfl
    rw [hunfold, hprod]
    linarith
  have hmain := shi_first_reaction_le (a := a)
    (u := nablaKRm04NormSqIntrinsic (I := I) S 0 t x)
    (v := nablaKRm04NormSqIntrinsic (I := I) S 1 t x)
    (s := Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x))
    (cr := -2 * ((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x)
      (gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S 1 t) x))
    (K0 := rmTowerCost (Module.finrank Real E) 0)
    (K1 := 2 * rmTowerCost (Module.finrank Real E) 1)
    ha h0 hut h1
    (by have := rmTowerCost_nonneg (Module.finrank Real E) 1; linarith)
    hcross hX
  have hconst : -shiFirstBernsteinCoeff a *
        shiFirstBernsteinQuantity (I := I) S a t x ^ 2 +
      shiFirstBernsteinConst (Module.finrank Real E) a =
      -(1 / (a + 1) ^ 2) * ((a + nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
          nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ^ 2 +
        (rmTowerCost (Module.finrank Real E) 0 +
          2 * rmTowerCost (Module.finrank Real E) 1 * (a + 1)) ^ 2 / 2 := rfl
  rw [hconst]
  exact hmain

theorem parabolicOperatorWithDrift_shiFirstBernsteinTimeQuantity_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T a : Real} (hT : 0 < T) (ha : 32 ≤ a)
    (hreg : Set.Icc 0 T ⊆ D.regular)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) (x : M)
    (hu : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (shiFirstBernsteinTimeQuantity (I := I) S a) t x ≤
      -(shiFirstTimeCoeff a / t) *
          shiFirstBernsteinTimeQuantity (I := I) S a t x ^ 2 +
        shiFirstTimeConst (Module.finrank Real E) a T / t := by
  have htreg := hreg ht
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have hFsmooth := contMDiff_shiFirstBernsteinQuantity (I := I) S a t
  have hsplit : shiFirstBernsteinTimeQuantity (I := I) S a =
      fun s (y : M) => s * shiFirstBernsteinQuantity (I := I) S a s y := rfl
  have hLG := parabolicOperatorWithDrift_time_mul (I := I)
    (G := flowG (I := I) S) T (fun _ y => (0 : TangentSpace I y))
    (shiFirstBernsteinQuantity (I := I) S a) t x huniq
    ((differentiableAt_shiFirstBernsteinQuantity (I := I) S hS a htreg x)
      |>.differentiableWithinAt)
    (fun y => hFsmooth.contMDiffAt.mdifferentiableAt (by simp))
    (gradientFun_mdiffAt (I := I) ((flowG (I := I) S).metric t) hFsmooth x)
  have hLF := parabolicOperatorWithDrift_shiFirstBernsteinQuantity_le
    (I := I) S hS hT ha hreg ht x hu
  have hcpos := shiFirstBernsteinCoeff_pos ha
  have hCnn := shiFirstBernsteinConst_nonneg (Module.finrank Real E) a
  have hX : parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
      (fun _ y => (0 : TangentSpace I y))
      (shiFirstBernsteinTimeQuantity (I := I) S a) t x ≤
      shiFirstBernsteinQuantity (I := I) S a t x +
        t * (-shiFirstBernsteinCoeff a *
            shiFirstBernsteinQuantity (I := I) S a t x ^ 2 +
          shiFirstBernsteinConst (Module.finrank Real E) a) := by
    rw [hsplit, hLG]
    have := mul_le_mul_of_nonneg_left hLF htpos.le
    linarith
  have hkey := shi_first_time_le (c := shiFirstBernsteinCoeff a)
    (C := shiFirstBernsteinConst (Module.finrank Real E) a)
    (t := t) (T := T) (F := shiFirstBernsteinQuantity (I := I) S a t x)
    hcpos hCnn htpos ht.2 hX
  have hconst : 1 / (2 * shiFirstBernsteinCoeff a) +
      shiFirstBernsteinConst (Module.finrank Real E) a * T ^ 2 =
      shiFirstTimeConst (Module.finrank Real E) a T := by
    rw [one_div_two_mul_shiFirstBernsteinCoeff ha]
    rfl
  rw [hconst] at hkey
  have hcoeff : shiFirstBernsteinCoeff a / 2 / t = shiFirstTimeCoeff a / t := rfl
  rw [hcoeff] at hkey
  have hquant : shiFirstBernsteinTimeQuantity (I := I) S a t x =
      t * shiFirstBernsteinQuantity (I := I) S a t x := rfl
  rw [hquant]
  exact hkey

end BernsteinQuantity

section Regularity

omit [NeZero (Module.finrank Real E)]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem continuousOn_shiFirstBernsteinTimeQuantity
    {alpha omega T a : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S) (halpha : alpha < 0) (hTomega : T < omega) :
    ContinuousOn
      (fun p : Real × M => shiFirstBernsteinTimeQuantity (I := I) S a p.1 p.2)
      (spacetimeSlab (M := M) T) := by
  have hsub : spacetimeSlab (M := M) T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular ×ˢ
        (Set.univ : Set M) := by
    rintro ⟨s, y⟩ hp
    exact ⟨⟨lt_of_lt_of_le halpha hp.1.1, lt_of_le_of_lt hp.1.2 hTomega⟩, trivial⟩
  have h0 := ((towerNorm_joint (I := I) hS 0).continuousOn).mono hsub
  have h1 := ((towerNorm_joint (I := I) hS 1).continuousOn).mono hsub
  have hres : ContinuousOn
      (fun p : Real × M => p.1 *
        ((a + nablaKRm04NormSqIntrinsic (I := I) S 0 p.1 p.2) *
          nablaKRm04NormSqIntrinsic (I := I) S 1 p.1 p.2))
      (spacetimeSlab (M := M) T) :=
    (continuous_fst.continuousOn).mul ((continuousOn_const.add h0).mul h1)
  exact hres

end Regularity

section CutoffConsequence

theorem shiFirstBernsteinTimeQuantity_cutoff_le
    {alpha omega T a eps : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    (cut : ShiFixedCutoff (I := I) (flowG (I := I) S) T eps)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (ha : 32 ≤ a)
    (hu : ∀ s ∈ Set.Icc 0 T, ∀ y : M, 0 < cut.chi s y →
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      cut.chi t x * shiFirstBernsteinTimeQuantity (I := I) S a t x ≤
        bernsteinMaximumBound (shiFirstTimeCoeff a)
          (shiFirstTimeConst (Module.finrank Real E) a T) eps T := by
  have hreg : Set.Icc 0 T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
    intro s hs
    exact ⟨lt_of_lt_of_le halpha hs.1, lt_of_le_of_lt hs.2 hTomega⟩
  refine bernstein_maximum_of_fixed_cutoff (I := I) cut
    (shiFirstBernsteinTimeQuantity (I := I) S a) hT
    (shiFirstTimeCoeff_pos ha) (shiFirstTimeConst_nonneg ha (Module.finrank Real E) T)
    (fun s hs y => shiFirstBernsteinTimeQuantity_nonneg (I := I) S
      (by linarith : (0 : Real) ≤ a) hs.1 y)
    (fun y => shiFirstBernsteinTimeQuantity_zero (I := I) S a y)
    (continuousOn_shiFirstBernsteinTimeQuantity (I := I) hS halpha hTomega)
    (fun s hs _ y =>
      (differentiableAt_shiFirstBernsteinTimeQuantity (I := I) S hS a
        (hreg hs) y).differentiableWithinAt)
    (fun s hs _ y =>
      (contMDiff_shiFirstBernsteinTimeQuantity (I := I) S a s).contMDiffAt.mdifferentiableAt
        (by simp))
    (fun s hs _ y =>
      gradientFun_mdiffAt (I := I) ((flowG (I := I) S).metric s)
        (contMDiff_shiFirstBernsteinTimeQuantity (I := I) S a s) y)
    (fun s hs hspos y hy =>
      parabolicOperatorWithDrift_shiFirstBernsteinTimeQuantity_le
        (I := I) S hS hT ha hreg hs hspos y (hu s hs y hy))

end CutoffConsequence

end DifferentialGeometry.PDE.RicciFlow
