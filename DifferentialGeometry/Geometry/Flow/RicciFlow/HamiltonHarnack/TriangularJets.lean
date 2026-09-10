import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.CurvatureBlock
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Norm.Product
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.OneJet
import DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.TotalNabla0S
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Linearity
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ProductLeibniz
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Geometry Geometry.Connection Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorLieDeriv
open scoped Manifold ContDiff BigOperators

variable {Idx : Type*}

def hamiltonTriangularA
    (S : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) : Real :=
  (1 / 2 : Real) * (S a b * W c - S a c * W b)

def hamiltonTestJetDU
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) : Real :=
  (1 / 2 : Real) * (Ric a b * W c - Ric a c * W b) +
    (1 / (4 * clock.elapsed) : Real) * (h a b * W c - h a c * W b)

def hamiltonTriangularConnectionU
    (S : Idx -> Idx -> Real) (W : Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real) (a b c : Idx) : Real :=
  DU a b c - hamiltonTriangularA S W a b c

def hamiltonTriangularConnectionW
    (DW : Idx -> Idx -> Real) (a b : Idx) : Real :=
  DW a b

theorem hamiltonTriangularA_skew
    (S : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) :
    hamiltonTriangularA S W a b c = -hamiltonTriangularA S W a c b := by
  unfold hamiltonTriangularA
  ring

theorem hamiltonTestJetDU_skew
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) :
    hamiltonTestJetDU clock Ric h W a b c =
      -hamiltonTestJetDU clock Ric h W a c b := by
  unfold hamiltonTestJetDU
  ring

theorem hamiltonTestJetDU_eq_triangularA
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) :
    hamiltonTestJetDU clock Ric h W a b c =
      hamiltonTriangularA
        (fun i j => Ric i j + (1 / (2 * clock.elapsed) : Real) * h i j)
        W a b c := by
  unfold hamiltonTestJetDU hamiltonTriangularA
  field_simp [HarnackClock.elapsed_ne_zero clock]
  ring

theorem hamiltonTriangularConnectionU_zero_of_testJet
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) :
    hamiltonTriangularConnectionU
        (fun i j => Ric i j + (1 / (2 * clock.elapsed) : Real) * h i j)
        W (hamiltonTestJetDU clock Ric h W) a b c = 0 := by
  unfold hamiltonTriangularConnectionU
  rw [hamiltonTestJetDU_eq_triangularA]
  ring

theorem hamiltonTriangularConnectionW_zero_of_testJet
    (DW : Idx -> Idx -> Real) (a b : Idx)
    (hDW : DW a b = 0) :
    hamiltonTriangularConnectionW DW a b = 0 := by
  exact hDW

theorem hamiltonTestJetDU_clock_coefficient
    (clock : HarnackClock) :
    (1 / (4 * clock.elapsed) : Real) =
      (1 / 2 : Real) * (1 / (2 * clock.elapsed) : Real) := by
  field_simp [HarnackClock.elapsed_ne_zero clock]
  ring

theorem hamiltonTestJetDU_clock_coefficient_pos
    (clock : HarnackClock) :
    0 < (1 / (4 * clock.elapsed) : Real) := by
  exact one_div_pos.mpr (mul_pos (by norm_num) clock.elapsed_pos)

theorem hamiltonTestJetDU_zero_of_zero_W
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (a b c : Idx) :
    hamiltonTestJetDU clock Ric h (fun _ => 0) a b c = 0 := by
  unfold hamiltonTestJetDU
  simp

private theorem hamiltonTriangularA_sq_sum_le
    {Idx : Type*} [Fintype Idx]
    (S : Idx -> Idx -> Real) (W : Idx -> Real) (D : Real)
    (hD : 0 <= D) (hS : forall a b, |S a b| <= D) :
    (∑ e, ∑ a, ∑ b, (hamiltonTriangularA S W e a b) ^ 2) <=
      D ^ 2 * (Fintype.card Idx : Real) ^ 2 *
        (∑ a, (W a) ^ 2) := by
  classical
  have hterm : forall e a b,
      (hamiltonTriangularA S W e a b) ^ 2 <=
        (D ^ 2 / 2) * ((W a) ^ 2 + (W b) ^ 2) := by
    intro e a b
    have hea : (S e a) ^ 2 <= D ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hD]
      exact hS e a
    have heb : (S e b) ^ 2 <= D ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hD]
      exact hS e b
    have hwa : 0 <= (W a) ^ 2 := sq_nonneg _
    have hwb : 0 <= (W b) ^ 2 := sq_nonneg _
    have hmulA : (S e a) ^ 2 * (W b) ^ 2 <= D ^ 2 * (W b) ^ 2 :=
      mul_le_mul_of_nonneg_right hea hwb
    have hmulB : (S e b) ^ 2 * (W a) ^ 2 <= D ^ 2 * (W a) ^ 2 :=
      mul_le_mul_of_nonneg_right heb hwa
    unfold hamiltonTriangularA
    nlinarith [sq_nonneg (S e a * W b + S e b * W a)]
  calc
    (∑ e, ∑ a, ∑ b, (hamiltonTriangularA S W e a b) ^ 2) <=
        ∑ e, ∑ a, ∑ b,
          (D ^ 2 / 2) * ((W a) ^ 2 + (W b) ^ 2) := by
      exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun a _ =>
        Finset.sum_le_sum fun b _ => hterm e a b
    _ = D ^ 2 * (Fintype.card Idx : Real) ^ 2 *
        (∑ a, (W a) ^ 2) := by
      have hsum (q : Real) :
          (∑ x, q * (W x) ^ 2) = q * (∑ x, (W x) ^ 2) := by
        rw [Finset.mul_sum]
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      have hfirst :
          (∑ x, (Fintype.card Idx : Real) *
              (D ^ 2 / 2 * (W x) ^ 2)) =
            ((Fintype.card Idx : Real) * D ^ 2 / 2) *
              (∑ x, (W x) ^ 2) := by
        calc
          (∑ x, (Fintype.card Idx : Real) *
              (D ^ 2 / 2 * (W x) ^ 2)) =
              ∑ x, ((Fintype.card Idx : Real) * D ^ 2 / 2) *
                (W x) ^ 2 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
          _ = ((Fintype.card Idx : Real) * D ^ 2 / 2) *
              (∑ x, (W x) ^ 2) := hsum _
      have hsecond :
          (∑ x, D ^ 2 / 2 * (W x) ^ 2) =
            (D ^ 2 / 2) * (∑ x, (W x) ^ 2) := by
        exact hsum _
      rw [hfirst, hsecond]
      ring

theorem hamiltonTestJetDU_sq_sum_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (clock : HarnackClock) (Ric : Idx -> Idx -> Real)
    (W : Idx -> Real) (B : Real) (hB : 0 <= B)
    (hRic : forall a b, |Ric a b| <= B) :
    (∑ e, ∑ a, ∑ b,
        (hamiltonTestJetDU clock Ric
          (fun i j => if i = j then 1 else 0) W e a b) ^ 2) <=
      (2 * B ^ 2 + 1 / (2 * clock.elapsed ^ 2)) *
        (Fintype.card Idx : Real) ^ 2 *
        (∑ a, (W a) ^ 2) := by
  let S : Idx -> Idx -> Real := fun i j =>
    Ric i j + (1 / (2 * clock.elapsed)) * (if i = j then 1 else 0)
  let D := B + 1 / (2 * clock.elapsed)
  have hclock : 0 <= 1 / (2 * clock.elapsed) :=
    (one_div_pos.mpr (mul_pos (by norm_num) clock.elapsed_pos)).le
  have hD : 0 <= D := add_nonneg hB hclock
  have hS : forall i j, |S i j| <= D := by
    intro i j
    dsimp [S, D]
    calc
      |Ric i j + (1 / (2 * clock.elapsed)) * (if i = j then 1 else 0)| <=
          |Ric i j| + |(1 / (2 * clock.elapsed)) *
            (if i = j then 1 else 0)| := abs_add_le _ _
      _ <= B + 1 / (2 * clock.elapsed) := by
        exact add_le_add (hRic i j) (by
          by_cases hij : i = j
          · rw [if_pos hij, mul_one, abs_of_nonneg hclock]
          · rw [if_neg hij, mul_zero, abs_zero]
            exact hclock)
  have htri := hamiltonTriangularA_sq_sum_le S W D hD hS
  have hrewrite : forall e a b,
      hamiltonTestJetDU clock Ric
          (fun i j => if i = j then 1 else 0) W e a b =
        hamiltonTriangularA S W e a b := by
    intro e a b
    rw [hamiltonTestJetDU_eq_triangularA]
  simp_rw [hrewrite] at ⊢
  calc
    (∑ e, ∑ a, ∑ b, (hamiltonTriangularA S W e a b) ^ 2) <=
        D ^ 2 * (Fintype.card Idx : Real) ^ 2 *
          (∑ a, (W a) ^ 2) := htri
    _ <= (2 * B ^ 2 + 1 / (2 * clock.elapsed ^ 2)) *
        (Fintype.card Idx : Real) ^ 2 *
        (∑ a, (W a) ^ 2) := by
      have hsquares : 0 <= (Fintype.card Idx : Real) ^ 2 *
          (∑ a, (W a) ^ 2) :=
        mul_nonneg (sq_nonneg _)
          (Finset.sum_nonneg fun a _ => sq_nonneg _)
      have hDsq : D ^ 2 <= 2 * B ^ 2 + 1 / (2 * clock.elapsed ^ 2) := by
        have hx :
            2 * (1 / (2 * clock.elapsed)) ^ 2 =
              1 / (2 * clock.elapsed ^ 2) := by
          field_simp [HarnackClock.elapsed_ne_zero clock]
        dsimp [D]
        rw [← hx]
        nlinarith [sq_nonneg (B - 1 / (2 * clock.elapsed))]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hDsq hsquares

private def hamiltonTestUCoordinate
    [Fintype Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real)
    (p : Real × (Idx -> Real)) (b c : Idx) : Real :=
  U b c +
    (∑ a : Idx, p.2 a * hamiltonTestJetDU clock Ric h W a b c) +
    (1 / 2 : Real) * (∑ a : Idx, (p.2 a) ^ 2 * D2U a b c) +
    (p.1 - clock.time) * ∑ a : Idx, D2U a b c

private def hamiltonTestWCoordinate
    [Fintype Idx]
    (clock : HarnackClock) (W : Idx -> Real)
    (D2W : Idx -> Idx -> Real)
    (p : Real × (Idx -> Real)) (b : Idx) : Real :=
  W b + (1 / 2 : Real) * (∑ a : Idx, (p.2 a) ^ 2 * D2W a b) +
    (p.1 - clock.time) *
      ((∑ a : Idx, D2W a b) + (1 / clock.elapsed) * W b)

private theorem hamiltonTestUCoordinate_base
    [Fintype Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real) (b c : Idx) :
    hamiltonTestUCoordinate clock Ric h U W D2U
      (clock.time, 0) b c = U b c := by
  simp [hamiltonTestUCoordinate]

private theorem hamiltonTestWCoordinate_base
    [Fintype Idx]
    (clock : HarnackClock) (W : Idx -> Real)
    (D2W : Idx -> Idx -> Real) (b : Idx) :
    hamiltonTestWCoordinate clock W D2W (clock.time, 0) b = W b := by
  simp [hamiltonTestWCoordinate]

private theorem hamiltonTestUCoordinate_contDiff
    [Fintype Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real) :
    ContDiff Real (∞ : WithTop ℕ∞)
      (fun p => fun b c => hamiltonTestUCoordinate clock Ric h U W D2U p b c) := by
  rw [contDiff_pi]
  intro b
  rw [contDiff_pi]
  intro c
  unfold hamiltonTestUCoordinate
  fun_prop

private theorem hamiltonTestWCoordinate_contDiff
    [Fintype Idx]
    (clock : HarnackClock) (W : Idx -> Real)
    (D2W : Idx -> Idx -> Real) :
    ContDiff Real (∞ : WithTop ℕ∞)
      (fun p => fun b => hamiltonTestWCoordinate clock W D2W p b) := by
  rw [contDiff_pi]
  intro b
  unfold hamiltonTestWCoordinate
  fun_prop

private theorem hamiltonTestUCoordinate_spatial_formula
    [Fintype Idx] [DecidableEq Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real) (e b c : Idx) (r : Real) :
    hamiltonTestUCoordinate clock Ric h U W D2U
        (clock.time, fun a => if a = e then r else 0) b c =
      U b c + r * hamiltonTestJetDU clock Ric h W e b c +
        (1 / 2 : Real) * r ^ 2 * D2U e b c := by
  simp [hamiltonTestUCoordinate]
  ring

private theorem hamiltonTestWCoordinate_spatial_formula
    [Fintype Idx] [DecidableEq Idx]
    (clock : HarnackClock) (W : Idx -> Real)
    (D2W : Idx -> Idx -> Real) (e b : Idx) (r : Real) :
    hamiltonTestWCoordinate clock W D2W
        (clock.time, fun a => if a = e then r else 0) b =
      W b + (1 / 2 : Real) * r ^ 2 * D2W e b := by
  simp [hamiltonTestWCoordinate]
  ring

private theorem hamiltonTestUCoordinate_spatial_at
    [Fintype Idx] [DecidableEq Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real) (e b c : Idx) (r : Real) :
    HasDerivAt
      (fun s : Real => hamiltonTestUCoordinate clock Ric h U W D2U
        (clock.time, fun a => if a = e then s else 0) b c)
      (hamiltonTestJetDU clock Ric h W e b c + r * D2U e b c) r := by
  have hfun :
      (fun s : Real => hamiltonTestUCoordinate clock Ric h U W D2U
        (clock.time, fun a => if a = e then s else 0) b c) =
      fun s : Real => U b c + s * hamiltonTestJetDU clock Ric h W e b c +
        (1 / 2 : Real) * s ^ 2 * D2U e b c := by
    funext s
    exact hamiltonTestUCoordinate_spatial_formula clock Ric h U W D2U e b c s
  rw [hfun]
  have hid : HasDerivAt (fun s : Real => s) 1 r := hasDerivAt_id r
  have hlin := hid.mul_const (hamiltonTestJetDU clock Ric h W e b c)
  have hquad : HasDerivAt
      (fun s : Real => (1 / 2 : Real) * s ^ 2 * D2U e b c)
      (r * D2U e b c) r := by
    have hraw := (hid.mul hid).const_mul (1 / 2 : Real) |>.mul_const (D2U e b c)
    have hraw' : HasDerivAt
        (fun s : Real => (1 / 2 : Real) * s ^ 2 * D2U e b c)
        ((1 / 2 : Real) * (1 * r + r * 1) * D2U e b c) r :=
      hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
        simp [Pi.mul_apply, pow_two])
    convert hraw' using 1
    ring
  simpa [Pi.add_apply, add_assoc] using
    (hlin.add hquad).const_add (U b c)

private theorem hamiltonTestUCoordinate_spatial
    [Fintype Idx] [DecidableEq Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real) (e b c : Idx) :
    HasDerivAt
      (fun r : Real => hamiltonTestUCoordinate clock Ric h U W D2U
        (clock.time, fun a => if a = e then r else 0) b c)
      (hamiltonTestJetDU clock Ric h W e b c) 0 := by
  simpa using hamiltonTestUCoordinate_spatial_at clock Ric h U W D2U e b c 0

private theorem hamiltonTestWCoordinate_spatial_at
    [Fintype Idx] [DecidableEq Idx]
    (clock : HarnackClock) (W : Idx -> Real)
    (D2W : Idx -> Idx -> Real) (e b : Idx) (r : Real) :
    HasDerivAt
      (fun s : Real => hamiltonTestWCoordinate clock W D2W
        (clock.time, fun a => if a = e then s else 0) b)
      (r * D2W e b) r := by
  have hfun :
      (fun s : Real => hamiltonTestWCoordinate clock W D2W
        (clock.time, fun a => if a = e then s else 0) b) =
      fun s : Real => W b + (1 / 2 : Real) * s ^ 2 * D2W e b := by
    funext s
    exact hamiltonTestWCoordinate_spatial_formula clock W D2W e b s
  rw [hfun]
  have hid : HasDerivAt (fun s : Real => s) 1 r := hasDerivAt_id r
  have hquad : HasDerivAt
      (fun s : Real => (1 / 2 : Real) * s ^ 2 * D2W e b)
      (r * D2W e b) r := by
    have hraw := (hid.mul hid).const_mul (1 / 2 : Real) |>.mul_const (D2W e b)
    have hraw' : HasDerivAt
        (fun s : Real => (1 / 2 : Real) * s ^ 2 * D2W e b)
        ((1 / 2 : Real) * (1 * r + r * 1) * D2W e b) r :=
      hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
        simp [Pi.mul_apply, pow_two])
    convert hraw' using 1
    ring
  exact hquad.const_add (W b)

private theorem hamiltonTestWCoordinate_spatial
    [Fintype Idx] [DecidableEq Idx]
    (clock : HarnackClock) (W : Idx -> Real)
    (D2W : Idx -> Idx -> Real) (e b : Idx) :
    HasDerivAt
      (fun r : Real => hamiltonTestWCoordinate clock W D2W
        (clock.time, fun a => if a = e then r else 0) b) 0 0 := by
  simpa using hamiltonTestWCoordinate_spatial_at clock W D2W e b 0

private theorem hamiltonTestUCoordinate_spatialSecond
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real) (e b c : Idx) (r : Real) :
    HasDerivAt
      (fun s : Real => hamiltonTestJetDU clock Ric h W e b c + s * D2U e b c)
      (D2U e b c) r := by
  simpa using (hasDerivAt_id r).mul_const (D2U e b c) |>.const_add
    (hamiltonTestJetDU clock Ric h W e b c)

private theorem hamiltonTestWCoordinate_spatialSecond
    (D2W : Idx -> Idx -> Real) (e b : Idx) (r : Real) :
    HasDerivAt (fun s : Real => s * D2W e b) (D2W e b) r := by
  simpa using (hasDerivAt_id r).mul_const (D2W e b)

private theorem hamiltonTestUCoordinate_time
    [Fintype Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real) (b c : Idx) :
    HasDerivAt
      (fun s : Real => hamiltonTestUCoordinate clock Ric h U W D2U (s, 0) b c)
      (∑ a : Idx, D2U a b c) clock.time := by
  have hid : HasDerivAt (fun s : Real => s) 1 clock.time :=
    hasDerivAt_id clock.time
  have hmul := (hid.sub_const clock.time).mul_const (∑ a : Idx, D2U a b c)
  have hderiv := hmul.const_add (U b c)
  simpa only [one_mul] using hderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by simp [hamiltonTestUCoordinate])

private theorem hamiltonTestWCoordinate_time
    [Fintype Idx]
    (clock : HarnackClock) (W : Idx -> Real)
    (D2W : Idx -> Idx -> Real) (b : Idx) :
    HasDerivAt
      (fun s : Real => hamiltonTestWCoordinate clock W D2W (s, 0) b)
      ((∑ a : Idx, D2W a b) + (1 / clock.elapsed) * W b) clock.time := by
  have hid : HasDerivAt (fun s : Real => s) 1 clock.time :=
    hasDerivAt_id clock.time
  have hmul := (hid.sub_const clock.time).mul_const
    ((∑ a : Idx, D2W a b) + (1 / clock.elapsed) * W b)
  have hderiv := hmul.const_add (W b)
  simpa only [one_mul] using hderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by simp [hamiltonTestWCoordinate])

private def hamiltonTestUCoordinateHeat
    [Fintype Idx]
    (dtU : Idx -> Idx -> Real) (D2U : Idx -> Idx -> Idx -> Real)
    (b c : Idx) : Real :=
  dtU b c - ∑ a : Idx, D2U a b c

private def hamiltonTestWCoordinateHeat
    [Fintype Idx]
    (dtW : Idx -> Real) (D2W : Idx -> Idx -> Real) (b : Idx) : Real :=
  dtW b - ∑ a : Idx, D2W a b

private theorem hamiltonTestUCoordinate_heat
    [Fintype Idx] (D2U : Idx -> Idx -> Idx -> Real) (b c : Idx) :
    hamiltonTestUCoordinateHeat (fun i j => ∑ a : Idx, D2U a i j) D2U b c = 0 := by
  simp [hamiltonTestUCoordinateHeat]

private theorem hamiltonTestWCoordinate_heat
    [Fintype Idx] (clock : HarnackClock) (W : Idx -> Real)
    (D2W : Idx -> Idx -> Real) (b : Idx) :
    hamiltonTestWCoordinateHeat
        (fun i => (∑ a : Idx, D2W a i) + (1 / clock.elapsed) * W i) D2W b =
      (1 / clock.elapsed) * W b := by
  simp [hamiltonTestWCoordinateHeat]

private theorem hamiltonTestUCoordinate_skew
    [Fintype Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real)
    (hU : ∀ b c, U b c = -U c b)
    (hD2U : ∀ a b c, D2U a b c = -D2U a c b)
    (p : Real × (Idx -> Real)) (b c : Idx) :
    hamiltonTestUCoordinate clock Ric h U W D2U p b c =
      -hamiltonTestUCoordinate clock Ric h U W D2U p c b := by
  unfold hamiltonTestUCoordinate
  have hsum :
      (∑ a : Idx, p.2 a * hamiltonTestJetDU clock Ric h W a b c) =
        -∑ a : Idx, p.2 a * hamiltonTestJetDU clock Ric h W a c b := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hamiltonTestJetDU_skew clock Ric h W a b c]
    ring
  have hsum2 :
      (∑ a : Idx, (p.2 a) ^ 2 * D2U a b c) =
        -∑ a : Idx, (p.2 a) ^ 2 * D2U a c b := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hD2U]
    ring
  have htrace :
      (∑ a : Idx, D2U a b c) = -∑ a : Idx, D2U a c b := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => hD2U a b c
  rw [hU, hsum, hsum2, htrace]
  ring

private theorem hamilton_coordinate_test_jet_realization_with_spatial_second
    [Fintype Idx] [DecidableEq Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (D2U : Idx -> Idx -> Idx -> Real) (D2W : Idx -> Idx -> Real)
    (hU : ∀ b c, U b c = -U c b)
    (hD2U : ∀ a b c, D2U a b c = -D2U a c b) :
    ∃ (u : Real × (Idx -> Real) -> Idx -> Idx -> Real)
      (w : Real × (Idx -> Real) -> Idx -> Real),
      ContDiff Real (∞ : WithTop ℕ∞) (fun p => fun b c => u p b c) ∧
      ContDiff Real (∞ : WithTop ℕ∞) (fun p => fun b => w p b) ∧
      (∀ b c, u (clock.time, 0) b c = U b c) ∧
      (∀ b, w (clock.time, 0) b = W b) ∧
      (∀ e b c,
        HasDerivAt
          (fun r : Real => u (clock.time, fun a => if a = e then r else 0) b c)
          (hamiltonTestJetDU clock Ric h W e b c) 0) ∧
      (∀ e b,
        HasDerivAt
          (fun r : Real => w (clock.time, fun a => if a = e then r else 0) b) 0 0) ∧
      (∀ e b c r,
        HasDerivAt
          (fun s : Real => u (clock.time, fun a => if a = e then s else 0) b c)
          (hamiltonTestJetDU clock Ric h W e b c + r * D2U e b c) r) ∧
      (∀ e b r,
        HasDerivAt
          (fun s : Real => w (clock.time, fun a => if a = e then s else 0) b)
          (r * D2W e b) r) ∧
      (∀ e b c r,
        HasDerivAt
          (fun s : Real => hamiltonTestJetDU clock Ric h W e b c + s * D2U e b c)
          (D2U e b c) r) ∧
      (∀ e b r,
        HasDerivAt (fun s : Real => s * D2W e b) (D2W e b) r) ∧
      (∀ b c,
        HasDerivAt
          (fun s : Real => u (s, 0) b c) (∑ a : Idx, D2U a b c) clock.time) ∧
      (∀ b,
        HasDerivAt
          (fun s : Real => w (s, 0) b)
          ((∑ a : Idx, D2W a b) + (1 / clock.elapsed) * W b) clock.time) ∧
      (∀ b c,
        hamiltonTestUCoordinateHeat (fun i j => ∑ a : Idx, D2U a i j) D2U b c = 0) ∧
      (∀ b,
        hamiltonTestWCoordinateHeat
            (fun i => (∑ a : Idx, D2W a i) + (1 / clock.elapsed) * W i) D2W b =
          (1 / clock.elapsed) * W b) ∧
      (∀ p b c, u p b c = -u p c b) ∧
      (∀ a b c,
        hamiltonTriangularConnectionU
          (fun i j => Ric i j + (1 / (2 * clock.elapsed) : Real) * h i j)
          W (hamiltonTestJetDU clock Ric h W) a b c = 0) ∧
      (∀ a b, hamiltonTriangularConnectionW (Idx := Idx)
        (fun _ _ : Idx => (0 : Real)) a b = 0) := by
  refine ⟨hamiltonTestUCoordinate clock Ric h U W D2U,
    hamiltonTestWCoordinate clock W D2W, ?_⟩
  refine ⟨hamiltonTestUCoordinate_contDiff clock Ric h U W D2U,
    hamiltonTestWCoordinate_contDiff clock W D2W, ?_⟩
  refine ⟨fun b c => hamiltonTestUCoordinate_base clock Ric h U W D2U b c, ?_⟩
  refine ⟨fun b => hamiltonTestWCoordinate_base clock W D2W b, ?_⟩
  refine ⟨fun e b c => hamiltonTestUCoordinate_spatial clock Ric h U W D2U e b c, ?_⟩
  refine ⟨fun e b => hamiltonTestWCoordinate_spatial clock W D2W e b, ?_⟩
  refine ⟨fun e b c r => hamiltonTestUCoordinate_spatial_at
    clock Ric h U W D2U e b c r, ?_⟩
  refine ⟨fun e b r => hamiltonTestWCoordinate_spatial_at clock W D2W e b r, ?_⟩
  refine ⟨fun e b c r => hamiltonTestUCoordinate_spatialSecond
    clock Ric h W D2U e b c r, ?_⟩
  refine ⟨fun e b r => hamiltonTestWCoordinate_spatialSecond D2W e b r, ?_⟩
  refine ⟨fun b c => hamiltonTestUCoordinate_time clock Ric h U W D2U b c, ?_⟩
  refine ⟨fun b => hamiltonTestWCoordinate_time clock W D2W b, ?_⟩
  refine ⟨fun b c => hamiltonTestUCoordinate_heat D2U b c, ?_⟩
  refine ⟨fun b => hamiltonTestWCoordinate_heat clock W D2W b, ?_⟩
  refine ⟨fun p b c => hamiltonTestUCoordinate_skew
    clock Ric h U W D2U hU hD2U p b c, ?_⟩
  refine ⟨fun a b c => hamiltonTriangularConnectionU_zero_of_testJet
    clock Ric h W a b c, ?_⟩
  exact fun a b => hamiltonTriangularConnectionW_zero_of_testJet
    (Idx := Idx) (fun _ _ : Idx => (0 : Real)) a b rfl

private theorem hamilton_coordinate_test_jet_realization
    [Fintype Idx] [DecidableEq Idx]
    (clock : HarnackClock)
    (Ric h U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hU : ∀ b c, U b c = -U c b) :
    ∃ (u : Real × (Idx -> Real) -> Idx -> Idx -> Real)
      (w : Real × (Idx -> Real) -> Idx -> Real),
      ContDiff Real (∞ : WithTop ℕ∞) (fun p => fun b c => u p b c) ∧
      ContDiff Real (∞ : WithTop ℕ∞) (fun p => fun b => w p b) ∧
      (∀ b c, u (clock.time, 0) b c = U b c) ∧
      (∀ b, w (clock.time, 0) b = W b) ∧
      (∀ e b c,
        HasDerivAt
          (fun r : Real => u (clock.time, fun a => if a = e then r else 0) b c)
          (hamiltonTestJetDU clock Ric h W e b c) 0) ∧
      (∀ e b,
        HasDerivAt
          (fun r : Real => w (clock.time, fun a => if a = e then r else 0) b) 0 0) ∧
      (∀ e b c r,
        HasDerivAt
          (fun s : Real => u (clock.time, fun a => if a = e then s else 0) b c)
          (hamiltonTestJetDU clock Ric h W e b c) r) ∧
      (∀ e b r,
        HasDerivAt
          (fun s : Real => w (clock.time, fun a => if a = e then s else 0) b) 0 r) ∧
      (∀ e b c r,
        HasDerivAt (fun _ : Real => hamiltonTestJetDU clock Ric h W e b c) 0 r) ∧
      (∀ (_ _ : Idx) (r : Real), HasDerivAt (fun _ : Real => (0 : Real)) 0 r) ∧
      (∀ b c, HasDerivAt (fun s : Real => u (s, 0) b c) 0 clock.time) ∧
      (∀ b,
        HasDerivAt
          (fun s : Real => w (s, 0) b)
          ((1 / clock.elapsed) * W b) clock.time) ∧
      (∀ b c,
        hamiltonTestUCoordinateHeat (fun _ _ : Idx => 0)
          (fun _ _ _ : Idx => 0) b c = 0) ∧
      (∀ b,
        hamiltonTestWCoordinateHeat (fun i => (1 / clock.elapsed) * W i)
            (fun _ _ : Idx => 0) b =
          (1 / clock.elapsed) * W b) ∧
      (∀ p b c, u p b c = -u p c b) ∧
      (∀ a b c,
        hamiltonTriangularConnectionU
          (fun i j => Ric i j + (1 / (2 * clock.elapsed) : Real) * h i j)
          W (hamiltonTestJetDU clock Ric h W) a b c = 0) ∧
      (∀ a b, hamiltonTriangularConnectionW (Idx := Idx)
        (fun _ _ : Idx => (0 : Real)) a b = 0) := by
  simpa using hamilton_coordinate_test_jet_realization_with_spatial_second
    clock Ric h U W (fun _ _ _ => 0) (fun _ _ => 0) hU
      (fun _ _ _ => by simp)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem hamilton_carrier_coordinate_test_jet_realization
    [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (clock : HarnackClock)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric h : Tensor0SBundle.Tensor0SSpace 2 I x)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : StrongDual Real (TangentSpace I x)) :
    let RicCoord : Idx → Idx → Real := fun a b =>
      Tensor0SBundle.component0S (I := I) basis Ric ![a, b]
    let hCoord : Idx → Idx → Real := fun a b =>
      Tensor0SBundle.component0S (I := I) basis h ![a, b]
    let UCoord : Idx → Idx → Real := fun a b =>
      HamiltonHarnackTwoForm.component (I := I) basis U a b
    let WCoord : Idx → Real := fun a => W (basis a)
    ∃ (u : Real × (Idx → Real) → Idx → Idx → Real)
      (w : Real × (Idx → Real) → Idx → Real),
      ContDiff Real (∞ : WithTop ℕ∞) (fun p => fun b c => u p b c) ∧
      ContDiff Real (∞ : WithTop ℕ∞) (fun p => fun b => w p b) ∧
      (∀ b c, u (clock.time, 0) b c = UCoord b c) ∧
      (∀ b, w (clock.time, 0) b = WCoord b) ∧
      (∀ e b c,
        HasDerivAt
          (fun r : Real => u (clock.time, fun a => if a = e then r else 0) b c)
          (hamiltonTestJetDU clock RicCoord hCoord WCoord e b c) 0) ∧
      (∀ e b,
        HasDerivAt
          (fun r : Real => w (clock.time, fun a => if a = e then r else 0) b) 0 0) ∧
      (∀ e b c r,
        HasDerivAt
          (fun s : Real => u (clock.time, fun a => if a = e then s else 0) b c)
          (hamiltonTestJetDU clock RicCoord hCoord WCoord e b c) r) ∧
      (∀ e b r,
        HasDerivAt
          (fun s : Real => w (clock.time, fun a => if a = e then s else 0) b) 0 r) ∧
      (∀ e b c r,
        HasDerivAt
          (fun _ : Real => hamiltonTestJetDU clock RicCoord hCoord WCoord e b c) 0 r) ∧
      (∀ (_ _ : Idx) (r : Real), HasDerivAt (fun _ : Real => (0 : Real)) 0 r) ∧
      (∀ b c, HasDerivAt (fun s : Real => u (s, 0) b c) 0 clock.time) ∧
      (∀ b,
        HasDerivAt
          (fun s : Real => w (s, 0) b)
          ((1 / clock.elapsed) * WCoord b) clock.time) ∧
      (∀ b c,
        hamiltonTestUCoordinateHeat (fun _ _ : Idx => 0)
          (fun _ _ _ : Idx => 0) b c = 0) ∧
      (∀ b,
        hamiltonTestWCoordinateHeat (fun i => (1 / clock.elapsed) * WCoord i)
            (fun _ _ : Idx => 0) b =
          (1 / clock.elapsed) * WCoord b) ∧
      (∀ p b c, u p b c = -u p c b) ∧
      (∀ a b c,
        hamiltonTriangularConnectionU
          (fun i j => RicCoord i j + (1 / (2 * clock.elapsed) : Real) * hCoord i j)
          WCoord (hamiltonTestJetDU clock RicCoord hCoord WCoord) a b c = 0) ∧
      (∀ a b, hamiltonTriangularConnectionW (Idx := Idx)
        (fun _ _ : Idx => (0 : Real)) a b = 0) := by
  dsimp only
  exact hamilton_coordinate_test_jet_realization clock
    (fun a b => Tensor0SBundle.component0S (I := I) basis Ric ![a, b])
    (fun a b => Tensor0SBundle.component0S (I := I) basis h ![a, b])
    (fun a b => HamiltonHarnackTwoForm.component (I := I) basis U a b)
    (fun a => W (basis a))
    (HamiltonHarnackTwoForm.component_skew (I := I) basis U)

variable [FiniteDimensional Real E] [T2Space M]

private def metricDualField
    (g : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1 :=
  partialEval0SField (I := I) (metricTensorField (I := I) g) Y

omit [T2Space M] in
private theorem metricDualField_apply
    (g : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (y : M) (Z : TangentSpace I y) :
    metricDualField (I := I) g Y y (fun _ : Fin 1 => Z) =
      g.inner y (Y y) Z := by
  rw [metricDualField, partialEval0SField_apply, tensor0S_curry_apply_cons,
    metricTensorField_apply]
  simp only [Fin.cons_zero]
  rfl

private theorem metricDualField_totalNabla_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible (I := I) cov g)
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (X Z : TangentSpace I x) :
    totalNabla0SFun (I := I) (M := M) 1 cov
        (metricDualField (I := I) g Y) x ![X, Z] =
      g.inner x ((cov (fun y : M => Y y) x) X) Z := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨Xsec, hXsec⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have htotal := totalNabla0SFun_apply_section (I := I) 1 cov Xsec
    (metricDualField (I := I) g Y) x (fun _ : Fin 1 => Z)
  have hnabla := nabla_partialEval0S (I := I) cov
    (metricTensorField (I := I) g)
    (0 : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 3)
    (zero_realizes_metric (I := I) cov g hmc) Xsec Y x
  rw [metricDualField] at htotal
  have hslots : ![X, Z] = Fin.cons (Xsec x) (fun _ : Fin 1 => Z) := by
    funext i
    fin_cases i <;> simp [hXsec]
  rw [metricDualField]
  rw [hslots, htotal, hnabla, hXsec]
  rw [Tensor0SSpace.add_apply, freezeFirstTwoArgs0S_apply]
  rw [tensor0S_curry_apply_cons, metricTensorField_apply]
  change (0 : Real) + g.inner x ((cov (fun y : M => Y y) x) X) Z = _
  exact zero_add _

private def raiseFirstTensorSlot
    (g : SmoothRiemannianMetric I M) {x : M}
    (S : Tensor0SSpace (I := I) 2 x) :
    TangentSpace I x →L[Real] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    ((cotangentSharpLinear (I := I) g x).comp
      ((tensor0SCurry (I := I) (M := M) 1 x) S).toLinearMap)

omit [T2Space M] in
private theorem raiseFirstTensorSlot_pairing
    (g : SmoothRiemannianMetric I M) {x : M}
    (S : Tensor0SSpace (I := I) 2 x)
    (X Z : TangentSpace I x) :
    g.inner x (raiseFirstTensorSlot (I := I) g S X) Z = S ![X, Z] := by
  rw [raiseFirstTensorSlot, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    cotangentSharpLinear_apply, cotangentSharp_inner_eval]
  have h := tensor0S_curry_apply_cons (I := I) 1 S X (fun _ : Fin 1 => Z)
  have hslots : Fin.cons X (fun _ : Fin 1 => Z) = ![X, Z] := by
    funext i
    fin_cases i <;> rfl
  rw [hslots] at h
  exact h

private theorem exists_one_form_tensor_first_covariant_derivative_eq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible (I := I) cov g)
    (x : M) (S : Tensor0SSpace (I := I) 2 x) :
    ∃ A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1,
      A x = 0 ∧ totalNabla0SFun (I := I) (M := M) 1 cov A x = S := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨Y, hY, hDY⟩ := exists_cov_eq_at (I := I) cov x 0
    (raiseFirstTensorSlot (I := I) g S)
  refine ⟨metricDualField (I := I) g Y, ?_, ?_⟩
  · apply tensor0SSpace_ext (I := I) 1 x
    intro v
    have hv : v = fun _ : Fin 1 => v 0 := by
      funext i
      fin_cases i
      rfl
    rw [hv, metricDualField_apply, hY, Tensor0SSpace.zero_apply]
    simp
  · apply tensor0SSpace_ext (I := I) 2 x
    intro v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, metricDualField_totalNabla_apply (I := I) cov g hmc Y x, hDY,
      raiseFirstTensorSlot_pairing (I := I)]

private theorem exists_parallel_one_form_tensor
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible (I := I) cov g)
    (x : M) (alpha : StrongDual Real (TangentSpace I x)) :
    ∃ A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1,
      (∀ Z : TangentSpace I x, A x (fun _ : Fin 1 => Z) = alpha Z) ∧
      totalNabla0SFun (I := I) (M := M) 1 cov A x = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨Y, hY, hDY⟩ := exists_cov_zero_at (I := I) cov x
    (Geometry.Operator.metricSharp (I := I) g x alpha)
  refine ⟨metricDualField (I := I) g Y, ?_, ?_⟩
  · intro Z
    rw [metricDualField_apply, hY]
    exact Geometry.Operator.inner_metricSharp (I := I) g x alpha Z
  · apply tensor0SSpace_ext (I := I) 2 x
    intro v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, metricDualField_totalNabla_apply (I := I) cov g hmc Y x, hDY]
    change g.inner x 0 (v 1) = 0
    simp

private def normalizedWedgeTensorField
    (A B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  (1 / 2 : Real) •
    (tensor0SFieldProduct ∞ A B -
      Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 2) 1)
        (tensor0SFieldProduct ∞ A B))

omit [T2Space M] in
private theorem normalizedWedgeTensorField_apply
    (A B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (y : M) (X Y : TangentSpace I y) :
    normalizedWedgeTensorField (I := I) A B y ![X, Y] =
      (1 / 2 : Real) *
        (A y (fun _ : Fin 1 => X) * B y (fun _ : Fin 1 => Y) -
          A y (fun _ : Fin 1 => Y) * B y (fun _ : Fin 1 => X)) := by
  rw [normalizedWedgeTensorField]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.smul_apply,
    Tensor0SSpace.sub_apply, smul_eq_mul]
  rw [tensor0SField_product_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply]
  have hAX : ![X, Y] ∘ Fin.castAdd 1 = fun _ : Fin 1 => X := by
    funext i
    fin_cases i
    rfl
  have hBY : ![X, Y] ∘ Fin.natAdd 1 = fun _ : Fin 1 => Y := by
    funext i
    fin_cases i
    rfl
  have hAY : (fun i => ![X, Y] ((Equiv.swap 0 1) i)) ∘ Fin.castAdd 1 =
      fun _ : Fin 1 => Y := by
    funext i
    fin_cases i
    rfl
  have hBX : (fun i => ![X, Y] ((Equiv.swap 0 1) i)) ∘ Fin.natAdd 1 =
      fun _ : Fin 1 => X := by
    funext i
    fin_cases i
    rfl
  rw [hAX, hBY, hAY, hBX]

omit [T2Space M] in
private theorem normalizedWedgeTensorField_skew
    (A B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (y : M) (X Y : TangentSpace I y) :
    normalizedWedgeTensorField (I := I) A B y ![X, Y] =
      -normalizedWedgeTensorField (I := I) A B y ![Y, X] := by
  rw [normalizedWedgeTensorField_apply, normalizedWedgeTensorField_apply]
  ring

private theorem totalNabla0SFun_product_one_one_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (A B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (x : M) (X Y Z : TangentSpace I x) :
    totalNabla0SFun (I := I) (M := M) 2 cov
        (tensor0SFieldProduct ∞ A B) x ![X, Y, Z] =
      totalNabla0SFun (I := I) (M := M) 1 cov A x ![X, Y] *
          B x (fun _ : Fin 1 => Z) +
        A x (fun _ : Fin 1 => Y) *
          totalNabla0SFun (I := I) (M := M) 1 cov B x ![X, Z] := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let hregA := totalNabla0S_regularity (I := I) 1 cov hcov A
  let hregB := totalNabla0S_regularity (I := I) 1 cov hcov B
  let nablaA := totalNabla0S (I := I) 1 cov A hregA
  let nablaB := totalNabla0S (I := I) 1 cov B hregB
  have hA := totalNabla0S_realizes (I := I) 1 cov A hregA
  have hB := totalNabla0S_realizes (I := I) 1 cov B hregB
  obtain ⟨Xsec, hXsec⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYsec⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  obtain ⟨Zsec, hZsec⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Z
  let Vsec : Fin 2 → ContMDiffSection I E ∞ (TangentSpace I) :=
    ![Ysec, Zsec]
  have hprod := nabla0SFun_product_eval (I := I) cov A B
    nablaA nablaB hA hB Xsec Vsec x
  rw [← totalNabla0SFun_apply_section (I := I) 2 cov Xsec
    (tensor0SFieldProduct ∞ A B) x] at hprod
  simp only [nablaA, nablaB, totalNabla0S_apply] at hprod
  have hleft :
      (fun a : Fin 1 => Vsec (Fin.castAdd 1 a) x) =
        fun _ : Fin 1 => Y := by
    funext i
    fin_cases i
    simp [Vsec, hYsec]
  have hright :
      (fun a : Fin 1 => Vsec (Fin.natAdd 1 a) x) =
        fun _ : Fin 1 => Z := by
    funext i
    fin_cases i
    simp [Vsec, hZsec]
  have hslots :
      Fin.cons (Xsec x) (fun i : Fin 2 => Vsec i x) =
        ![X, Y, Z] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hXsec
    · fin_cases j
      · exact hYsec
      · exact hZsec
  rw [hslots, hleft, hright] at hprod
  have hAX : Fin.cons (Xsec x) (fun _ : Fin 1 => Y) = ![X, Y] := by
    funext i
    fin_cases i <;> simp [hXsec]
  have hAZ : Fin.cons (Xsec x) (fun _ : Fin 1 => Z) = ![X, Z] := by
    funext i
    fin_cases i <;> simp [hXsec]
  rw [hAX, hAZ] at hprod
  exact hprod

private theorem normalizedWedgeTensorField_totalNabla_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (A B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (x : M)
    (hA : totalNabla0SFun (I := I) (M := M) 1 cov A x = 0)
    (hB : totalNabla0SFun (I := I) (M := M) 1 cov B x = 0) :
    totalNabla0SFun (I := I) (M := M) 2 cov
      (normalizedWedgeTensorField (I := I) A B) x = 0 := by
  apply tensor0SSpace_ext (I := I) 3 x
  intro v
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, normalizedWedgeTensorField]
  rw [totalNabla0SFun_smul, sub_eq_add_neg,
    show -Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 2) 1)
        (tensor0SFieldProduct ∞ A B) =
      (-1 : Real) • Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 2) 1)
        (tensor0SFieldProduct ∞ A B) by simp,
    totalNabla0SFun_add, totalNabla0SFun_smul]
  rw [Tensor0SSpace.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply]
  rw [totalNabla0SFun_product_one_one_apply (I := I) cov hcov A B]
  rw [totalNabla0SFun_domDomCongr, Tensor0SSpace.domDomCongr_apply]
  have hperm :
      (fun i => ![v 0, v 1, v 2]
        (frontExtendEquiv (Equiv.swap (0 : Fin 2) 1) i)) =
      ![v 0, v 2, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hperm]
  rw [totalNabla0SFun_product_one_one_apply (I := I) cov hcov A B]
  simp only [hA, hB, Tensor0SSpace.zero_apply, zero_mul, mul_zero, add_zero,
    smul_zero]

private theorem normalizedWedgeTensorField_totalNabla_of_first_eq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (A B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (x : M) (S : Tensor0SSpace (I := I) 2 x)
    (hA : A x = 0)
    (hDA : totalNabla0SFun (I := I) (M := M) 1 cov A x = S)
    (hDB : totalNabla0SFun (I := I) (M := M) 1 cov B x = 0)
    (X Y Z : TangentSpace I x) :
    totalNabla0SFun (I := I) (M := M) 2 cov
        (normalizedWedgeTensorField (I := I) A B) x ![X, Y, Z] =
      (1 / 2 : Real) *
        (S ![X, Y] * B x (fun _ : Fin 1 => Z) -
          S ![X, Z] * B x (fun _ : Fin 1 => Y)) := by
  rw [normalizedWedgeTensorField]
  rw [totalNabla0SFun_smul, sub_eq_add_neg,
    show -Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 2) 1)
        (tensor0SFieldProduct ∞ A B) =
      (-1 : Real) • Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 2) 1)
        (tensor0SFieldProduct ∞ A B) by simp,
    totalNabla0SFun_add, totalNabla0SFun_smul]
  rw [Tensor0SSpace.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply]
  rw [totalNabla0SFun_product_one_one_apply (I := I) cov hcov A B]
  rw [totalNabla0SFun_domDomCongr, Tensor0SSpace.domDomCongr_apply]
  have hperm :
      (fun i => ![X, Y, Z]
        (frontExtendEquiv (Equiv.swap (0 : Fin 2) 1) i)) =
      ![X, Z, Y] := by
    funext i
    fin_cases i <;> rfl
  rw [hperm]
  rw [totalNabla0SFun_product_one_one_apply (I := I) cov hcov A B]
  simp only [hA, hDA, hDB, Tensor0SSpace.zero_apply, zero_mul, add_zero,
    smul_eq_mul]
  ring

private theorem totalNabla0SFun_zero
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) :
    totalNabla0SFun (I := I) (M := M) s cov
      (0 : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s) x = 0 := by
  let A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s := 0
  have h := totalNabla0SFun_smul (I := I) cov (0 : Real) A x
  simpa [A] using h

private theorem totalNabla0SFun_finset_sum
    {ι : Type*} {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (S : Finset ι)
    (A : ι → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s) :
    totalNabla0SFun (I := I) (M := M) s cov (∑ i ∈ S, A i) x =
      ∑ i ∈ S, totalNabla0SFun (I := I) (M := M) s cov (A i) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [totalNabla0SFun_zero (I := I) cov x]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        totalNabla0SFun_add, ih]

omit [T2Space M] in
private theorem tensor0SField_sum_apply
    {ι : Type*} [Fintype ι] {s : ℕ}
    (A : ι → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s)
    (x : M) (v : Fin s → TangentSpace I x) :
    (∑ i : ι, A i) x v = ∑ i : ι, A i x v := by
  classical
  rw [ContMDiffSection.finset_sum_apply]
  exact tensor0S_sum_apply (I := I) (fun i => A i x) v

omit [T2Space M] in
private theorem tensor0SField_smul_apply
    {s : ℕ} (c : Real)
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s)
    (x : M) (v : Fin s → TangentSpace I x) :
    (c • A) x v = c * A x v := by
  rw [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply]
  rfl

private theorem exists_parallel_two_form_tensor
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible (I := I) cov g)
    (x : M) (U₀ : HamiltonHarnackTwoForm (TangentSpace I x)) :
    ∃ U : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2,
      U x = U₀.toTensor0S ∧
      totalNabla0SFun (I := I) (M := M) 2 cov U x = 0 ∧
      ∀ y : M, ∀ X Y : TangentSpace I y,
        U y ![X, Y] = -U y ![Y, X] := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let d := Module.finrank Real (TangentSpace I x)
  let basis : Module.Basis (Fin d) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  let dual : Fin d → StrongDual Real (TangentSpace I x) :=
    fun i => (basis.coord i).toContinuousLinearMap
  choose A hAvalue hAnabla using fun i : Fin d =>
    exists_parallel_one_form_tensor (I := I) cov g hmc x (dual i)
  let U : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
    ∑ i : Fin d, ∑ j : Fin d,
      (U₀ ![basis i, basis j]) • normalizedWedgeTensorField (I := I) (A i) (A j)
  refine ⟨U, ?_, ?_, ?_⟩
  · apply ext0S_basis (I := I) basis
    intro slots
    simp only [U, component0S_apply,
      HamiltonHarnackTwoForm.toTensor0S_apply]
    have hslotvec : (fun a => basis (slots a)) =
        ![basis (slots 0), basis (slots 1)] := by
      funext a
      fin_cases a <;> rfl
    rw [hslotvec]
    rw [tensor0SField_sum_apply (I := I)]
    have hinner (i : Fin d) :
        ((∑ j : Fin d,
            (U₀ ![basis i, basis j]) •
              normalizedWedgeTensorField (I := I) (A i) (A j)) x)
            ![basis (slots 0), basis (slots 1)] =
          ∑ j : Fin d,
            ((U₀ ![basis i, basis j]) •
              normalizedWedgeTensorField (I := I) (A i) (A j)) x
                ![basis (slots 0), basis (slots 1)] :=
      tensor0SField_sum_apply (I := I) _ x _
    simp_rw [hinner, tensor0SField_smul_apply (I := I),
      normalizedWedgeTensorField_apply (I := I), hAvalue]
    simp only [dual, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    simp only [Module.Basis.repr_self_apply]
    classical
    ring_nf
    simp only [mul_boole, ite_mul, zero_mul, Finset.sum_add_distrib]
    simp only [Fintype.sum_ite_eq]
    have hskew := U₀.map_swap (v := ![basis (slots 0), basis (slots 1)])
      (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
    have hslots :
        ![basis (slots 0), basis (slots 1)] ∘ (Equiv.swap (0 : Fin 2) 1) =
          ![basis (slots 1), basis (slots 0)] := by
      funext i
      fin_cases i <;> rfl
    rw [hslots] at hskew
    change
      U₀.toAlternatingMap ![basis (slots 0), basis (slots 1)] * (1 / 2) +
          U₀.toAlternatingMap ![basis (slots 1), basis (slots 0)] * (-1 / 2) =
        U₀.toAlternatingMap ![basis (slots 0), basis (slots 1)]
    rw [hskew]
    ring
  · simp only [U]
    rw [totalNabla0SFun_finset_sum (I := I)]
    apply Finset.sum_eq_zero
    intro i _
    rw [totalNabla0SFun_finset_sum (I := I)]
    apply Finset.sum_eq_zero
    intro j _
    rw [totalNabla0SFun_smul]
    rw [normalizedWedgeTensorField_totalNabla_zero
      (I := I) cov hcov (A i) (A j) x (hAnabla i) (hAnabla j)]
    simp
  · intro y X Y
    simp only [U]
    rw [tensor0SField_sum_apply (I := I)]
    rw [tensor0SField_sum_apply (I := I)]
    have hinner (Z T : TangentSpace I y) (i : Fin d) :
        ((∑ j : Fin d,
            (U₀ ![basis i, basis j]) •
              normalizedWedgeTensorField (I := I) (A i) (A j)) y) ![Z, T] =
          ∑ j : Fin d,
            ((U₀ ![basis i, basis j]) •
              normalizedWedgeTensorField (I := I) (A i) (A j)) y ![Z, T] :=
      tensor0SField_sum_apply (I := I) _ y _
    simp_rw [hinner, tensor0SField_smul_apply (I := I),
      normalizedWedgeTensorField_skew (I := I) (A := A _)
      (B := A _) y X Y]
    simp only [mul_neg, Finset.sum_neg_distrib]

private theorem exists_spatial_test_tensor_fields
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible (I := I) cov g)
    (x : M) (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
    (W₀ : StrongDual Real (TangentSpace I x))
    (S : Tensor0SSpace (I := I) 2 x) :
    ∃ (U : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
      (W : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1),
      U x = U₀.toTensor0S ∧
      (∀ Z : TangentSpace I x, W x (fun _ : Fin 1 => Z) = W₀ Z) ∧
      totalNabla0SFun (I := I) (M := M) 1 cov W x = 0 ∧
      (∀ X Y Z : TangentSpace I x,
        totalNabla0SFun (I := I) (M := M) 2 cov U x ![X, Y, Z] =
          (1 / 2 : Real) * (S ![X, Y] * W₀ Z - S ![X, Z] * W₀ Y)) ∧
      ∀ y : M, ∀ X Y : TangentSpace I y,
        U y ![X, Y] = -U y ![Y, X] := by
  obtain ⟨Upar, hUparValue, hUparNabla, hUparSkew⟩ :=
    exists_parallel_two_form_tensor (I := I) cov hcov g hmc x U₀
  obtain ⟨Wpar, hWparValue, hWparNabla⟩ :=
    exists_parallel_one_form_tensor (I := I) cov g hmc x W₀
  obtain ⟨beta, hbetaValue, hbetaNabla⟩ :=
    exists_one_form_tensor_first_covariant_derivative_eq
      (I := I) cov g hmc x S
  let wedge := normalizedWedgeTensorField (I := I) beta Wpar
  let U := Upar + wedge
  have hwedgeValue : wedge x = 0 := by
    apply tensor0SSpace_ext (I := I) 2 x
    intro v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change normalizedWedgeTensorField (I := I) beta Wpar x ![v 0, v 1] = 0
    simp only [normalizedWedgeTensorField_apply, hbetaValue,
      Tensor0SSpace.zero_apply, zero_mul, mul_zero, sub_self]
  refine ⟨U, Wpar, ?_, hWparValue, hWparNabla, ?_, ?_⟩
  · change Upar x + wedge x = U₀.toTensor0S
    rw [hUparValue, hwedgeValue, add_zero]
  · intro X Y Z
    change totalNabla0SFun (I := I) (M := M) 2 cov (Upar + wedge) x
        ![X, Y, Z] = _
    rw [totalNabla0SFun_add, Tensor0SSpace.add_apply, hUparNabla,
      Tensor0SSpace.zero_apply, zero_add]
    change totalNabla0SFun (I := I) (M := M) 2 cov
        (normalizedWedgeTensorField (I := I) beta Wpar) x ![X, Y, Z] = _
    rw [normalizedWedgeTensorField_totalNabla_of_first_eq
      (I := I) cov hcov beta Wpar x S hbetaValue hbetaNabla hWparNabla X Y Z]
    rw [hWparValue, hWparValue]
  · intro y X Y
    change (Upar y + wedge y) ![X, Y] = -(Upar y + wedge y) ![Y, X]
    rw [Tensor0SSpace.add_apply, Tensor0SSpace.add_apply, hUparSkew y X Y]
    change
      -Upar y ![Y, X] +
          normalizedWedgeTensorField (I := I) beta Wpar y ![X, Y] =
        -(Upar y ![Y, X] +
          normalizedWedgeTensorField (I := I) beta Wpar y ![Y, X])
    rw [normalizedWedgeTensorField_skew (I := I) beta Wpar y X Y]
    ring

omit [T2Space M] in
private theorem tensor0SField_eq_neg_swap
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (hA : ∀ y : M, ∀ X Y : TangentSpace I y,
      A y ![X, Y] = -A y ![Y, X]) :
    A = (-1 : Real) •
      Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 2) 1) A := by
  apply DFunLike.ext _ _
  intro y
  apply tensor0SSpace_ext (I := I) 2 y
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  rw [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
    Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply]
  have hslots :
      (fun i => ![v 0, v 1] ((Equiv.swap (0 : Fin 2) 1) i)) =
        ![v 1, v 0] := by
    funext i
    fin_cases i <;> rfl
  rw [hslots, hA y (v 0) (v 1)]
  ring

private theorem totalNabla0S_eq_neg_domDomCongr
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (e : Equiv.Perm (Fin s))
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s)
    (hA : A = (-1 : Real) • Tensor0SField.domDomCongr ∞ e A) :
    let hreg := totalNabla0S_regularity (I := I) s cov hcov A
    let nablaA := totalNabla0S (I := I) s cov A hreg
    nablaA = (-1 : Real) •
      Tensor0SField.domDomCongr ∞ (frontExtendEquiv e) nablaA := by
  dsimp only
  apply DFunLike.ext _ _
  intro y
  rw [totalNabla0S_apply]
  conv_lhs => rw [hA]
  rw [totalNabla0SFun_smul, totalNabla0SFun_domDomCongr]
  rw [ContMDiffSection.coe_smul, Pi.smul_apply,
    Tensor0SField.domDomCongr_apply, totalNabla0S_apply]

private theorem canonicalSecondNabla0S_eq_neg_domDomCongr
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (hA : A = (-1 : Real) •
      Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 2) 1) A) :
    let derivs := CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) cov hcov A
    derivs.nabla2A = (-1 : Real) •
      Tensor0SField.domDomCongr ∞
        (frontExtendEquiv (frontExtendEquiv (Equiv.swap (0 : Fin 2) 1)))
        derivs.nabla2A := by
  dsimp only
  let hreg1 := totalNabla0S_regularity (I := I) 2 cov hcov A
  let nablaA := totalNabla0S (I := I) 2 cov A hreg1
  have hnablaA : nablaA = (-1 : Real) •
      Tensor0SField.domDomCongr ∞
        (frontExtendEquiv (Equiv.swap (0 : Fin 2) 1)) nablaA :=
    totalNabla0S_eq_neg_domDomCongr (I := I) cov hcov
      (Equiv.swap (0 : Fin 2) 1) A hA
  let hreg2 := totalNabla0S_regularity (I := I) 3 cov hcov nablaA
  let nabla2A := totalNabla0S (I := I) 3 cov nablaA hreg2
  have hnabla2A : nabla2A = (-1 : Real) •
      Tensor0SField.domDomCongr ∞
        (frontExtendEquiv (frontExtendEquiv (Equiv.swap (0 : Fin 2) 1)))
        nabla2A :=
    totalNabla0S_eq_neg_domDomCongr (I := I) cov hcov
      (frontExtendEquiv (Equiv.swap (0 : Fin 2) 1)) nablaA hnablaA
  simpa only [CanonicalSpatialDerivs0S.ofSmoothConnection, hreg1, nablaA,
    hreg2, nabla2A] using hnabla2A

private def canonicalRoughLap0SField
    {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s :=
  DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField
    (I := I) (M := M) g
    (CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) cov hcov A).nabla2A

private theorem canonicalRoughLap0SField_eq_neg_swap
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (hA : A = (-1 : Real) •
      Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 2) 1) A) :
    canonicalRoughLap0SField (I := I) g cov hcov A =
      (-1 : Real) • Tensor0SField.domDomCongr ∞
        (Equiv.swap (0 : Fin 2) 1)
        (canonicalRoughLap0SField (I := I) g cov hcov A) := by
  sorry

private theorem canonicalRoughLap0SField_skew
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (hA : ∀ y : M, ∀ X Y : TangentSpace I y,
      A y ![X, Y] = -A y ![Y, X])
    (y : M) (X Y : TangentSpace I y) :
    canonicalRoughLap0SField (I := I) g cov hcov A y ![X, Y] =
      -canonicalRoughLap0SField (I := I) g cov hcov A y ![Y, X] := by
  have hfield := canonicalRoughLap0SField_eq_neg_swap
    (I := I) g cov hcov A (tensor0SField_eq_neg_swap (I := I) A hA)
  conv_lhs => rw [hfield]
  rw [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  have hslots :
      (fun i => ![X, Y] ((Equiv.swap (0 : Fin 2) 1) i)) = ![Y, X] := by
    funext i
    fin_cases i <;> rfl
  rw [hslots]
  ring

private def skewProjection0SField
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  (1 / 2 : Real) •
    (A - Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 2) 1) A)

omit [T2Space M] in
private theorem skewProjection0SField_apply
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (y : M) (X Y : TangentSpace I y) :
    skewProjection0SField (I := I) A y ![X, Y] =
      (A y ![X, Y] - A y ![Y, X]) / 2 := by
  rw [skewProjection0SField]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.smul_apply,
    Tensor0SSpace.sub_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply, smul_eq_mul]
  have hslots : (fun i => ![X, Y] ((Equiv.swap 0 1) i)) = ![Y, X] := by
    funext i
    fin_cases i <;> rfl
  rw [hslots]
  ring

omit [T2Space M] in
private theorem skewProjection0SField_skew
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (y : M) (X Y : TangentSpace I y) :
    skewProjection0SField (I := I) A y ![X, Y] =
      -skewProjection0SField (I := I) A y ![Y, X] := by
  rw [skewProjection0SField_apply, skewProjection0SField_apply]
  ring

omit [T2Space M] in
private theorem affineTensor0SField_contMDiff
    {s : ℕ}
    (A B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s)
    (t₀ : Real) :
    ContMDiff (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Tensor0SModel s Real E)) ∞
      (fun p : M × Real =>
        (⟨p.1, A p.1 + (p.2 - t₀) • B p.1⟩ :
          TotalSpace (Tensor0SModel s Real E)
            (fun y : M => Tensor0SSpace s I y))) := by
  have hfst : ContMDiff (I.prod 𝓘(Real, Real)) I ∞
      (fun p : M × Real => p.1) := contMDiff_fst
  have hsnd : ContMDiff (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real => p.2) := contMDiff_snd
  have hA : ContMDiff (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Tensor0SModel s Real E)) ∞
      (fun p : M × Real =>
        (⟨p.1, A p.1⟩ : TotalSpace (Tensor0SModel s Real E)
          (fun y : M => Tensor0SSpace s I y))) := A.contMDiff.comp hfst
  have hB : ContMDiff (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Tensor0SModel s Real E)) ∞
      (fun p : M × Real =>
        (⟨p.1, B p.1⟩ : TotalSpace (Tensor0SModel s Real E)
          (fun y : M => Tensor0SSpace s I y))) := B.contMDiff.comp hfst
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel s Real E)
    (fun y : M => Tensor0SSpace s I y) x₀ with he
  have hA' := (Bundle.contMDiffAt_totalSpace
    (F := Tensor0SModel s Real E)
    (E := fun y : M => Tensor0SSpace s I y)).mp (hA p₀)
  have hB' := (Bundle.contMDiffAt_totalSpace
    (F := Tensor0SModel s Real E)
    (E := fun y : M => Tensor0SSpace s I y)).mp (hB p₀)
  have hscalar : ContMDiffAt (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real => p.2 - t₀) p₀ :=
    (hsnd.sub contMDiff_const).contMDiffAt
  refine (hA'.2.add (hscalar.smul hB'.2)).congr_of_eventuallyEq ?_
  · have hbase : ∀ᶠ p : M × Real in nhds p₀, p.1 ∈ e.baseSet :=
      continuousAt_fst (e.open_baseSet.mem_nhds (by
        rw [he, ← hx₀]
        exact mem_baseSet_trivializationAt _ _ p₀.1))
    filter_upwards [hbase] with p hp
    rw [(e.linear Real hp).map_add, (e.linear Real hp).map_smul]
    simp only [Pi.add_apply, Pi.smul_apply']
    rw [he, hx₀]

omit [T2Space M] in
private theorem affineTensor0SField_hasDerivAt
    {s : ℕ}
    (A B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s)
    (x : M) (t₀ : Real) (v : Fin s → TangentSpace I x) :
    HasDerivAt (fun t : Real => (A x + (t - t₀) • B x) v) (B x v) t₀ := by
  change HasDerivAt (fun t : Real => A x v + (t - t₀) * B x v) (B x v) t₀
  have hlinear := ((hasDerivAt_id t₀).sub_const t₀).mul_const (B x v)
  simpa only [id_eq, one_mul] using hlinear.const_add (A x v)
private theorem hamilton_intrinsic_test_jet_realization
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible (I := I) cov g)
    (x : M) (clock : HarnackClock)
    (Ric : Tensor0SSpace (I := I) 2 x)
    (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
    (W₀ : StrongDual Real (TangentSpace I x)) :
    ∃ (U : Real →
        Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
      (W : Real →
        Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1),
      ContMDiff (I.prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Tensor0SModel 2 Real E)) ∞
        (fun p : M × Real =>
          (⟨p.1, U p.2 p.1⟩ : TotalSpace (Tensor0SModel 2 Real E)
            (fun y : M => Tensor0SSpace 2 I y))) ∧
      ContMDiff (I.prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Tensor0SModel 1 Real E)) ∞
        (fun p : M × Real =>
          (⟨p.1, W p.2 p.1⟩ : TotalSpace (Tensor0SModel 1 Real E)
            (fun y : M => Tensor0SSpace 1 I y))) ∧
      U clock.time x = U₀.toTensor0S ∧
      (∀ Z : TangentSpace I x,
        W clock.time x (fun _ : Fin 1 => Z) = W₀ Z) ∧
      totalNabla0SFun (I := I) (M := M) 1 cov (W clock.time) x = 0 ∧
      (∀ X Y Z : TangentSpace I x,
        totalNabla0SFun (I := I) (M := M) 2 cov (U clock.time) x
            ![X, Y, Z] =
          (1 / 2 : Real) * (Ric ![X, Y] * W₀ Z - Ric ![X, Z] * W₀ Y) +
          (1 / (4 * clock.elapsed) : Real) *
            (g.inner x X Y * W₀ Z - g.inner x X Z * W₀ Y)) ∧
      (∀ r : Real, ∀ y : M, ∀ X Y : TangentSpace I y,
        U r y ![X, Y] = -U r y ![Y, X]) ∧
      (∀ v : Fin 2 → TangentSpace I x,
        HasDerivAt (fun r : Real => U r x v)
          ((Geometry.Operator.roughLap0STensor (I := I) g
              ((CanonicalSpatialDerivs0S.ofSmoothConnection
                (I := I) cov hcov (U clock.time)).nabla2A x) -
            covariantEndomorphismAction0S (I := I) (U clock.time x)
              (DifferentialGeometry.Geometry.Curvature.ricciEndAt
                (I := I) g Ric).toContinuousLinearMap) v)
          clock.time) ∧
      ∀ v : Fin 1 → TangentSpace I x,
        HasDerivAt (fun r : Real => W r x v)
          ((Geometry.Operator.roughLap0STensor (I := I) g
                ((CanonicalSpatialDerivs0S.ofSmoothConnection
                  (I := I) cov hcov (W clock.time)).nabla2A x) +
              (1 / clock.elapsed : Real) • W clock.time x -
            covariantEndomorphismAction0S (I := I) (W clock.time x)
              (DifferentialGeometry.Geometry.Curvature.ricciEndAt
                (I := I) g Ric).toContinuousLinearMap) v)
          clock.time := by
  let S : Tensor0SSpace (I := I) 2 x :=
    Ric + (1 / (2 * clock.elapsed) : Real) • metricTensorField (I := I) g x
  obtain ⟨Usp, Wsp, hUvalue, hWvalue, hDW, hDU, hUskew⟩ :=
    exists_spatial_test_tensor_fields (I := I) cov hcov g hmc x U₀ W₀ S
  let roughU := canonicalRoughLap0SField (I := I) g cov hcov Usp
  let roughW := canonicalRoughLap0SField (I := I) g cov hcov Wsp
  let RicEnd :=
    (DifferentialGeometry.Geometry.Curvature.ricciEndAt
      (I := I) g Ric).toContinuousLinearMap
  let UactionAt := covariantEndomorphismAction0S (I := I) (Usp x) RicEnd
  let WactionAt := covariantEndomorphismAction0S (I := I) (Wsp x) RicEnd
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨UactionRaw, hUactionRaw⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := Tensor0SModel 2 Real E)
      (V := fun y : M => Tensor0SSpace 2 I y) (n := (⊤ : ℕ∞)) x UactionAt
  let Uaction := skewProjection0SField (I := I) UactionRaw
  obtain ⟨Waction, hWaction⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := Tensor0SModel 1 Real E)
      (V := fun y : M => Tensor0SSpace 1 I y) (n := (⊤ : ℕ∞)) x WactionAt
  have hUaction : Uaction x = UactionAt := by
    apply tensor0SSpace_ext (I := I) 2 x
    intro v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    simp only [Uaction]
    rw [skewProjection0SField_apply, hUactionRaw]
    have hskew := covariantEndomorphismAction0S_two_skew
      (I := I) (Usp x) RicEnd (hUskew x) (v 0) (v 1)
    simpa only [UactionAt] using
      (show
        (UactionAt ![v 0, v 1] - UactionAt ![v 1, v 0]) / 2 =
          UactionAt ![v 0, v 1] by rw [hskew]; ring)
  let Udot := roughU - Uaction
  let Wdot := roughW + (1 / clock.elapsed : Real) • Wsp - Waction
  let U : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
    fun r => Usp + (r - clock.time) • Udot
  let W : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1 :=
    fun r => Wsp + (r - clock.time) • Wdot
  have hUtime : U clock.time = Usp := by
    simp only [U, sub_self, zero_smul, add_zero]
  have hWtime : W clock.time = Wsp := by
    simp only [W, sub_self, zero_smul, add_zero]
  refine ⟨U, W, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [U, ContMDiffSection.coe_add, Pi.add_apply,
      ContMDiffSection.coe_smul, Pi.smul_apply] using
      affineTensor0SField_contMDiff (I := I) Usp Udot clock.time
  · simpa only [W, ContMDiffSection.coe_add, Pi.add_apply,
      ContMDiffSection.coe_smul, Pi.smul_apply] using
      affineTensor0SField_contMDiff (I := I) Wsp Wdot clock.time
  · rw [hUtime]
    exact hUvalue
  · rw [hWtime]
    exact hWvalue
  · rw [hWtime]
    exact hDW
  · intro X Y Z
    rw [hUtime, hDU]
    simp only [S, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
      metricTensorField_apply, smul_eq_mul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [HarnackClock.elapsed_ne_zero clock]
    ring
  · intro r y X Y
    simp only [U, ContMDiffSection.coe_add, Pi.add_apply,
      ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
      Tensor0SSpace.smul_apply, Udot, ContMDiffSection.coe_sub, Pi.sub_apply,
      Tensor0SSpace.sub_apply, smul_eq_mul]
    rw [hUskew y X Y,
      canonicalRoughLap0SField_skew (I := I) g cov hcov Usp hUskew y X Y,
      skewProjection0SField_skew (I := I) UactionRaw y X Y]
    ring
  · intro v
    rw [hUtime]
    have htime := affineTensor0SField_hasDerivAt
      (I := I) Usp Udot x clock.time v
    have hUdotx : Udot x = roughU x - Uaction x := rfl
    have hUdotAt : Udot x = roughU x - UactionAt := by
      rw [hUdotx, hUaction]
    rw [hUdotAt] at htime
    simpa only [U, hUdotAt, roughU, canonicalRoughLap0SField,
      UactionAt, RicEnd,
      DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField_apply,
      Geometry.Operator.roughLap0STensor, ContMDiffSection.coe_add,
      ContMDiffSection.coe_sub,
      Pi.add_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
      Pi.sub_apply, Tensor0SSpace.sub_apply] using htime
  · intro v
    rw [hWtime]
    have htime := affineTensor0SField_hasDerivAt
      (I := I) Wsp Wdot x clock.time v
    have hWdotx : Wdot x =
        roughW x + (1 / clock.elapsed : Real) • Wsp x - Waction x := rfl
    have hWdotAt : Wdot x =
        roughW x + (1 / clock.elapsed : Real) • Wsp x - WactionAt := by
      rw [hWdotx, hWaction]
    rw [hWdotAt] at htime
    simpa only [W, hWdotAt, roughW, canonicalRoughLap0SField,
      WactionAt, RicEnd,
      DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField_apply,
      Geometry.Operator.roughLap0STensor, ContMDiffSection.coe_add,
      ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply,
      ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply,
      Tensor0SSpace.smul_apply, smul_eq_mul] using htime

theorem hamilton_test_jet_realization
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible (I := I) cov g)
    (x : M) (clock : HarnackClock)
    (Ric : Tensor0SSpace (I := I) 2 x)
    (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
    (W₀ : StrongDual Real (TangentSpace I x)) :
    ∃ (U : ∀ (_ : Real) (y : M),
        HamiltonHarnackTwoForm (TangentSpace I y))
      (U_tensor : Real →
        Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
      (W : Real →
        Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1),
      (∀ r : Real, ∀ y : M, (U r y).toTensor0S = U_tensor r y) ∧
      ContMDiff (I.prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Tensor0SModel 2 Real E)) ∞
        (fun p : M × Real =>
          (⟨p.1, U_tensor p.2 p.1⟩ : TotalSpace (Tensor0SModel 2 Real E)
            (fun y : M => Tensor0SSpace 2 I y))) ∧
      ContMDiff (I.prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Tensor0SModel 1 Real E)) ∞
        (fun p : M × Real =>
          (⟨p.1, W p.2 p.1⟩ : TotalSpace (Tensor0SModel 1 Real E)
            (fun y : M => Tensor0SSpace 1 I y))) ∧
      U clock.time x = U₀ ∧
      (∀ Z : TangentSpace I x,
        W clock.time x (fun _ : Fin 1 => Z) = W₀ Z) ∧
      totalNabla0SFun (I := I) (M := M) 1 cov (W clock.time) x = 0 ∧
      (∀ X Y Z : TangentSpace I x,
        totalNabla0SFun (I := I) (M := M) 2 cov (U_tensor clock.time) x
            ![X, Y, Z] =
          (1 / 2 : Real) * (Ric ![X, Y] * W₀ Z - Ric ![X, Z] * W₀ Y) +
          (1 / (4 * clock.elapsed) : Real) *
            (g.inner x X Y * W₀ Z - g.inner x X Z * W₀ Y)) ∧
      (∀ v : Fin 2 → TangentSpace I x,
        HasDerivAt (fun r : Real => U_tensor r x v)
          ((Geometry.Operator.roughLap0STensor (I := I) g
              ((CanonicalSpatialDerivs0S.ofSmoothConnection
                (I := I) cov hcov (U_tensor clock.time)).nabla2A x) -
            covariantEndomorphismAction0S (I := I) (U_tensor clock.time x)
              (DifferentialGeometry.Geometry.Curvature.ricciEndAt
                (I := I) g Ric).toContinuousLinearMap) v)
          clock.time) ∧
      ∀ v : Fin 1 → TangentSpace I x,
        HasDerivAt (fun r : Real => W r x v)
          ((Geometry.Operator.roughLap0STensor (I := I) g
                ((CanonicalSpatialDerivs0S.ofSmoothConnection
                  (I := I) cov hcov (W clock.time)).nabla2A x) +
              (1 / clock.elapsed : Real) • W clock.time x -
            covariantEndomorphismAction0S (I := I) (W clock.time x)
              (DifferentialGeometry.Geometry.Curvature.ricciEndAt
                (I := I) g Ric).toContinuousLinearMap) v)
          clock.time := by
  obtain ⟨U_tensor, W, hUjoint, hWjoint, hUvalue, hWvalue, hDW, hDU,
      hUskew, hUtime, hWtime⟩ :=
    hamilton_intrinsic_test_jet_realization
      (I := I) cov hcov g hmc x clock Ric U₀ W₀
  let U : ∀ (_ : Real) (y : M),
      HamiltonHarnackTwoForm (TangentSpace I y) :=
    fun r y => HamiltonHarnackTwoForm.ofTensor0S
      (I := I) (U_tensor r y) (hUskew r y)
  refine ⟨U, U_tensor, W, ?_, hUjoint, hWjoint, ?_, hWvalue,
    hDW, hDU, hUtime, hWtime⟩
  · intro r y
    exact HamiltonHarnackTwoForm.toTensor0S_ofTensor0S
      (I := I) (U_tensor r y) (hUskew r y)
  · apply HamiltonHarnackTwoForm.toTensor0S_injective (I := I)
    rw [show (U clock.time x).toTensor0S = U_tensor clock.time x by
      exact HamiltonHarnackTwoForm.toTensor0S_ofTensor0S
        (I := I) (U_tensor clock.time x) (hUskew clock.time x)]
    exact hUvalue

end DifferentialGeometry.PDE.RicciFlow
