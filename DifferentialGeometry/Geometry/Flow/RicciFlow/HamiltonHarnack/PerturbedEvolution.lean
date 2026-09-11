import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.BlockInterface
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.FiniteArrayNorm

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx]

def hamiltonMetricCurvatureBlockPerturbation
    (psi : Real) (a b c d : Idx) : Real :=
  by
    classical
    exact (psi / 2) *
      ((if a = c then 1 else 0) * (if b = d then 1 else 0) -
        (if a = d then 1 else 0) * (if b = c then 1 else 0))

def hamiltonPerturbedCurvatureBlock
    (K : Idx -> Idx -> Idx -> Idx -> Real) (psi : Real) :
    Idx -> Idx -> Idx -> Idx -> Real :=
  fun a b c d => K a b c d +
    hamiltonMetricCurvatureBlockPerturbation psi a b c d

def hamiltonPerturbedMBlock
    (clock : HarnackClock) (M : Idx -> Idx -> Real) (phi : Real) :
    Idx -> Idx -> Real :=
  by
    classical
    exact fun a b => M a b +
      (phi / clock.elapsed) * (if a = b then 1 else 0)

omit [Fintype Idx] in
private theorem metric_curvature_block_perturbation_abs_le
    (psi : Real) (hpsi : 0 <= psi) (a b c d : Idx) :
    |hamiltonMetricCurvatureBlockPerturbation psi a b c d| <= psi := by
  classical
  have hhalf : 0 <= psi / 2 := div_nonneg hpsi (by norm_num)
  unfold hamiltonMetricCurvatureBlockPerturbation
  split_ifs <;> simp_all [abs_of_nonneg hhalf]

omit [Fintype Idx] in
private theorem perturbed_m_block_sub_abs_le
    (clock : HarnackClock) (M : Idx -> Idx -> Real)
    (phi : Real) (hphi : 0 <= phi) (a b : Idx) :
    |hamiltonPerturbedMBlock clock M phi a b - M a b| <=
      phi / clock.elapsed := by
  classical
  have hquot : 0 <= phi / clock.elapsed :=
    div_nonneg hphi clock.elapsed_pos.le
  unfold hamiltonPerturbedMBlock
  rw [add_sub_cancel_left]
  by_cases hab : a = b
  · rw [if_pos hab, mul_one, abs_of_nonneg hquot]
  · rw [if_neg hab, mul_zero, abs_zero]
    exact hquot

private theorem metric_curvature_block_perturbation_quadratic
    (psi : Real) (U : Idx -> Idx -> Real)
    (hU : forall a b, U a b = -U b a) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      hamiltonMetricCurvatureBlockPerturbation psi a b c d *
        U a b * U c d) =
      psi * (∑ a, ∑ b, (U a b) ^ 2) := by
  classical
  simp only [hamiltonMetricCurvatureBlockPerturbation, mul_sub, sub_mul,
    mul_ite, ite_mul, mul_one, mul_zero, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_irrel]
  simp only [zero_mul, Fintype.sum_ite_eq]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.sum_const_zero, Fintype.sum_ite_eq]
  rw [hU b a]
  ring

private theorem metric_curvature_block_perturbation_gradient_quadratic
    (psi : Real) (DU : Idx -> Idx -> Idx -> Real)
    (hDU : forall e a b, DU e a b = -DU e b a) :
    (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      hamiltonMetricCurvatureBlockPerturbation psi a b c d *
        DU e a b * DU e c d) =
      psi * (∑ e, ∑ a, ∑ b, (DU e a b) ^ 2) := by
  classical
  simp only [hamiltonMetricCurvatureBlockPerturbation, mul_sub, sub_mul,
    mul_ite, ite_mul, mul_one, mul_zero, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_irrel]
  simp only [zero_mul, Fintype.sum_ite_eq]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.sum_const_zero, Fintype.sum_ite_eq]
  rw [hDU e b a]
  ring

private theorem metric_curvature_block_perturbation_contraction
    (psi : Real) (U : Idx -> Idx -> Real)
    (hU : forall a b, U a b = -U b a) (a b : Idx) :
    (∑ c, ∑ d,
      hamiltonMetricCurvatureBlockPerturbation psi a b c d * U c d) =
      psi * U a b := by
  classical
  simp only [hamiltonMetricCurvatureBlockPerturbation, mul_sub, sub_mul,
    mul_ite, ite_mul, mul_one, mul_zero, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_irrel]
  simp only [zero_mul, Fintype.sum_ite_eq]
  simp only [Finset.sum_const_zero, Fintype.sum_ite_eq]
  rw [hU b a]
  ring

private theorem diagonal_perturbation_quadratic
    [DecidableEq Idx]
    (clock : HarnackClock) (phi : Real) (W : Idx -> Real) :
    (∑ a, ∑ b,
      (phi / clock.elapsed) * (if a = b then 1 else 0) * W a * W b) =
      (phi / clock.elapsed) * (∑ a, (W a) ^ 2) := by
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp only [Fintype.sum_ite_eq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem hamiltonPerturbedBlockQuadratic_expand
    (clock : HarnackClock)
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (phi psi : Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hU : forall a b, U a b = -U b a) :
    hamiltonBlockQuadratic
        (hamiltonPerturbedCurvatureBlock K psi) P
        (hamiltonPerturbedMBlock clock M phi) U W =
      hamiltonBlockQuadratic K P M U W +
        (phi / clock.elapsed) * (∑ a, (W a) ^ 2) +
        psi * (∑ a, ∑ b, (U a b) ^ 2) := by
  classical
  unfold hamiltonBlockQuadratic hamiltonBlockPolarized
    hamiltonPerturbedCurvatureBlock hamiltonPerturbedMBlock
  simp only [add_mul, Finset.sum_add_distrib]
  rw [metric_curvature_block_perturbation_quadratic psi U hU,
    diagonal_perturbation_quadratic clock phi W]
  ring

theorem hamiltonBlockSigma_perturbed
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (psi : Real) (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hU : forall a b, U a b = -U b a) (a b : Idx) :
    hamiltonBlockSigma (hamiltonPerturbedCurvatureBlock K psi) P U W a b =
      hamiltonBlockSigma K P U W a b + psi * U a b := by
  classical
  unfold hamiltonBlockSigma hamiltonPerturbedCurvatureBlock
  simp only [add_mul, Finset.sum_add_distrib]
  rw [metric_curvature_block_perturbation_contraction psi U hU a b]
  ring

theorem hamiltonBlockSigmaSquare_perturbed_expand
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (psi : Real) (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hU : forall a b, U a b = -U b a) :
    hamiltonBlockSigmaSquare
        (hamiltonPerturbedCurvatureBlock K psi) P U W =
      hamiltonBlockSigmaSquare K P U W +
        2 * psi *
          (∑ a, ∑ b, hamiltonBlockSigma K P U W a b * U a b) +
        psi ^ 2 * (∑ a, ∑ b, (U a b) ^ 2) := by
  classical
  unfold hamiltonBlockSigmaSquare
  simp_rw [hamiltonBlockSigma_perturbed K P psi U W hU]
  simp only [add_sq, Finset.sum_add_distrib]
  have hcross :
      (∑ a, ∑ b, 2 * (hamiltonBlockSigma K P U W a b) *
          (psi * U a b)) =
        2 * psi *
          (∑ a, ∑ b, hamiltonBlockSigma K P U W a b * U a b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hsquare :
      (∑ a, ∑ b, (psi * U a b) ^ 2) =
        psi ^ 2 * (∑ a, ∑ b, (U a b) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hcross, hsquare]

theorem hamiltonBlockSigmaSquare_perturbed_abs_sub_le
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (psi : Real) (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (BK BP : Real) (hBK : 0 <= BK) (hBP : 0 <= BP)
    (hpsi0 : 0 <= psi) (hpsi1 : psi <= 1)
    (hK : forall a b c d, |K a b c d| <= BK)
    (hP : forall a b c, |P a b c| <= BP)
    (hU : forall a b, U a b = -U b a) :
    |hamiltonBlockSigmaSquare
        (hamiltonPerturbedCurvatureBlock K psi) P U W -
      hamiltonBlockSigmaSquare K P U W| <=
      psi * BP * (Fintype.card Idx : Real) ^ 2 *
          (∑ a, (W a) ^ 2) +
        psi *
          (BP * (Fintype.card Idx : Real) +
            2 * BK * (Fintype.card Idx : Real) ^ 2 + 1) *
          (∑ a, ∑ b, (U a b) ^ 2) := by
  classical
  let Up : Idx × Idx -> Real := fun p => U p.1 p.2
  let Pp : (Idx × Idx) -> Idx -> Real := fun p c => P p.1 p.2 c
  let Kp : (Idx × Idx) -> (Idx × Idx) -> Real := fun p q =>
    K p.1 p.2 q.1 q.2
  have hUp :
      (∑ p, (Up p) ^ 2) = ∑ a, ∑ b, (U a b) ^ 2 := by
    exact Fintype.sum_prod_type (fun p : Idx × Idx => (Up p) ^ 2)
  have hPU :
      |∑ a, ∑ b, ∑ c, P a b c * U a b * W c| <=
        BP / 2 *
          ((Fintype.card Idx : Real) *
              (∑ a, ∑ b, (U a b) ^ 2) +
            (Fintype.card Idx : Real) ^ 2 *
              (∑ c, (W c) ^ 2)) := by
    have h := DifferentialGeometry.Tensor0SBundle.abs_bilinear_sum_le
      Pp Up W BP hBP (fun p c => hP p.1 p.2 c)
    rw [hUp, Fintype.card_prod] at h
    simp only [Nat.cast_mul] at h
    have hrewrite :
        (∑ p, ∑ c, Pp p c * Up p * W c) =
          ∑ a, ∑ b, ∑ c, P a b c * U a b * W c := by
      exact Fintype.sum_prod_type
        (fun p : Idx × Idx => ∑ c, Pp p c * Up p * W c)
    rw [hrewrite] at h
    convert h using 1
    ring
  have hKU :
      |∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * U c d| <=
        BK * (Fintype.card Idx : Real) ^ 2 *
          (∑ a, ∑ b, (U a b) ^ 2) := by
    have h := DifferentialGeometry.Tensor0SBundle.abs_quadratic_sum_le
      Kp Up BK hBK (fun p q => hK p.1 p.2 q.1 q.2)
    rw [hUp, Fintype.card_prod] at h
    simp only [Nat.cast_mul] at h
    have hrewrite :
        (∑ p, ∑ q, Kp p q * Up p * Up q) =
          ∑ a, ∑ b, ∑ c, ∑ d,
            K a b c d * U a b * U c d := by
      calc
        (∑ p, ∑ q, Kp p q * Up p * Up q) =
            ∑ a, ∑ b, ∑ q,
              Kp (a, b) q * Up (a, b) * Up q := by
          rw [Fintype.sum_prod_type]
        _ = ∑ a, ∑ b, ∑ c, ∑ d,
              K a b c d * U a b * U c d := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Fintype.sum_prod_type]
    rw [hrewrite] at h
    convert h using 1
    ring
  let cross := ∑ a, ∑ b, hamiltonBlockSigma K P U W a b * U a b
  have hcross :
      |cross| <=
        BP / 2 *
          ((Fintype.card Idx : Real) *
              (∑ a, ∑ b, (U a b) ^ 2) +
            (Fintype.card Idx : Real) ^ 2 *
              (∑ c, (W c) ^ 2)) +
          BK * (Fintype.card Idx : Real) ^ 2 *
            (∑ a, ∑ b, (U a b) ^ 2) := by
    have hexpand :
        cross =
          (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
            ∑ a, ∑ b, ∑ c, ∑ d,
              K a b c d * U a b * U c d := by
      dsimp [cross]
      unfold hamiltonBlockSigma
      simp only [add_mul, Finset.sum_add_distrib]
      simp_rw [Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
      · refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
    rw [hexpand]
    exact (abs_add_le _ _).trans (add_le_add hPU hKU)
  have hU2 : 0 <= ∑ a, ∑ b, (U a b) ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hexact :
      hamiltonBlockSigmaSquare
          (hamiltonPerturbedCurvatureBlock K psi) P U W -
        hamiltonBlockSigmaSquare K P U W =
      2 * psi * cross + psi ^ 2 * (∑ a, ∑ b, (U a b) ^ 2) := by
    rw [hamiltonBlockSigmaSquare_perturbed_expand K P psi U W hU]
    dsimp [cross]
    ring
  have hpsiSq : psi ^ 2 <= psi := by
    nlinarith [mul_nonneg hpsi0 (sub_nonneg.mpr hpsi1)]
  have hpsiU :
      psi ^ 2 * (∑ a, ∑ b, (U a b) ^ 2) <=
        psi * (∑ a, ∑ b, (U a b) ^ 2) :=
    mul_le_mul_of_nonneg_right hpsiSq hU2
  rw [hexact]
  calc
    |2 * psi * cross + psi ^ 2 * (∑ a, ∑ b, (U a b) ^ 2)| <=
        |2 * psi * cross| +
          |psi ^ 2 * (∑ a, ∑ b, (U a b) ^ 2)| := abs_add_le _ _
    _ = 2 * psi * |cross| +
        psi ^ 2 * (∑ a, ∑ b, (U a b) ^ 2) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow,
        abs_of_nonneg hpsi0, abs_of_nonneg hU2]
      norm_num
    _ <= 2 * psi *
          (BP / 2 *
              ((Fintype.card Idx : Real) *
                  (∑ a, ∑ b, (U a b) ^ 2) +
                (Fintype.card Idx : Real) ^ 2 *
                  (∑ c, (W c) ^ 2)) +
            BK * (Fintype.card Idx : Real) ^ 2 *
              (∑ a, ∑ b, (U a b) ^ 2)) +
          psi ^ 2 * (∑ a, ∑ b, (U a b) ^ 2) := by
      gcongr
    _ <= psi * BP * (Fintype.card Idx : Real) ^ 2 *
          (∑ a, (W a) ^ 2) +
        psi *
          (BP * (Fintype.card Idx : Real) +
            2 * BK * (Fintype.card Idx : Real) ^ 2 + 1) *
          (∑ a, ∑ b, (U a b) ^ 2) := by
      calc
        2 * psi *
              (BP / 2 *
                  ((Fintype.card Idx : Real) *
                      (∑ a, ∑ b, (U a b) ^ 2) +
                    (Fintype.card Idx : Real) ^ 2 *
                      (∑ c, (W c) ^ 2)) +
                BK * (Fintype.card Idx : Real) ^ 2 *
                  (∑ a, ∑ b, (U a b) ^ 2)) +
            psi ^ 2 * (∑ a, ∑ b, (U a b) ^ 2) <=
            2 * psi *
              (BP / 2 *
                  ((Fintype.card Idx : Real) *
                      (∑ a, ∑ b, (U a b) ^ 2) +
                    (Fintype.card Idx : Real) ^ 2 *
                      (∑ c, (W c) ^ 2)) +
                BK * (Fintype.card Idx : Real) ^ 2 *
                  (∑ a, ∑ b, (U a b) ^ 2)) +
            psi * (∑ a, ∑ b, (U a b) ^ 2) := by
          exact add_le_add_right hpsiU
            (2 * psi *
              (BP / 2 *
                  ((Fintype.card Idx : Real) *
                      (∑ a, ∑ b, (U a b) ^ 2) +
                    (Fintype.card Idx : Real) ^ 2 *
                      (∑ c, (W c) ^ 2)) +
                BK * (Fintype.card Idx : Real) ^ 2 *
                  (∑ a, ∑ b, (U a b) ^ 2)))
        _ = psi * BP * (Fintype.card Idx : Real) ^ 2 *
              (∑ a, (W a) ^ 2) +
            psi *
              (BP * (Fintype.card Idx : Real) +
                2 * BK * (Fintype.card Idx : Real) ^ 2 + 1) *
              (∑ a, ∑ b, (U a b) ^ 2) := by
          ring

private theorem abs_four_sum_quadratic_le
    (F : Idx -> Idx -> Idx -> Idx -> Real)
    (X : Idx -> Real) (C : Real) (hC : 0 <= C)
    (hF : forall a b c d, |F a b c d| <= C) :
    |∑ a, ∑ b, ∑ c, ∑ d, F a b c d * X a * X b| <=
      C * (Fintype.card Idx : Real) ^ 3 *
        (∑ a, (X a) ^ 2) := by
  classical
  let A : Idx -> Idx -> Real := fun a b => ∑ c, ∑ d, F a b c d
  have hrewrite :
      (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * X a * X b) =
        ∑ a, ∑ b, A a b * X a * X b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    dsimp [A]
    simp_rw [Finset.sum_mul]
  rw [hrewrite]
  have hA : forall a b,
      |A a b| <= (Fintype.card Idx : Real) ^ 2 * C := by
    intro a b
    have h :=
      DifferentialGeometry.Tensor0SBundle.abs_double_sum_le_card_mul_card_mul_of_bound
        (fun c d => F a b c d) C (hF a b)
    simpa only [A, pow_two] using h
  have hnonneg : 0 <= (Fintype.card Idx : Real) ^ 2 * C :=
    mul_nonneg (sq_nonneg _) hC
  have hquad := DifferentialGeometry.Tensor0SBundle.abs_quadratic_sum_le
    A X ((Fintype.card Idx : Real) ^ 2 * C) hnonneg hA
  calc
    |∑ a, ∑ b, A a b * X a * X b| <=
        ((Fintype.card Idx : Real) ^ 2 * C) *
          (Fintype.card Idx : Real) * (∑ a, (X a) ^ 2) := hquad
    _ = C * (Fintype.card Idx : Real) ^ 3 *
        (∑ a, (X a) ^ 2) := by ring

private theorem abs_five_sum_matrix_vector_le
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (C : Real) (hC : 0 <= C)
    (hF : forall a b c d e, |F a b c d e| <= C) :
    |∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        F a b c d e * U a b * W c| <=
      (C * (Fintype.card Idx : Real) ^ 2) / 2 *
        ((Fintype.card Idx : Real) *
            (∑ a, ∑ b, (U a b) ^ 2) +
          (Fintype.card Idx : Real) ^ 2 *
            (∑ c, (W c) ^ 2)) := by
  classical
  let A : (Idx × Idx) -> Idx -> Real := fun p c =>
    ∑ d, ∑ e, F p.1 p.2 c d e
  let Up : Idx × Idx -> Real := fun p => U p.1 p.2
  have hrewrite :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          F a b c d e * U a b * W c) =
        ∑ p, ∑ c, A p c * Up p * W c := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          F a b c d e * U a b * W c) =
          ∑ p : Idx × Idx, ∑ c, ∑ d, ∑ e,
            F p.1 p.2 c d e * U p.1 p.2 * W c := by
        rw [Fintype.sum_prod_type]
      _ = ∑ p, ∑ c, A p c * Up p * W c := by
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        dsimp [A, Up]
        simp_rw [Finset.sum_mul]
  rw [hrewrite]
  have hA : forall p c,
      |A p c| <= (Fintype.card Idx : Real) ^ 2 * C := by
    intro p c
    have h :=
      DifferentialGeometry.Tensor0SBundle.abs_double_sum_le_card_mul_card_mul_of_bound
        (fun d e => F p.1 p.2 c d e) C (hF p.1 p.2 c)
    simpa only [A, pow_two] using h
  have hnonneg : 0 <= (Fintype.card Idx : Real) ^ 2 * C :=
    mul_nonneg (sq_nonneg _) hC
  have hbilinear := DifferentialGeometry.Tensor0SBundle.abs_bilinear_sum_le
    A Up W ((Fintype.card Idx : Real) ^ 2 * C) hnonneg hA
  have hUp :
      (∑ p, (Up p) ^ 2) = ∑ a, ∑ b, (U a b) ^ 2 := by
    exact Fintype.sum_prod_type (fun p : Idx × Idx => (Up p) ^ 2)
  rw [hUp, Fintype.card_prod] at hbilinear
  simp only [Nat.cast_mul] at hbilinear
  convert hbilinear using 1
  ring

private theorem abs_six_sum_matrix_quadratic_le
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (C : Real) (hC : 0 <= C)
    (hF : forall a b c d e f, |F a b c d e f| <= C) :
    |∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
        F a b c d e f * U a b * U c d| <=
      C * (Fintype.card Idx : Real) ^ 4 *
        (∑ a, ∑ b, (U a b) ^ 2) := by
  classical
  let A : (Idx × Idx) -> (Idx × Idx) -> Real := fun p q =>
    ∑ e, ∑ f, F p.1 p.2 q.1 q.2 e f
  let Up : Idx × Idx -> Real := fun p => U p.1 p.2
  have hrewrite :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          F a b c d e f * U a b * U c d) =
        ∑ p, ∑ q, A p q * Up p * Up q := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          F a b c d e f * U a b * U c d) =
          ∑ p : Idx × Idx, ∑ c, ∑ d, ∑ e, ∑ f,
            F p.1 p.2 c d e f * U p.1 p.2 * U c d := by
        rw [Fintype.sum_prod_type]
      _ = ∑ p : Idx × Idx, ∑ q : Idx × Idx, ∑ e, ∑ f,
            F p.1 p.2 q.1 q.2 e f * U p.1 p.2 * U q.1 q.2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Fintype.sum_prod_type]
      _ = ∑ p, ∑ q, A p q * Up p * Up q := by
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun q _ => ?_
        dsimp [A, Up]
        simp_rw [Finset.sum_mul]
  rw [hrewrite]
  have hA : forall p q,
      |A p q| <= (Fintype.card Idx : Real) ^ 2 * C := by
    intro p q
    have h :=
      DifferentialGeometry.Tensor0SBundle.abs_double_sum_le_card_mul_card_mul_of_bound
        (fun e f => F p.1 p.2 q.1 q.2 e f) C
        (hF p.1 p.2 q.1 q.2)
    simpa only [A, pow_two] using h
  have hnonneg : 0 <= (Fintype.card Idx : Real) ^ 2 * C :=
    mul_nonneg (sq_nonneg _) hC
  have hquad := DifferentialGeometry.Tensor0SBundle.abs_quadratic_sum_le
    A Up ((Fintype.card Idx : Real) ^ 2 * C) hnonneg hA
  have hUp :
      (∑ p, (Up p) ^ 2) = ∑ a, ∑ b, (U a b) ^ 2 := by
    exact Fintype.sum_prod_type (fun p : Idx × Idx => (Up p) ^ 2)
  rw [hUp, Fintype.card_prod] at hquad
  simp only [Nat.cast_mul] at hquad
  convert hquad using 1
  ring

theorem hamiltonBlockJ_add_blocks_abs_sub_le
    (K dK : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M dM : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (BK BP BM BdK BdM : Real)
    (hBK : 0 <= BK) (hBP : 0 <= BP) (hBM : 0 <= BM)
    (hBdK : 0 <= BdK) (hBdM : 0 <= BdM)
    (hK : forall a b c d, |K a b c d| <= BK)
    (hP : forall a b c, |P a b c| <= BP)
    (hM : forall a b, |M a b| <= BM)
    (hdK : forall a b c d, |dK a b c d| <= BdK)
    (hdM : forall a b, |dM a b| <= BdM) :
    |hamiltonBlockJ (fun a b c d => K a b c d + dK a b c d) P
        (fun a b => M a b + dM a b) U W -
      hamiltonBlockJ K P M U W| <=
      (2 * (BK * BdM + BdK * BM + BdK * BdM) *
          (Fintype.card Idx : Real) ^ 3 +
        4 * BdK * BP * (Fintype.card Idx : Real) ^ 4) *
          (∑ a, (W a) ^ 2) +
      (4 * BdK * BP * (Fintype.card Idx : Real) ^ 3 +
        (8 * BK * BdK + 4 * BdK ^ 2) *
          (Fintype.card Idx : Real) ^ 4) *
          (∑ a, ∑ b, (U a b) ^ 2) := by
  classical
  let T1 := 2 * (∑ a, ∑ b, ∑ c, ∑ d,
    K a c b d * dM c d * W a * W b)
  let T2 := 2 * (∑ a, ∑ b, ∑ c, ∑ d,
    dK a c b d * M c d * W a * W b)
  let T3 := 2 * (∑ a, ∑ b, ∑ c, ∑ d,
    dK a c b d * dM c d * W a * W b)
  let T4 := 8 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    dK a d c e * P d b e * U a b * W c)
  let T5 := 4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    K a e c f * dK b e d f * U a b * U c d)
  let T6 := 4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    dK a e c f * K b e d f * U a b * U c d)
  let T7 := 4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    dK a e c f * dK b e d f * U a b * U c d)
  have hexpand :
      hamiltonBlockJ (fun a b c d => K a b c d + dK a b c d) P
          (fun a b => M a b + dM a b) U W -
        hamiltonBlockJ K P M U W =
      T1 + T2 + T3 + T4 + T5 + T6 + T7 := by
    rw [hamiltonBlockJ_add_blocks]
    dsimp [T1, T2, T3, T4, T5, T6, T7]
    ring
  rw [hexpand]
  have hmul {x y A B : Real} (hA : 0 <= A)
      (hx : |x| <= A) (hy : |y| <= B) :
      |x * y| <= A * B := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hA
  have hT1 :
      |T1| <= 2 * BK * BdM * (Fintype.card Idx : Real) ^ 3 *
        (∑ a, (W a) ^ 2) := by
    have hs := abs_four_sum_quadratic_le
      (fun a b c d => K a c b d * dM c d) W (BK * BdM)
      (mul_nonneg hBK hBdM)
      (fun a b c d => hmul hBK (hK a c b d) (hdM c d))
    dsimp [T1]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    nlinarith
  have hT2 :
      |T2| <= 2 * BdK * BM * (Fintype.card Idx : Real) ^ 3 *
        (∑ a, (W a) ^ 2) := by
    have hs := abs_four_sum_quadratic_le
      (fun a b c d => dK a c b d * M c d) W (BdK * BM)
      (mul_nonneg hBdK hBM)
      (fun a b c d => hmul hBdK (hdK a c b d) (hM c d))
    dsimp [T2]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    nlinarith
  have hT3 :
      |T3| <= 2 * BdK * BdM * (Fintype.card Idx : Real) ^ 3 *
        (∑ a, (W a) ^ 2) := by
    have hs := abs_four_sum_quadratic_le
      (fun a b c d => dK a c b d * dM c d) W (BdK * BdM)
      (mul_nonneg hBdK hBdM)
      (fun a b c d => hmul hBdK (hdK a c b d) (hdM c d))
    dsimp [T3]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    nlinarith
  have hT4 :
      |T4| <=
        4 * BdK * BP * (Fintype.card Idx : Real) ^ 3 *
            (∑ a, ∑ b, (U a b) ^ 2) +
          4 * BdK * BP * (Fintype.card Idx : Real) ^ 4 *
            (∑ a, (W a) ^ 2) := by
    have hs := abs_five_sum_matrix_vector_le
      (fun a b c d e => dK a d c e * P d b e) U W (BdK * BP)
      (mul_nonneg hBdK hBP)
      (fun a b c d e => hmul hBdK (hdK a d c e) (hP d b e))
    dsimp [T4]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 8)]
    nlinarith
  have hT5 :
      |T5| <= 4 * BK * BdK * (Fintype.card Idx : Real) ^ 4 *
        (∑ a, ∑ b, (U a b) ^ 2) := by
    have hs := abs_six_sum_matrix_quadratic_le
      (fun a b c d e f => K a e c f * dK b e d f) U (BK * BdK)
      (mul_nonneg hBK hBdK)
      (fun a b c d e f => hmul hBK (hK a e c f) (hdK b e d f))
    dsimp [T5]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 4)]
    nlinarith
  have hT6 :
      |T6| <= 4 * BdK * BK * (Fintype.card Idx : Real) ^ 4 *
        (∑ a, ∑ b, (U a b) ^ 2) := by
    have hs := abs_six_sum_matrix_quadratic_le
      (fun a b c d e f => dK a e c f * K b e d f) U (BdK * BK)
      (mul_nonneg hBdK hBK)
      (fun a b c d e f => hmul hBdK (hdK a e c f) (hK b e d f))
    dsimp [T6]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 4)]
    nlinarith
  have hT7 :
      |T7| <= 4 * BdK ^ 2 * (Fintype.card Idx : Real) ^ 4 *
        (∑ a, ∑ b, (U a b) ^ 2) := by
    have hs := abs_six_sum_matrix_quadratic_le
      (fun a b c d e f => dK a e c f * dK b e d f) U (BdK ^ 2)
      (sq_nonneg BdK)
      (fun a b c d e f => by
        rw [abs_mul]
        calc
          |dK a e c f| * |dK b e d f| <= BdK * BdK :=
            mul_le_mul (hdK a e c f) (hdK b e d f)
              (abs_nonneg _) hBdK
          _ = BdK ^ 2 := by ring)
    dsimp [T7]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 4)]
    nlinarith
  have htriangle :
      |T1 + T2 + T3 + T4 + T5 + T6 + T7| <=
        |T1| + |T2| + |T3| + |T4| + |T5| + |T6| + |T7| := by
    calc
      |T1 + T2 + T3 + T4 + T5 + T6 + T7| <=
          |T1 + T2 + T3 + T4 + T5 + T6| + |T7| := abs_add_le _ _
      _ <= (|T1 + T2 + T3 + T4 + T5| + |T6|) + |T7| := by
        gcongr
        exact abs_add_le _ _
      _ <= ((|T1 + T2 + T3 + T4| + |T5|) + |T6|) + |T7| := by
        gcongr
        exact abs_add_le _ _
      _ <= (((|T1 + T2 + T3| + |T4|) + |T5|) + |T6|) + |T7| := by
        gcongr
        exact abs_add_le _ _
      _ <= ((((|T1 + T2| + |T3|) + |T4|) + |T5|) + |T6|) + |T7| := by
        gcongr
        exact abs_add_le _ _
      _ <= (((((|T1| + |T2|) + |T3|) + |T4|) + |T5|) + |T6|) + |T7| := by
        gcongr
        exact abs_add_le _ _
  calc
    |T1 + T2 + T3 + T4 + T5 + T6 + T7| <=
        |T1| + |T2| + |T3| + |T4| + |T5| + |T6| + |T7| := htriangle
    _ <=
        (2 * (BK * BdM + BdK * BM + BdK * BdM) *
            (Fintype.card Idx : Real) ^ 3 +
          4 * BdK * BP * (Fintype.card Idx : Real) ^ 4) *
            (∑ a, (W a) ^ 2) +
        (4 * BdK * BP * (Fintype.card Idx : Real) ^ 3 +
          (8 * BK * BdK + 4 * BdK ^ 2) *
            (Fintype.card Idx : Real) ^ 4) *
            (∑ a, ∑ b, (U a b) ^ 2) := by
      linarith

private theorem perturbation_reaction_w_coefficient_le
    (tau S B N phi psi : Real)
    (htau : 0 < tau) (htauS : tau <= S)
    (hB : 0 <= B) (hN : 0 <= N) (hphi : 0 <= phi)
    (hpsi : 0 <= psi) (hpsi1 : psi <= 1) :
    2 * (B * (phi / tau) + psi * (B / tau) +
        psi * (phi / tau)) * N ^ 3 +
        4 * psi * B * N ^ 4 <=
      (2 * (B + 1) * N ^ 3) * (phi / tau) +
        (2 * B * S * N ^ 3 + 4 * B * S ^ 2 * N ^ 4) *
          (psi / tau ^ 2) := by
  have htau0 : 0 <= tau := htau.le
  have hS : 0 <= S := htau0.trans htauS
  have htauSq : 0 < tau ^ 2 := sq_pos_of_pos htau
  have htauSqS : tau ^ 2 <= S ^ 2 := by nlinarith
  have hphiTau : 0 <= phi / tau := div_nonneg hphi htau0
  have hpsiTau :
      psi / tau <= S * psi / tau ^ 2 := by
    calc
      psi / tau = (psi * tau) / tau ^ 2 := by
        field_simp [ne_of_gt htau]
      _ <= (S * psi) / tau ^ 2 := by
        apply (div_le_div_iff_of_pos_right htauSq).2
        nlinarith [mul_nonneg hpsi (sub_nonneg.mpr htauS)]
  have hpsiZero :
      psi <= S ^ 2 * psi / tau ^ 2 := by
    calc
      psi = (tau ^ 2 * psi) / tau ^ 2 := by
        field_simp [ne_of_gt htau]
      _ <= (S ^ 2 * psi) / tau ^ 2 := by
        apply (div_le_div_iff_of_pos_right htauSq).2
        exact mul_le_mul_of_nonneg_right htauSqS hpsi
  have hpsiPhi : psi * (phi / tau) <= phi / tau := by
    nlinarith [mul_nonneg hphiTau (sub_nonneg.mpr hpsi1)]
  have hpsiBtau :
      psi * (B / tau) <= B * S * (psi / tau ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hpsiTau hB
    convert hscaled using 1 <;> first | rfl | ring
  have hpsiB :
      psi * B <= B * S ^ 2 * (psi / tau ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hpsiZero hB
    convert hscaled using 1 <;> first | rfl | ring
  have hpair := add_le_add_left hpsiBtau (B * (phi / tau))
  have hfirst := add_le_add hpair hpsiPhi
  have hscaleFirst : 0 <= 2 * N ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg hN 3)
  have hscaleSecond : 0 <= 4 * N ^ 4 := by positivity
  have hfirstScaled := mul_le_mul_of_nonneg_right hfirst hscaleFirst
  have hsecondScaled := mul_le_mul_of_nonneg_right hpsiB hscaleSecond
  have htotal := add_le_add hfirstScaled hsecondScaled
  convert htotal using 1 <;> first | rfl | ring

private theorem perturbation_reaction_u_coefficient_le
    (B N psi : Real)
    (hpsi : 0 <= psi) (hpsi1 : psi <= 1) :
    4 * psi * B * N ^ 3 +
        (8 * B * psi + 4 * psi ^ 2) * N ^ 4 <=
      psi * (4 * B * N ^ 3 + (8 * B + 4) * N ^ 4) := by
  have hpsiSq : psi ^ 2 <= psi := by
    nlinarith [mul_nonneg hpsi (sub_nonneg.mpr hpsi1)]
  have hscale : 0 <= 4 * N ^ 4 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hpsiSq hscale
  have htotal := add_le_add_left hscaled
    (4 * psi * B * N ^ 3 + 8 * B * psi * N ^ 4)
  convert htotal using 1 <;> first | rfl | ring

private theorem perturbation_jet_coefficient_le
    (tau S B N psi : Real)
    (htau : 0 < tau) (htauS : tau <= S)
    (hpsi : 0 <= psi) :
    2 * psi *
        ((2 * B ^ 2 + 1 / (2 * tau ^ 2)) * N ^ 2) <=
      (4 * B ^ 2 * S ^ 2 * N ^ 2 + N ^ 2) *
        (psi / tau ^ 2) := by
  have htau0 : 0 <= tau := htau.le
  have hS : 0 <= S := htau0.trans htauS
  have htauSq : 0 < tau ^ 2 := sq_pos_of_pos htau
  have htauSqS : tau ^ 2 <= S ^ 2 := by nlinarith
  have hpsiZero :
      psi <= S ^ 2 * psi / tau ^ 2 := by
    calc
      psi = (tau ^ 2 * psi) / tau ^ 2 := by
        field_simp [ne_of_gt htau]
      _ <= (S ^ 2 * psi) / tau ^ 2 := by
        apply (div_le_div_iff_of_pos_right htauSq).2
        exact mul_le_mul_of_nonneg_right htauSqS hpsi
  have hscale : 0 <= 4 * B ^ 2 * N ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) (sq_nonneg N)
  have hscaled := mul_le_mul_of_nonneg_right hpsiZero hscale
  have htotal := add_le_add_right hscaled (N ^ 2 * (psi / tau ^ 2))
  convert htotal using 1 <;> first | rfl | ring

theorem hamiltonPerturbedBlock_heat_product_eq_exact
    (clock : HarnackClock)
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (LK : Idx -> Idx -> Idx -> Idx -> Real)
    (LP : Idx -> Idx -> Idx -> Real)
    (LM : Idx -> Idx -> Real)
    (DK : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (DP : Idx -> Idx -> Idx -> Idx -> Real)
    (DM : Idx -> Idx -> Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real)
    (phi Lphi psi psi' : Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hU : forall a b, U a b = -U b a)
    (hDU : forall e a b, DU e a b = -DU e b a) :
    hamiltonBlockHeatProduct
        (hamiltonPerturbedCurvatureBlock K psi) P
        (hamiltonPerturbedMBlock clock M phi)
        (hamiltonPerturbedCurvatureBlock LK psi') LP
        (hamiltonPerturbedMBlock clock LM
          (Lphi - phi / clock.elapsed))
        DK DP DM DU (fun _ => 0) (fun _ _ => 0)
        (fun a => (1 / clock.elapsed) * W a) U W =
      hamiltonBlockHeatProduct K P M LK LP LM DK DP DM DU
          (fun _ => 0) (fun _ _ => 0)
          (fun a => (1 / clock.elapsed) * W a) U W +
        (Lphi / clock.elapsed + phi / clock.elapsed ^ 2) *
          (∑ a, (W a) ^ 2) +
        psi' * (∑ a, ∑ b, (U a b) ^ 2) -
        2 * psi * (∑ e, ∑ a, ∑ b, (DU e a b) ^ 2) := by
  classical
  unfold hamiltonBlockHeatProduct hamiltonPerturbedCurvatureBlock
    hamiltonPerturbedMBlock
  simp only [add_mul, mul_add, Finset.sum_add_distrib, zero_mul, mul_zero,
    Finset.sum_const_zero, sub_zero, add_zero]
  rw [metric_curvature_block_perturbation_quadratic psi' U hU,
    metric_curvature_block_perturbation_gradient_quadratic psi DU hDU]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp only [Fintype.sum_ite_eq]
  ring_nf
  have hP :
      (∑ a, ∑ b, ∑ c,
          P a b c * U a b * clock.elapsed⁻¹ * W c) =
        ∑ a, ∑ b, ∑ c,
          clock.elapsed⁻¹ * P a b c * U a b * W c := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hsum (q : Real) :
      (∑ a, q * (W a) ^ 2) = q * (∑ a, (W a) ^ 2) := by
    rw [Finset.mul_sum]
  have hdiagonal :
      (∑ a,
          (clock.elapsed⁻¹ * Lphi * (W a) ^ 2 -
            clock.elapsed⁻¹ ^ 2 * phi * (W a) ^ 2)) +
          (∑ a, clock.elapsed⁻¹ ^ 2 * phi * (W a) ^ 2) * 2 =
        clock.elapsed⁻¹ * Lphi * (∑ a, (W a) ^ 2) +
          clock.elapsed⁻¹ ^ 2 * phi * (∑ a, (W a) ^ 2) := by
    rw [Finset.sum_sub_distrib,
      hsum (clock.elapsed⁻¹ * Lphi),
      hsum (clock.elapsed⁻¹ ^ 2 * phi)]
    ring
  rw [hP]
  linear_combination hdiagonal

theorem hamiltonPerturbedBlock_heat_product_eq_j_add_sigma_square
    [DecidableEq Idx]
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaM : Idx -> Idx -> Idx -> Real)
    (phi Lphi psi psi' : Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hRm : Rm04Symm R)
    (hNablaRm : forall e, Rm04PairSymm (nablaR e))
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hContract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hNablaPSkew : forall e a b c,
      nablaP e a b c = -nablaP e b a c)
    (hM : forall a b,
      hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) a b =
        hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) b a)
    (hU : forall a b, U a b = -U b a) :
    hamiltonBlockHeatProduct
        (hamiltonPerturbedCurvatureBlock
          (fun a b c d => R a b d c) psi)
        (hamiltonPComponent nablaRic)
        (hamiltonPerturbedMBlock clock
          (hamiltonMComponent clock R Ric
            (fun a b => ∑ e, nablaP e e a b)) phi)
        (hamiltonPerturbedCurvatureBlock
          (fun a b c d => hamiltonRmReactionComponent R a b d c) psi')
        (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
        (hamiltonPerturbedMBlock clock
          (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
            (fun a b => ∑ e, nablaP e e a b))
          (Lphi - phi / clock.elapsed))
        (fun e a b c d => nablaR e a b d c) nablaP nablaM
        (hamiltonTestJetDU clock Ric
          (fun a b => if a = b then 1 else 0) W)
        (fun _ => 0) (fun _ _ => 0)
        (fun a => (1 / clock.elapsed) * W a) U W =
      hamiltonBlockJ
          (fun a b c d => R a b d c)
          (hamiltonPComponent nablaRic)
          (hamiltonMComponent clock R Ric
            (fun a b => ∑ e, nablaP e e a b)) U W +
        hamiltonBlockSigmaSquare
          (fun a b c d => R a b d c)
          (hamiltonPComponent nablaRic) U W +
        (Lphi / clock.elapsed + phi / clock.elapsed ^ 2) *
          (∑ a, (W a) ^ 2) +
        psi' * (∑ a, ∑ b, (U a b) ^ 2) -
        2 * psi *
          (∑ e, ∑ a, ∑ b,
            (hamiltonTestJetDU clock Ric
              (fun i j => if i = j then 1 else 0) W e a b) ^ 2) := by
  rw [hamiltonPerturbedBlock_heat_product_eq_exact clock
    (fun a b c d => R a b d c)
    (hamiltonPComponent nablaRic)
    (hamiltonMComponent clock R Ric
      (fun a b => ∑ e, nablaP e e a b))
    (fun a b c d => hamiltonRmReactionComponent R a b d c)
    (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
    (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
      (fun a b => ∑ e, nablaP e e a b))
    (fun e a b c d => nablaR e a b d c) nablaP nablaM
    (hamiltonTestJetDU clock Ric
      (fun a b => if a = b then 1 else 0) W)
    phi Lphi psi psi' U W hU
    (hamiltonTestJetDU_skew clock Ric
      (fun a b => if a = b then 1 else 0) W)]
  rw [hamiltonBlock_heat_product_eq_j_add_sigma_square clock
    R Ric nablaR nablaRic nablaP nablaM U W hRm hNablaRm hRic
    hNablaRic hTrace hContract hNablaPSkew hM hU]

theorem exists_hamiltonPerturbedBlock_control_constant
    (B S : Real) :
    exists C : Real, 0 <= C ∧
      2 * (B + 1) * (Fintype.card Idx : Real) ^ 3 <= C ∧
      2 * B * S * (Fintype.card Idx : Real) ^ 3 +
          4 * B * S ^ 2 * (Fintype.card Idx : Real) ^ 4 +
          B * S ^ 2 * (Fintype.card Idx : Real) ^ 2 +
          4 * B ^ 2 * S ^ 2 * (Fintype.card Idx : Real) ^ 2 +
          (Fintype.card Idx : Real) ^ 2 <= C ∧
      4 * B * (Fintype.card Idx : Real) ^ 3 +
          (8 * B + 4) * (Fintype.card Idx : Real) ^ 4 +
          B * (Fintype.card Idx : Real) +
          2 * B * (Fintype.card Idx : Real) ^ 2 + 1 <= C := by
  let N : Real := Fintype.card Idx
  let cPhi := 2 * (B + 1) * N ^ 3
  let cPsiW := 2 * B * S * N ^ 3 + 4 * B * S ^ 2 * N ^ 4 +
    B * S ^ 2 * N ^ 2 + 4 * B ^ 2 * S ^ 2 * N ^ 2 + N ^ 2
  let cPsiU := 4 * B * N ^ 3 + (8 * B + 4) * N ^ 4 +
    B * N + 2 * B * N ^ 2 + 1
  let C := max 0 (max cPhi (max cPsiW cPsiU))
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · exact (le_max_left cPhi (max cPsiW cPsiU)).trans
      (le_max_right 0 (max cPhi (max cPsiW cPsiU)))
  · exact ((le_max_left cPsiW cPsiU).trans
      (le_max_right cPhi (max cPsiW cPsiU))).trans
        (le_max_right 0 (max cPhi (max cPsiW cPsiU)))
  · exact ((le_max_right cPsiW cPsiU).trans
      (le_max_right cPhi (max cPsiW cPsiU))).trans
        (le_max_right 0 (max cPhi (max cPsiW cPsiU)))

theorem hamiltonPerturbedBlock_heat_product_ge
    [DecidableEq Idx]
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaM : Idx -> Idx -> Idx -> Real)
    (phi Lphi psi psi' B S C : Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hRm : Rm04Symm R)
    (hNablaRm : forall e, Rm04PairSymm (nablaR e))
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hContract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hNablaPSkew : forall e a b c,
      nablaP e a b c = -nablaP e b a c)
    (hM : forall a b,
      hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) a b =
        hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) b a)
    (hU : forall a b, U a b = -U b a)
    (hB : 0 <= B) (hphi : 0 <= phi)
    (hpsi : 0 <= psi) (hpsi1 : psi <= 1)
    (helapsed : clock.elapsed <= S)
    (hRBound : forall a b c d, |R a b c d| <= B)
    (hPBound : forall a b c,
      |hamiltonPComponent nablaRic a b c| <= B)
    (hMBound : forall a b,
      |hamiltonMComponent clock R Ric
        (fun i j => ∑ e, nablaP e e i j) a b| <= B / clock.elapsed)
    (hRicBound : forall a b, |Ric a b| <= B)
    (hCphi :
      2 * (B + 1) * (Fintype.card Idx : Real) ^ 3 <= C)
    (hCpsiW :
      2 * B * S * (Fintype.card Idx : Real) ^ 3 +
          4 * B * S ^ 2 * (Fintype.card Idx : Real) ^ 4 +
          B * S ^ 2 * (Fintype.card Idx : Real) ^ 2 +
          4 * B ^ 2 * S ^ 2 * (Fintype.card Idx : Real) ^ 2 +
          (Fintype.card Idx : Real) ^ 2 <= C)
    (hCpsiU :
      4 * B * (Fintype.card Idx : Real) ^ 3 +
          (8 * B + 4) * (Fintype.card Idx : Real) ^ 4 +
          B * (Fintype.card Idx : Real) +
          2 * B * (Fintype.card Idx : Real) ^ 2 + 1 <= C) :
    hamiltonBlockHeatProduct
        (hamiltonPerturbedCurvatureBlock
          (fun a b c d => R a b d c) psi)
        (hamiltonPComponent nablaRic)
        (hamiltonPerturbedMBlock clock
          (hamiltonMComponent clock R Ric
            (fun a b => ∑ e, nablaP e e a b)) phi)
        (hamiltonPerturbedCurvatureBlock
          (fun a b c d => hamiltonRmReactionComponent R a b d c) psi')
        (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
        (hamiltonPerturbedMBlock clock
          (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
            (fun a b => ∑ e, nablaP e e a b))
          (Lphi - phi / clock.elapsed))
        (fun e a b c d => nablaR e a b d c) nablaP nablaM
        (hamiltonTestJetDU clock Ric
          (fun a b => if a = b then 1 else 0) W)
        (fun _ => 0) (fun _ _ => 0)
        (fun a => (1 / clock.elapsed) * W a) U W >=
      hamiltonBlockJ
          (hamiltonPerturbedCurvatureBlock
            (fun a b c d => R a b d c) psi)
          (hamiltonPComponent nablaRic)
          (hamiltonPerturbedMBlock clock
            (hamiltonMComponent clock R Ric
              (fun a b => ∑ e, nablaP e e a b)) phi) U W +
        hamiltonBlockSigmaSquare
          (hamiltonPerturbedCurvatureBlock
            (fun a b c d => R a b d c) psi)
          (hamiltonPComponent nablaRic) U W +
        (Lphi / clock.elapsed + phi / clock.elapsed ^ 2 -
            C * psi / clock.elapsed ^ 2 - C * phi / clock.elapsed) *
          (∑ a, (W a) ^ 2) +
        (psi' - C * psi) * (∑ a, ∑ b, (U a b) ^ 2) := by
  let K : Idx -> Idx -> Idx -> Idx -> Real := fun a b c d => R a b d c
  let P : Idx -> Idx -> Idx -> Real := hamiltonPComponent nablaRic
  let M : Idx -> Idx -> Real := hamiltonMComponent clock R Ric
    (fun a b => ∑ e, nablaP e e a b)
  let dK : Idx -> Idx -> Idx -> Idx -> Real :=
    hamiltonMetricCurvatureBlockPerturbation psi
  let dM : Idx -> Idx -> Real := fun a b =>
    hamiltonPerturbedMBlock clock M phi a b - M a b
  let W2 := ∑ a, (W a) ^ 2
  let U2 := ∑ a, ∑ b, (U a b) ^ 2
  let D2 := ∑ e, ∑ a, ∑ b,
    (hamiltonTestJetDU clock Ric
      (fun i j => if i = j then 1 else 0) W e a b) ^ 2
  let J0 := hamiltonBlockJ K P M U W
  let Jh := hamiltonBlockJ
    (hamiltonPerturbedCurvatureBlock K psi) P
    (hamiltonPerturbedMBlock clock M phi) U W
  let Q0 := hamiltonBlockSigmaSquare K P U W
  let Qh := hamiltonBlockSigmaSquare
    (hamiltonPerturbedCurvatureBlock K psi) P U W
  let N : Real := Fintype.card Idx
  let cPhi := 2 * (B + 1) * N ^ 3
  let cPsiJ := 2 * B * S * N ^ 3 + 4 * B * S ^ 2 * N ^ 4
  let cUJ := 4 * B * N ^ 3 + (8 * B + 4) * N ^ 4
  let cSigmaW := B * S ^ 2 * N ^ 2
  let cSigmaU := B * N + 2 * B * N ^ 2 + 1
  let cJet := 4 * B ^ 2 * S ^ 2 * N ^ 2 + N ^ 2
  rw [hamiltonPerturbedBlock_heat_product_eq_j_add_sigma_square clock
    R Ric nablaR nablaRic nablaP nablaM phi Lphi psi psi' U W hRm
    hNablaRm hRic hNablaRic hTrace hContract hNablaPSkew hM hU]
  change J0 + Q0 +
      (Lphi / clock.elapsed + phi / clock.elapsed ^ 2) * W2 +
      psi' * U2 - 2 * psi * D2 >=
    Jh + Qh +
      (Lphi / clock.elapsed + phi / clock.elapsed ^ 2 -
        C * psi / clock.elapsed ^ 2 - C * phi / clock.elapsed) * W2 +
      (psi' - C * psi) * U2
  have hN : 0 <= N := by
    dsimp [N]
    positivity
  have hphiTau : 0 <= phi / clock.elapsed :=
    div_nonneg hphi clock.elapsed_pos.le
  have hpsiTauSq : 0 <= psi / clock.elapsed ^ 2 :=
    div_nonneg hpsi (sq_nonneg _)
  have hW2 : 0 <= W2 := by
    exact Finset.sum_nonneg fun a _ => sq_nonneg _
  have hU2 : 0 <= U2 := by
    exact Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => sq_nonneg _
  have hBM : 0 <= B / clock.elapsed :=
    div_nonneg hB clock.elapsed_pos.le
  have hBdM : 0 <= phi / clock.elapsed := hphiTau
  have hdK : forall a b c d, |dK a b c d| <= psi := by
    intro a b c d
    exact metric_curvature_block_perturbation_abs_le psi hpsi a b c d
  have hdM : forall a b, |dM a b| <= phi / clock.elapsed := by
    intro a b
    exact perturbed_m_block_sub_abs_le clock M phi hphi a b
  have hK : forall a b c d, |K a b c d| <= B := by
    intro a b c d
    exact hRBound a b d c
  have hP : forall a b c, |P a b c| <= B := hPBound
  have hMbase : forall a b, |M a b| <= B / clock.elapsed := hMBound
  have hJabs :
      |Jh - J0| <=
        (2 * (B * (phi / clock.elapsed) +
              psi * (B / clock.elapsed) +
              psi * (phi / clock.elapsed)) * N ^ 3 +
            4 * psi * B * N ^ 4) * W2 +
          (4 * psi * B * N ^ 3 +
            (8 * B * psi + 4 * psi ^ 2) * N ^ 4) * U2 := by
    have hraw := hamiltonBlockJ_add_blocks_abs_sub_le K dK P M dM U W
        B B (B / clock.elapsed) psi (phi / clock.elapsed)
        hB hB hBM hpsi hBdM hK hP hMbase hdK hdM
    have hKfun :
        (fun a b c d => K a b c d + dK a b c d) =
          hamiltonPerturbedCurvatureBlock K psi := by
      rfl
    have hMfun :
        (fun a b => M a b + dM a b) =
          hamiltonPerturbedMBlock clock M phi := by
      funext a b
      dsimp [dM]
      ring
    rw [hKfun, hMfun] at hraw
    simpa only [Jh, J0, N, W2, U2] using hraw
  have hJW := perturbation_reaction_w_coefficient_le
    clock.elapsed S B N phi psi clock.elapsed_pos helapsed hB hN hphi
      hpsi hpsi1
  have hJU := perturbation_reaction_u_coefficient_le B N psi hpsi hpsi1
  have hJerr :
      |Jh - J0| <=
        (cPhi * (phi / clock.elapsed) +
            cPsiJ * (psi / clock.elapsed ^ 2)) * W2 +
          psi * cUJ * U2 := by
    calc
      |Jh - J0| <=
          (2 * (B * (phi / clock.elapsed) +
                psi * (B / clock.elapsed) +
                psi * (phi / clock.elapsed)) * N ^ 3 +
              4 * psi * B * N ^ 4) * W2 +
            (4 * psi * B * N ^ 3 +
              (8 * B * psi + 4 * psi ^ 2) * N ^ 4) * U2 := hJabs
      _ <= (cPhi * (phi / clock.elapsed) +
              cPsiJ * (psi / clock.elapsed ^ 2)) * W2 +
            psi * cUJ * U2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hJW hW2)
          (mul_le_mul_of_nonneg_right hJU hU2)
  have hJdelta : Jh - J0 <=
      (cPhi * (phi / clock.elapsed) +
          cPsiJ * (psi / clock.elapsed ^ 2)) * W2 +
        psi * cUJ * U2 :=
    (le_abs_self (Jh - J0)).trans hJerr
  have hQabs :
      |Qh - Q0| <=
        psi * B * N ^ 2 * W2 +
          psi * (B * N + 2 * B * N ^ 2 + 1) * U2 := by
    simpa only [Qh, Q0, K, P, N, W2, U2] using
      hamiltonBlockSigmaSquare_perturbed_abs_sub_le K P psi U W B B
        hB hB hpsi hpsi1 hK hP hU
  have hpsiClock : psi <= S ^ 2 * (psi / clock.elapsed ^ 2) := by
    have htauSq : 0 < clock.elapsed ^ 2 := sq_pos_of_pos clock.elapsed_pos
    have htauSqS : clock.elapsed ^ 2 <= S ^ 2 := by
      nlinarith [clock.elapsed_pos]
    calc
      psi = (clock.elapsed ^ 2 * psi) / clock.elapsed ^ 2 := by
        field_simp [clock.elapsed_ne_zero]
      _ <= (S ^ 2 * psi) / clock.elapsed ^ 2 := by
        apply (div_le_div_iff_of_pos_right htauSq).2
        exact mul_le_mul_of_nonneg_right htauSqS hpsi
      _ = S ^ 2 * (psi / clock.elapsed ^ 2) := by ring
  have hSigmaW :
      psi * B * N ^ 2 <= cSigmaW * (psi / clock.elapsed ^ 2) := by
    have hscale : 0 <= B * N ^ 2 := mul_nonneg hB (sq_nonneg N)
    have hscaled := mul_le_mul_of_nonneg_right hpsiClock hscale
    dsimp [cSigmaW]
    convert hscaled using 1 <;> first | rfl | ring
  have hQerr :
      |Qh - Q0| <=
        cSigmaW * (psi / clock.elapsed ^ 2) * W2 +
          psi * cSigmaU * U2 := by
    calc
      |Qh - Q0| <=
          psi * B * N ^ 2 * W2 +
            psi * (B * N + 2 * B * N ^ 2 + 1) * U2 := hQabs
      _ <= cSigmaW * (psi / clock.elapsed ^ 2) * W2 +
            psi * cSigmaU * U2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hSigmaW hW2)
          (le_refl _)
  have hQdelta : Qh - Q0 <=
      cSigmaW * (psi / clock.elapsed ^ 2) * W2 +
        psi * cSigmaU * U2 :=
    (le_abs_self (Qh - Q0)).trans hQerr
  have hD2 :
      D2 <=
        (2 * B ^ 2 + 1 / (2 * clock.elapsed ^ 2)) * N ^ 2 * W2 := by
    simpa only [D2, N, W2] using
      hamiltonTestJetDU_sq_sum_le clock Ric W B hB hRicBound
  have hJetCoefficient := perturbation_jet_coefficient_le
    clock.elapsed S B N psi clock.elapsed_pos helapsed hpsi
  have hDerr :
      2 * psi * D2 <=
        cJet * (psi / clock.elapsed ^ 2) * W2 := by
    calc
      2 * psi * D2 <=
          2 * psi *
            ((2 * B ^ 2 + 1 / (2 * clock.elapsed ^ 2)) * N ^ 2 * W2) :=
        mul_le_mul_of_nonneg_left hD2 (mul_nonneg (by norm_num) hpsi)
      _ = (2 * psi *
          ((2 * B ^ 2 + 1 / (2 * clock.elapsed ^ 2)) * N ^ 2)) * W2 := by
        ring
      _ <= cJet * (psi / clock.elapsed ^ 2) * W2 := by
        exact mul_le_mul_of_nonneg_right hJetCoefficient hW2
  have htotal := add_le_add (add_le_add hJdelta hQdelta) hDerr
  have htotal' :
      (Jh - J0) + (Qh - Q0) + 2 * psi * D2 <=
        cPhi * (phi / clock.elapsed) * W2 +
          (cPsiJ + cSigmaW + cJet) *
            (psi / clock.elapsed ^ 2) * W2 +
          (cUJ + cSigmaU) * psi * U2 := by
    convert htotal using 1 <;> first | rfl | ring
  have hCphi' : cPhi <= C := by
    simpa only [cPhi, N] using hCphi
  have hCpsiW' : cPsiJ + cSigmaW + cJet <= C := by
    simpa only [cPsiJ, cSigmaW, cJet, N, add_assoc] using hCpsiW
  have hCpsiU' : cUJ + cSigmaU <= C := by
    simpa only [cUJ, cSigmaU, N, add_assoc] using hCpsiU
  have hCphiScaled :
      cPhi * (phi / clock.elapsed) * W2 <=
        C * (phi / clock.elapsed) * W2 := by
    have hscale : 0 <= (phi / clock.elapsed) * W2 :=
      mul_nonneg hphiTau hW2
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hCphi' hscale
  have hCpsiWScaled :
      (cPsiJ + cSigmaW + cJet) *
          (psi / clock.elapsed ^ 2) * W2 <=
        C * (psi / clock.elapsed ^ 2) * W2 := by
    have hscale : 0 <= (psi / clock.elapsed ^ 2) * W2 :=
      mul_nonneg hpsiTauSq hW2
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hCpsiW' hscale
  have hCpsiUScaled :
      (cUJ + cSigmaU) * psi * U2 <= C * psi * U2 := by
    have hscale : 0 <= psi * U2 := mul_nonneg hpsi hU2
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hCpsiU' hscale
  have hCtotal := add_le_add (add_le_add hCphiScaled hCpsiWScaled)
    hCpsiUScaled
  have herrors := htotal'.trans hCtotal
  have hnonneg :
      0 <= C * (phi / clock.elapsed) * W2 +
          C * (psi / clock.elapsed ^ 2) * W2 + C * psi * U2 -
        ((Jh - J0) + (Qh - Q0) + 2 * psi * D2) :=
    sub_nonneg.mpr herrors
  have hfinal :
      Jh + Qh +
          (Lphi / clock.elapsed + phi / clock.elapsed ^ 2 -
            C * psi / clock.elapsed ^ 2 - C * phi / clock.elapsed) * W2 +
          (psi' - C * psi) * U2 <=
        J0 + Q0 +
          (Lphi / clock.elapsed + phi / clock.elapsed ^ 2) * W2 +
          psi' * U2 - 2 * psi * D2 := by
    rw [← sub_nonneg]
    convert hnonneg using 1
    all_goals first | rfl | ring
  exact hfinal

theorem hamiltonBlock_coefficient_bounds
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nabla2R : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (A0 A1 A2 S : Real)
    (hA0 : 0 <= A0) (hA1 : 0 <= A1) (hA2 : 0 <= A2)
    (hS : 0 <= S) (helapsed : clock.elapsed <= S)
    (hRBound : forall a b c d, |R a b c d| <= A0)
    (hNablaRBound : forall e a b c d, |nablaR e a b c d| <= A1)
    (hNabla2RBound : forall e f a b c d, |nabla2R e f a b c d| <= A2)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hContract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hDifferentiatedDiv : differentiatedCurvatureDivergenceComponents nabla2R nablaP) :
    let N : Real := Fintype.card Idx
    let B := A0 + N * A1 + N * A0 +
      S * (N ^ 2 * A2 + N ^ 3 * A0 ^ 2) + N * A0 / 2
    0 <= B ∧
      (forall a b c d, |R a b c d| <= B) ∧
      (forall a b c, |hamiltonPComponent nablaRic a b c| <= B) ∧
      (forall a b,
        |hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) a b| <= B / clock.elapsed) ∧
      (forall a b, |Ric a b| <= B) := by
  let N : Real := Fintype.card Idx
  let C0 := N ^ 2 * A2 + N ^ 3 * A0 ^ 2
  let D0 := N * A0 / 2
  let B := A0 + N * A1 + N * A0 + S * C0 + D0
  change 0 <= B ∧
    (forall a b c d, |R a b c d| <= B) ∧
    (forall a b c, |hamiltonPComponent nablaRic a b c| <= B) ∧
    (forall a b,
      |hamiltonMComponent clock R Ric
        (fun i j => ∑ e, nablaP e e i j) a b| <= B / clock.elapsed) ∧
    (forall a b, |Ric a b| <= B)
  have hN : 0 <= N := by
    dsimp [N]
    positivity
  have hC0 : 0 <= C0 := by
    dsimp [C0]
    positivity
  have hD0 : 0 <= D0 := by
    dsimp [D0]
    positivity
  have hB : 0 <= B := by
    dsimp [B]
    positivity
  have hRic0 : forall a b, |Ric a b| <= N * A0 := by
    intro a b
    rw [← hTrace a b]
    simpa only [N] using
      DifferentialGeometry.Tensor0SBundle.abs_sum_le_card_mul_of_bound
        (fun e : Idx => R e a b e) A0 (fun e => hRBound e a b e)
  have hP0 : forall a b c,
      |hamiltonPComponent nablaRic a b c| <= N * A1 := by
    intro a b c
    have hP : hamiltonPComponent nablaRic a b c =
        ∑ e : Idx, nablaR e e c b a := by
      unfold hamiltonPComponent
      calc
        nablaRic a b c - nablaRic b a c =
            nablaRic a c b - nablaRic b c a := by
          rw [hNablaRic a b c, hNablaRic b a c]
        _ = ∑ e : Idx, nablaR e e c b a := (hContract c a b).symm
    rw [hP]
    simpa only [N] using
      DifferentialGeometry.Tensor0SBundle.abs_sum_le_card_mul_of_bound
        (fun e : Idx => nablaR e e c b a) A1
        (fun e => hNablaRBound e e c b a)
  have hDivP : forall a b,
      |∑ e : Idx, nablaP e e a b| <= N ^ 2 * A2 := by
    intro a b
    have hDiv : (∑ e : Idx, nablaP e e a b) =
        ∑ e : Idx, ∑ c : Idx, nabla2R e c c b a e := by
      apply Finset.sum_congr rfl
      intro e _
      exact (hDifferentiatedDiv e b a e).symm
    rw [hDiv]
    have hbound :=
      DifferentialGeometry.Tensor0SBundle.abs_double_sum_le_card_mul_card_mul_of_bound
        (fun e c : Idx => nabla2R e c c b a e) A2
        (fun e c => hNabla2RBound e c c b a e)
    simpa only [N, pow_two] using hbound
  have hCurvRic : forall a b,
      |hamiltonCurvatureRicciComponent R Ric a b| <= N ^ 3 * A0 ^ 2 := by
    intro a b
    unfold hamiltonCurvatureRicciComponent
    have hbound :=
      DifferentialGeometry.Tensor0SBundle.abs_double_sum_le_card_mul_card_mul_of_bound
        (fun c d : Idx => R a c d b * Ric c d) (A0 * (N * A0)) (by
          intro c d
          rw [abs_mul]
          exact mul_le_mul (hRBound a c d b) (hRic0 c d)
            (abs_nonneg _) hA0)
    calc
      |∑ c : Idx, ∑ d : Idx, R a c d b * Ric c d| <=
          N * N * (A0 * (N * A0)) := by
        simpa only [N] using hbound
      _ = N ^ 3 * A0 ^ 2 := by ring
  have hShift : forall a b,
      |(1 / (2 * clock.elapsed)) * Ric a b| <= D0 / clock.elapsed := by
    intro a b
    rw [abs_mul, abs_of_pos (one_div_pos.mpr (mul_pos (by norm_num)
      clock.elapsed_pos))]
    calc
      1 / (2 * clock.elapsed) * |Ric a b| <=
          1 / (2 * clock.elapsed) * (N * A0) :=
        mul_le_mul_of_nonneg_left (hRic0 a b)
          (one_div_nonneg.mpr (mul_nonneg (by norm_num) clock.elapsed_pos.le))
      _ = D0 / clock.elapsed := by
        dsimp [D0]
        field_simp [ne_of_gt clock.elapsed_pos]
  have hM0 : forall a b,
      |hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) a b| <=
        C0 + D0 / clock.elapsed := by
    intro a b
    unfold hamiltonMComponent
    calc
      |(∑ e : Idx, nablaP e e a b) +
          hamiltonCurvatureRicciComponent R Ric a b +
          (1 / (2 * clock.elapsed)) * Ric a b| <=
          |∑ e : Idx, nablaP e e a b| +
            |hamiltonCurvatureRicciComponent R Ric a b| +
            |(1 / (2 * clock.elapsed)) * Ric a b| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) (le_refl _))
      _ <= N ^ 2 * A2 + N ^ 3 * A0 ^ 2 + D0 / clock.elapsed := by
        exact add_le_add (add_le_add (hDivP a b) (hCurvRic a b)) (hShift a b)
      _ = C0 + D0 / clock.elapsed := by rfl
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · intro a b c d
    exact (hRBound a b c d).trans (by
      dsimp [B]
      nlinarith [mul_nonneg hN hA1, mul_nonneg hN hA0,
        mul_nonneg hS hC0, hD0])
  · intro a b c
    exact (hP0 a b c).trans (by
      dsimp [B]
      nlinarith [hA0, mul_nonneg hN hA0, mul_nonneg hS hC0, hD0])
  · intro a b
    apply (le_div_iff₀ clock.elapsed_pos).2
    calc
      |hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) a b| * clock.elapsed <=
          (C0 + D0 / clock.elapsed) * clock.elapsed :=
        mul_le_mul_of_nonneg_right (hM0 a b) clock.elapsed_pos.le
      _ = clock.elapsed * C0 + D0 := by
        field_simp [ne_of_gt clock.elapsed_pos]
      _ <= S * C0 + D0 := by
        simpa only [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_right helapsed hC0) D0
      _ <= B := by
        dsimp [B]
        nlinarith [hA0, mul_nonneg hN hA1, mul_nonneg hN hA0]
  · intro a b
    exact (hRic0 a b).trans (by
      dsimp [B]
      nlinarith [hA0, mul_nonneg hN hA1, mul_nonneg hS hC0, hD0])

end DifferentialGeometry.PDE.RicciFlow
