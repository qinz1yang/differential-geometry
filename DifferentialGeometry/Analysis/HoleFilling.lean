import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open Filter

namespace DifferentialGeometry.Analysis

theorem weighted_young_inequality
    {a x alpha beta theta : ℝ}
    (ha : 0 ≤ a) (hx : 0 ≤ x)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (halphaBeta : alpha + beta = 1) (htheta : 0 < theta) :
    a * x ^ beta ≤
      alpha * (a * (beta / theta) ^ beta) ^ (1 / alpha) + theta * x := by
  let y := (a * (beta / theta) ^ beta) ^ (1 / alpha)
  let z := theta / beta * x
  have hbetaTheta : 0 ≤ beta / theta := div_nonneg hbeta.le htheta.le
  have hthetaBeta : 0 ≤ theta / beta := div_nonneg htheta.le hbeta.le
  have hy : 0 ≤ y := Real.rpow_nonneg (mul_nonneg ha (Real.rpow_nonneg hbetaTheta _)) _
  have hz : 0 ≤ z := mul_nonneg hthetaBeta hx
  have hyPow : y ^ alpha = a * (beta / theta) ^ beta := by
    dsimp only [y]
    rw [← Real.rpow_mul (mul_nonneg ha (Real.rpow_nonneg hbetaTheta _))]
    field_simp [halpha.ne']
    rw [Real.rpow_one]
  have hzPow : z ^ beta = (theta / beta) ^ beta * x ^ beta := by
    exact Real.mul_rpow hthetaBeta hx
  have hratio :
      (beta / theta) ^ beta * (theta / beta) ^ beta = 1 := by
    rw [← Real.mul_rpow hbetaTheta hthetaBeta]
    have hmul : beta / theta * (theta / beta) = 1 := by
      field_simp [halpha.ne', hbeta.ne', htheta.ne']
    rw [hmul, Real.one_rpow]
  have hgeom := Real.geom_mean_le_arith_mean2_weighted
    halpha.le hbeta.le hy hz halphaBeta
  calc
    a * x ^ beta = y ^ alpha * z ^ beta := by
      rw [hyPow, hzPow]
      calc
        a * x ^ beta =
            a * ((beta / theta) ^ beta * (theta / beta) ^ beta) * x ^ beta := by
          rw [hratio, mul_one]
        _ = a * (beta / theta) ^ beta * ((theta / beta) ^ beta * x ^ beta) := by ring
    _ ≤ alpha * y + beta * z := hgeom
    _ = alpha * (a * (beta / theta) ^ beta) ^ (1 / alpha) + theta * x := by
      dsimp only [y, z]
      field_simp [hbeta.ne']

theorem geometric_hole_filling
    {X : ℕ → ℝ} {theta A B : ℝ}
    (hX_bdd : BddAbove (Set.range X))
    (htheta : 0 ≤ theta) (hB : 1 ≤ B) (hA : 0 ≤ A)
    (hthetaB : theta * B < 1)
    (hstep : ∀ k, X k ≤ theta * X (k + 1) + A * B ^ k) :
    X 0 ≤ A / (1 - theta * B) := by
  have htheta_one : theta < 1 := by
    calc
      theta = theta * 1 := (mul_one theta).symm
      _ ≤ theta * B := mul_le_mul_of_nonneg_left hB htheta
      _ < 1 := hthetaB
  have hratio_nonneg : 0 ≤ theta * B :=
    mul_nonneg htheta (le_trans zero_le_one hB)
  have hratio_summable : Summable (fun k : ℕ ↦ (theta * B) ^ k) :=
    summable_geometric_of_lt_one hratio_nonneg hthetaB
  obtain ⟨K, hK⟩ := hX_bdd
  have hfinite : ∀ m : ℕ,
      X 0 ≤ theta ^ m * X m + A * ∑ k ∈ Finset.range m, (theta * B) ^ k := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
        calc
          X 0 ≤ theta ^ m * X m + A * ∑ k ∈ Finset.range m, (theta * B) ^ k := hm
          _ ≤ theta ^ m * (theta * X (m + 1) + A * B ^ m) +
                A * ∑ k ∈ Finset.range m, (theta * B) ^ k := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hstep m) (pow_nonneg htheta m)) le_rfl
          _ = theta ^ (m + 1) * X (m + 1) +
                A * ∑ k ∈ Finset.range (m + 1), (theta * B) ^ k := by
            rw [Finset.sum_range_succ, pow_succ theta, mul_pow]
            ring
  have hbound : ∀ m : ℕ,
      X 0 ≤ theta ^ m * K + A * (1 - theta * B)⁻¹ := by
    intro m
    calc
      X 0 ≤ theta ^ m * X m + A * ∑ k ∈ Finset.range m, (theta * B) ^ k :=
        hfinite m
      _ ≤ theta ^ m * K + A * ∑ k ∈ Finset.range m, (theta * B) ^ k := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hK (Set.mem_range_self m)) (pow_nonneg htheta m)) le_rfl
      _ ≤ theta ^ m * K + A * ∑' k : ℕ, (theta * B) ^ k := by
        gcongr
        exact hratio_summable.sum_le_tsum (Finset.range m)
          (fun k _ ↦ pow_nonneg hratio_nonneg k)
      _ = theta ^ m * K + A * (1 - theta * B)⁻¹ := by
        rw [tsum_geometric_of_lt_one hratio_nonneg hthetaB]
  have htendsto : Tendsto
      (fun m : ℕ ↦ theta ^ m * K + A * (1 - theta * B)⁻¹)
      atTop (nhds (A * (1 - theta * B)⁻¹)) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one htheta htheta_one).mul_const K).add_const
        (A * (1 - theta * B)⁻¹)
  have hlimit : X 0 ≤ A * (1 - theta * B)⁻¹ :=
    ge_of_tendsto htendsto (Filter.Eventually.of_forall hbound)
  simpa only [div_eq_mul_inv] using hlimit

theorem weighted_geometric_hole_filling
    {X coefficient : ℕ → ℝ} {alpha beta theta A B : ℝ}
    (hX_bdd : BddAbove (Set.range X))
    (hX_nonneg : ∀ k, 0 ≤ X k) (hcoefficient_nonneg : ∀ k, 0 ≤ coefficient k)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (halphaBeta : alpha + beta = 1) (htheta : 0 < theta)
    (hB : 1 ≤ B) (hA : 0 ≤ A) (hthetaB : theta * B < 1)
    (hcoefficient : ∀ k,
      alpha * (coefficient k * (beta / theta) ^ beta) ^ (1 / alpha) ≤ A * B ^ k)
    (hstep : ∀ k, X k ≤ coefficient k * X (k + 1) ^ beta) :
    X 0 ≤ A / (1 - theta * B) := by
  apply geometric_hole_filling hX_bdd htheta.le hB hA hthetaB
  intro k
  calc
    X k ≤ coefficient k * X (k + 1) ^ beta := hstep k
    _ ≤ alpha * (coefficient k * (beta / theta) ^ beta) ^ (1 / alpha) +
          theta * X (k + 1) :=
      weighted_young_inequality (hcoefficient_nonneg k) (hX_nonneg (k + 1))
        halpha hbeta halphaBeta htheta
    _ ≤ theta * X (k + 1) + A * B ^ k := by
      rw [add_comm]
      exact add_le_add le_rfl (hcoefficient k)

theorem nnreal_affine_geometric_hole_filling
    {X data factor : ℕ → NNReal} {theta A B : NNReal}
    (hX_bdd : BddAbove (Set.range X)) (hB : 1 ≤ B)
    (hthetaB : theta * B < 1)
    (hfactor : ∀ k, factor k ≤ theta)
    (hdata : ∀ k, data k ≤ A * B ^ k)
    (hstep : ∀ k, X k ≤ data k + factor k * X (k + 1)) :
    X 0 ≤ A / (1 - theta * B) := by
  obtain ⟨K, hK⟩ := hX_bdd
  have hXreal : BddAbove (Set.range (fun k ↦ (X k : Real))) := by
    refine ⟨K, ?_⟩
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    exact_mod_cast hK (Set.mem_range_self k)
  have hreal := geometric_hole_filling hXreal theta.coe_nonneg
    (by exact_mod_cast hB) A.coe_nonneg (by exact_mod_cast hthetaB) (fun k ↦ ?_)
  · apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_div, NNReal.coe_sub hthetaB.le,
      NNReal.coe_one, NNReal.coe_mul] using hreal
  · calc
      (X k : Real) ≤ data k + factor k * X (k + 1) := by
        exact_mod_cast hstep k
      _ ≤ theta * X (k + 1) + A * B ^ k := by
        rw [add_comm]
        gcongr
        · exact_mod_cast hfactor k
        · exact_mod_cast hdata k

theorem summable_hole_filling
    {X cost : ℕ → ℝ} {theta : ℝ}
    (hX_bdd : BddAbove (Set.range X))
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (hcost_nonneg : ∀ k, 0 ≤ cost k)
    (hcost : Summable (fun k : ℕ ↦ theta ^ k * cost k))
    (hstep : ∀ k, X k ≤ theta * X (k + 1) + cost k) :
    X 0 ≤ ∑' k : ℕ, theta ^ k * cost k := by
  obtain ⟨K, hK⟩ := hX_bdd
  have hfinite : ∀ m : ℕ,
      X 0 ≤ theta ^ m * X m + ∑ k ∈ Finset.range m, theta ^ k * cost k := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
        calc
          X 0 ≤ theta ^ m * X m +
              ∑ k ∈ Finset.range m, theta ^ k * cost k := hm
          _ ≤ theta ^ m * (theta * X (m + 1) + cost m) +
              ∑ k ∈ Finset.range m, theta ^ k * cost k := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hstep m) (pow_nonneg htheta m)) le_rfl
          _ = theta ^ (m + 1) * X (m + 1) +
              ∑ k ∈ Finset.range (m + 1), theta ^ k * cost k := by
            rw [Finset.sum_range_succ, pow_succ]
            ring
  have hbound : ∀ m : ℕ,
      X 0 ≤ theta ^ m * K + ∑' k : ℕ, theta ^ k * cost k := by
    intro m
    calc
      X 0 ≤ theta ^ m * X m +
          ∑ k ∈ Finset.range m, theta ^ k * cost k := hfinite m
      _ ≤ theta ^ m * K +
          ∑ k ∈ Finset.range m, theta ^ k * cost k := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hK (Set.mem_range_self m))
            (pow_nonneg htheta m)) le_rfl
      _ ≤ theta ^ m * K + ∑' k : ℕ, theta ^ k * cost k := by
        gcongr
        exact hcost.sum_le_tsum (Finset.range m)
          (fun k _ ↦ mul_nonneg (pow_nonneg htheta k) (hcost_nonneg k))
  have htendsto : Tendsto
      (fun m : ℕ ↦ theta ^ m * K + ∑' k : ℕ, theta ^ k * cost k)
      atTop (nhds (∑' k : ℕ, theta ^ k * cost k)) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one htheta htheta_one).mul_const K).add_const
        (∑' k : ℕ, theta ^ k * cost k)
  exact ge_of_tendsto htendsto (Filter.Eventually.of_forall hbound)

theorem weighted_summable_hole_filling
    {X coefficient : ℕ → ℝ} {alpha beta theta : ℝ}
    (hX_bdd : BddAbove (Set.range X))
    (hX_nonneg : ∀ k, 0 ≤ X k) (hcoefficient_nonneg : ∀ k, 0 ≤ coefficient k)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (halphaBeta : alpha + beta = 1) (htheta : 0 < theta) (htheta_one : theta < 1)
    (hsummable : Summable (fun k : ℕ ↦ theta ^ k *
      (alpha * (coefficient k * (beta / theta) ^ beta) ^ (1 / alpha))))
    (hstep : ∀ k, X k ≤ coefficient k * X (k + 1) ^ beta) :
    X 0 ≤ ∑' k : ℕ, theta ^ k *
      (alpha * (coefficient k * (beta / theta) ^ beta) ^ (1 / alpha)) := by
  apply summable_hole_filling hX_bdd htheta.le htheta_one
  · intro k
    exact mul_nonneg halpha.le
      (Real.rpow_nonneg
        (mul_nonneg (hcoefficient_nonneg k)
          (Real.rpow_nonneg (div_nonneg hbeta.le htheta.le) _)) _)
  · exact hsummable
  · intro k
    calc
      X k ≤ coefficient k * X (k + 1) ^ beta := hstep k
      _ ≤ alpha * (coefficient k * (beta / theta) ^ beta) ^ (1 / alpha) +
            theta * X (k + 1) :=
        weighted_young_inequality (hcoefficient_nonneg k) (hX_nonneg (k + 1))
          halpha hbeta halphaBeta htheta
      _ = theta * X (k + 1) +
          alpha * (coefficient k * (beta / theta) ^ beta) ^ (1 / alpha) :=
        add_comm _ _

end DifferentialGeometry.Analysis

end
