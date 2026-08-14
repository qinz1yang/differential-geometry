import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReaction
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open scoped BigOperators

def sectionalSum3 (l1 l2 l3 : Real) : Real :=
  l1 + l2 + l3

def pinchHeight3 (l3 : Real) : Real :=
  max (-l3) 0

def hamiltonIveyBarrier (K τ X : Real) : Real :=
  X * (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 3)

def reactionSectionalSum3 (l1 l2 l3 : Real) : Real :=
  DifferentialGeometry.Dim3Reaction.sectionalReaction12 l1 l2 l3 +
    DifferentialGeometry.Dim3Reaction.sectionalReaction13 l1 l2 l3 +
    DifferentialGeometry.Dim3Reaction.sectionalReaction23 l1 l2 l3

def reactionPinchHeight3 (l1 l2 l3 : Real) : Real :=
  -DifferentialGeometry.Dim3Reaction.sectionalReaction23 l1 l2 l3

private theorem hamiltonIveyBarrierLog_nonpos_of_subregion
    {K τ X : Real} (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ) (hXpos : 0 < X)
    (hXsub : X ≤ K / (1 + 2 * K * τ)) :
    Real.log (X / K) + Real.log (1 + 2 * K * τ) ≤ 0 := by
  have hquot_pos : 0 < X * (1 + 2 * K * τ) / K := by
    positivity
  have hmul : X * (1 + 2 * K * τ) ≤ K := by
    calc
      X * (1 + 2 * K * τ) ≤ (K / (1 + 2 * K * τ)) * (1 + 2 * K * τ) :=
        mul_le_mul_of_nonneg_right hXsub (le_of_lt hden)
      _ = K := by
        exact div_mul_cancel₀ K hden.ne'
  have hquot_le : X * (1 + 2 * K * τ) / K ≤ 1 := by
    rw [div_le_one hK]
    exact hmul
  have hlog : Real.log (X * (1 + 2 * K * τ) / K) ≤ Real.log 1 :=
    Real.log_le_log hquot_pos hquot_le
  have hlogmul : Real.log (X / K) + Real.log (1 + 2 * K * τ) =
      Real.log ((X / K) * (1 + 2 * K * τ)) := by
    rw [Real.log_mul (div_pos hXpos hK).ne' hden.ne']
  rw [hlogmul]
  have hquot' : (X / K) * (1 + 2 * K * τ) = X * (1 + 2 * K * τ) / K := by
    ring
  rw [hquot']
  simpa using hlog

theorem hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion
    {K τ X : Real} (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ) (hX : 0 ≤ X)
    (hXsub : X ≤ K / (1 + 2 * K * τ)) :
    hamiltonIveyBarrier K τ X ≤ -3 * X := by
  unfold hamiltonIveyBarrier
  by_cases hX0 : X = 0
  · subst hX0
    simp
  · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hX0)
    have hsum : Real.log (X / K) + Real.log (1 + 2 * K * τ) - 3 ≤ -3 := by
      have hlog := hamiltonIveyBarrierLog_nonpos_of_subregion hK hden hXpos hXsub
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum hX
    nlinarith

theorem hamiltonIveyBarrier_le_sectionalSum_of_subregion
    {K τ X S : Real} (hS : -3 * X ≤ S) (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ)
    (hX : 0 ≤ X) (hXsub : X ≤ K / (1 + 2 * K * τ)) :
    hamiltonIveyBarrier K τ X ≤ S :=
  (hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion hK hden hX hXsub).trans hS

theorem hamiltonIveyBarrier_initial_le_sectionalSum
    {K X S : Real} (hS : -3 * X ≤ S) (hK : 0 < K) (hX : 0 ≤ X) (hXK : X ≤ K) :
    hamiltonIveyBarrier K 0 X ≤ S := by
  refine hamiltonIveyBarrier_le_sectionalSum_of_subregion hS hK ?_ hX ?_
  · norm_num
  · simpa using hXK

theorem hamiltonIveyBarrier_initial_le_sectionalSum_of_ordered
    {l1 l2 l3 K : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hpinch : -K ≤ l3) (hK : 0 < K) :
    hamiltonIveyBarrier K 0 (pinchHeight3 l3) ≤ sectionalSum3 l1 l2 l3 := by
  have hS : -3 * pinchHeight3 l3 ≤ sectionalSum3 l1 l2 l3 := by
    unfold pinchHeight3 sectionalSum3
    by_cases hl3 : l3 ≤ 0
    · rw [max_eq_left (neg_nonneg.mpr hl3)]
      linarith
    · rw [max_eq_right (neg_nonpos.mpr (le_of_lt (not_le.mp hl3)))]
      linarith
  have hX : 0 ≤ pinchHeight3 l3 := by
    unfold pinchHeight3
    exact le_max_right _ _
  have hXK : pinchHeight3 l3 ≤ K := by
    unfold pinchHeight3
    by_cases hl3 : l3 ≤ 0
    · rw [max_eq_left (neg_nonneg.mpr hl3)]
      linarith
    · rw [max_eq_right (neg_nonpos.mpr (le_of_lt (not_le.mp hl3)))]
      exact le_of_lt hK
  exact hamiltonIveyBarrier_initial_le_sectionalSum hS hK hX hXK

theorem hamiltonIveyBarrier_le_sectionalSum_of_ordered_subregion
    {l1 l2 l3 K τ : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hK : 0 < K)
    (hden : 0 < 1 + 2 * K * τ) (hsub : pinchHeight3 l3 ≤ K / (1 + 2 * K * τ)) :
    hamiltonIveyBarrier K τ (pinchHeight3 l3) ≤ sectionalSum3 l1 l2 l3 := by
  have hS : -3 * pinchHeight3 l3 ≤ sectionalSum3 l1 l2 l3 := by
    unfold pinchHeight3 sectionalSum3
    by_cases hl3 : l3 ≤ 0
    · rw [max_eq_left (neg_nonneg.mpr hl3)]
      linarith
    · rw [max_eq_right (neg_nonpos.mpr (le_of_lt (not_le.mp hl3)))]
      linarith
  have hX : 0 ≤ pinchHeight3 l3 := by
    unfold pinchHeight3
    exact le_max_right _ _
  exact hamiltonIveyBarrier_le_sectionalSum_of_subregion hS hK hden hX hsub

private theorem pinchingRatioLog_core_nonneg
    {l1 l2 l3 : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0) :
    0 ≤ l1 * l2 * (l1 + l2 - l3) - l3 * (l1 ^ 2 + l2 ^ 2) := by
  let X : Real := -l3
  let a : Real := l1 - l3
  let b : Real := l2 - l3
  have hX : 0 ≤ X := by
    dsimp [X]
    exact neg_nonneg.mpr (le_of_lt hl3)
  have ha : 0 ≤ a := by
    dsimp [a]
    linarith
  have hb : 0 ≤ b := by
    dsimp [b]
    linarith
  have hX3 : 0 ≤ X ^ 3 := pow_nonneg hX 3
  have hp2 : 0 ≤ a ^ 2 * b := mul_nonneg (sq_nonneg a) hb
  have hp3 : 0 ≤ a * b ^ 2 := mul_nonneg ha (sq_nonneg b)
  have hsum : (3 : Real)⁻¹ + (3 : Real)⁻¹ + (3 : Real)⁻¹ = 1 := by norm_num
  have hamgm := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (3 : Real)⁻¹) (w₂ := (3 : Real)⁻¹) (w₃ := (3 : Real)⁻¹)
    (p₁ := X ^ 3) (p₂ := a ^ 2 * b) (p₃ := a * b ^ 2)
    (by norm_num) (by norm_num) (by norm_num) hX3 hp2 hp3 hsum
  have hpow1 : (X ^ 3) ^ ((3 : Real)⁻¹) = X :=
    Real.pow_rpow_inv_natCast hX (by norm_num : (3 : ℕ) ≠ 0)
  have hpow2 : (a ^ 2 * b) ^ ((3 : Real)⁻¹) * (a * b ^ 2) ^ ((3 : Real)⁻¹) = a * b := by
    rw [← Real.mul_rpow hp2 hp3]
    rw [show a ^ 2 * b * (a * b ^ 2) = (a * b) ^ 3 by ring]
    exact Real.pow_rpow_inv_natCast (mul_nonneg ha hb) (by norm_num : (3 : ℕ) ≠ 0)
  have hle : X * (a * b) ≤ (3 : Real)⁻¹ * (X ^ 3 + a ^ 2 * b + a * b ^ 2) := by
    have h1 := hamgm
    rw [hpow1] at h1
    rw [mul_assoc, hpow2] at h1
    convert h1 using 1
    ring
  have h3 : 3 * X * (a * b) ≤ X ^ 3 + a ^ 2 * b + a * b ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hle (by norm_num : (0 : Real) ≤ 3)
    nlinarith
  have hcore : 0 ≤ X ^ 3 - 3 * a * b * X + a * b * (a + b) := by
    nlinarith
  have heq : l1 * l2 * (l1 + l2 - l3) - l3 * (l1 ^ 2 + l2 ^ 2) =
      X ^ 3 - 3 * a * b * X + a * b * (a + b) := by
    dsimp [X, a, b]
    ring
  rw [heq]
  exact hcore

theorem pinchingRatioLog_reaction_derivative_eq
    (l1 l2 l3 : Real) :
    reactionSectionalSum3 l1 l2 l3 * (-l3)
        - sectionalSum3 l1 l2 l3 * reactionPinchHeight3 l1 l2 l3
        - reactionPinchHeight3 l1 l2 l3 * (-l3) - 2 * (-l3) ^ 3 =
      2 * (l1 * l2 * (l1 + l2 - l3) - l3 * (l1 ^ 2 + l2 ^ 2)) := by
  unfold reactionSectionalSum3 reactionPinchHeight3 sectionalSum3
    DifferentialGeometry.Dim3Reaction.sectionalReaction12
    DifferentialGeometry.Dim3Reaction.sectionalReaction13
    DifferentialGeometry.Dim3Reaction.sectionalReaction23
  ring

theorem pinchingRatioLog_reaction_derivative_ge
    {l1 l2 l3 : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0) :
    2 * (-l3) ^ 3 ≤
      reactionSectionalSum3 l1 l2 l3 * (-l3)
        - sectionalSum3 l1 l2 l3 * reactionPinchHeight3 l1 l2 l3
        - reactionPinchHeight3 l1 l2 l3 * (-l3) := by
  have hcore := pinchingRatioLog_core_nonneg h21 h32 hl3
  have heq := pinchingRatioLog_reaction_derivative_eq l1 l2 l3
  nlinarith

theorem hamiltonIveyBarrier_reaction_derivative_ge_on_boundary
    {l1 l2 l3 K τ : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hden : 0 < 1 + 2 * K * τ)
    (hboundary : hamiltonIveyBarrier K τ (-l3) = sectionalSum3 l1 l2 l3) :
    2 * (-l3) * ((-l3) - K / (1 + 2 * K * τ)) ≤
      reactionSectionalSum3 l1 l2 l3
        - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3
        - (-l3) * (2 * K / (1 + 2 * K * τ)) := by
  have hXpos : 0 < -l3 := neg_pos.mpr hl3
  have hG := pinchingRatioLog_reaction_derivative_ge h21 h32 hl3
  have hderivX : 2 * (-l3) ^ 3 ≤ reactionSectionalSum3 l1 l2 l3 * (-l3)
      - (sectionalSum3 l1 l2 l3 + (-l3)) * reactionPinchHeight3 l1 l2 l3 := by
    convert hG using 1; ring
  have hquot : sectionalSum3 l1 l2 l3 / (-l3) + 1 =
      Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2 := by
    unfold hamiltonIveyBarrier at hboundary
    have hb : sectionalSum3 l1 l2 l3 / (-l3) =
        Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 3 := by
      have hb' : sectionalSum3 l1 l2 l3 =
          (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 3) := by
        simpa [sectionalSum3] using hboundary.symm
      have hdiv := congrArg (fun t : Real => t / (-l3)) hb'
      dsimp only at hdiv
      have hshow :
          (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 3) / (-l3) =
            Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 3 := by
        rw [mul_comm]
        exact mul_div_cancel_right₀ _ hXpos.ne'
      rw [hshow] at hdiv
      exact hdiv
    linarith
  have hquot' : sectionalSum3 l1 l2 l3 + (-l3) =
      (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) := by
    have hmul := congrArg (fun t : Real => t * (-l3)) hquot
    dsimp only at hmul
    rw [add_mul, div_mul_cancel₀ _ hXpos.ne', one_mul] at hmul
    convert hmul using 1; ring
  have hquotX' :
      (sectionalSum3 l1 l2 l3 + (-l3)) * reactionPinchHeight3 l1 l2 l3 =
        (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2)
          * reactionPinchHeight3 l1 l2 l3 := by
    rw [hquot']
  have hderiv2 : 2 * (-l3) ^ 3 ≤
      (-l3) * reactionSectionalSum3 l1 l2 l3
        - (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2)
          * reactionPinchHeight3 l1 l2 l3 := by
    nlinarith [hderivX, hquotX']
  have hbase : 2 * (-l3) ^ 2 ≤ reactionSectionalSum3 l1 l2 l3
      - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3 := by
    have hd : 2 * (-l3) ^ 2 = (-l3) * (2 * (-l3) ^ 2) / (-l3) := by
      field_simp [hXpos.ne']
    rw [hd]
    exact (div_le_iff₀ hXpos).mpr (by
      convert hderiv2 using 1 <;> ring)
  have hfinal := sub_le_sub_right hbase ((-l3) * (2 * K / (1 + 2 * K * τ)))
  have hfinal' : 2 * (-l3) * ((-l3) - K / (1 + 2 * K * τ)) ≤
      reactionSectionalSum3 l1 l2 l3
        - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3
        - (-l3) * (2 * K / (1 + 2 * K * τ)) := by
    field_simp [hden.ne'] at hfinal ⊢
    nlinarith
  exact hfinal'

theorem pinchHeight_ge_one_of_normalized_boundary
    {l1 l2 l3 : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hboundary : hamiltonIveyBarrier 1 0 (-l3) = sectionalSum3 l1 l2 l3) :
    1 ≤ -l3 := by
  have hXpos : 0 < -l3 := neg_pos.mpr hl3
  have hS : -3 * (-l3) ≤ sectionalSum3 l1 l2 l3 := by
    unfold sectionalSum3
    linarith
  have hb : sectionalSum3 l1 l2 l3 = (-l3) * (Real.log (-l3) - 3) := by
    unfold hamiltonIveyBarrier at hboundary
    have hb' : sectionalSum3 l1 l2 l3 =
        (-l3) * (Real.log ((-l3) / 1) + Real.log (1 + 2 * (1 : Real) * 0) - 3) :=
      hboundary.symm
    simpa using hb'
  have hnonneg : 0 ≤ (-l3) * Real.log (-l3) := by
    nlinarith
  have hlog : 0 ≤ Real.log (-l3) := by
    exact nonneg_of_mul_nonneg_right hnonneg hXpos
  have hloge : 1 ≤ -l3 := (Real.log_nonneg_iff hXpos).mp hlog
  exact hloge

theorem hamiltonIveyBarrier_rescaled_reaction_derivative_ge_on_boundary
    {l1 l2 l3 : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hboundary : hamiltonIveyBarrier 1 0 (-l3) = sectionalSum3 l1 l2 l3) :
    2 * (-l3) ^ 2 ≤
      reactionSectionalSum3 l1 l2 l3
        - (Real.log (-l3) - 2) * reactionPinchHeight3 l1 l2 l3 := by
  have hgen := hamiltonIveyBarrier_reaction_derivative_ge_on_boundary h21 h32 hl3
    (by norm_num : 0 < 1 + 2 * (1 : Real) * 0) hboundary
  have hnorm : 2 * (-l3) * ((-l3) - 1) ≤
      reactionSectionalSum3 l1 l2 l3 - (Real.log (-l3) - 2) * reactionPinchHeight3 l1 l2 l3
        - 2 * (-l3) := by
    norm_num [Real.log_one, div_one] at hgen ⊢
    ring_nf at hgen ⊢
    exact hgen
  nlinarith

theorem reactionSectionalSum3_ge_quadratic (l1 l2 l3 : Real) :
    (4 / 3 : Real) * sectionalSum3 l1 l2 l3 ^ 2 ≤ reactionSectionalSum3 l1 l2 l3 := by
  unfold reactionSectionalSum3 sectionalSum3
    DifferentialGeometry.Dim3Reaction.sectionalReaction12
    DifferentialGeometry.Dim3Reaction.sectionalReaction13
    DifferentialGeometry.Dim3Reaction.sectionalReaction23
  nlinarith [sq_nonneg (l1 - l2), sq_nonneg (l2 - l3), sq_nonneg (l3 - l1)]

theorem hamiltonIveyBarrier_reaction_derivative_pos_on_boundary
    {l1 l2 l3 K τ : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ)
    (hboundary : hamiltonIveyBarrier K τ (-l3) = sectionalSum3 l1 l2 l3) :
    0 < reactionSectionalSum3 l1 l2 l3
        - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3
        - (-l3) * (2 * K / (1 + 2 * K * τ)) := by
  have hXpos : 0 < -l3 := neg_pos.mpr hl3
  have hgen := hamiltonIveyBarrier_reaction_derivative_ge_on_boundary h21 h32 hl3 hden hboundary
  by_cases hXsub : -l3 ≤ K / (1 + 2 * K * τ)
  · have hS' : sectionalSum3 l1 l2 l3 = -3 * (-l3) := by
      have hbar := hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion
        hK hden (neg_nonneg.mpr hl3.le) hXsub
      have hS : -3 * (-l3) ≤ sectionalSum3 l1 l2 l3 := by
        unfold sectionalSum3
        nlinarith [h21, h32]
      nlinarith [hbar, hboundary, hS]
    have hlog : Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) = 0 := by
      have hXlog : (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ)) = 0 := by
        unfold hamiltonIveyBarrier at hboundary
        nlinarith [hboundary, hS']
      exact (mul_eq_zero.mp hXlog).resolve_left hXpos.ne'
    have hXeq : -l3 = K / (1 + 2 * K * τ) := by
      have hquot : (-l3) * (1 + 2 * K * τ) / K = 1 := by
        have hlm : Real.log ((-l3) / K * (1 + 2 * K * τ)) = 0 := by
          rw [Real.log_mul (div_ne_zero hXpos.ne' hK.ne') hden.ne']
          simpa using hlog
        have heq : (-l3) / K * (1 + 2 * K * τ) = (-l3) * (1 + 2 * K * τ) / K := by ring
        rw [heq] at hlm
        rcases (Real.log_eq_zero.mp hlm) with h0 | h1 | h2
        · have hpos : 0 < (-l3) * (1 + 2 * K * τ) / K := by positivity
          linarith
        · exact h1
        · have hpos : 0 < (-l3) * (1 + 2 * K * τ) / K := by positivity
          linarith
      have hmul : (-l3) * (1 + 2 * K * τ) = K := by
        have hmul' : (-l3) * (1 + 2 * K * τ) / K * K = 1 * K :=
          congrArg (fun t : ℝ => t * K) hquot
        rw [div_mul_cancel₀ _ hK.ne', one_mul] at hmul'
        exact hmul'
      rw [eq_div_iff hden.ne']
      exact hmul
    have hl1 : l1 = l3 := by
      unfold sectionalSum3 at hS'
      have hdiff : l1 - l3 = 0 := by
        have hsum : (l1 - l3) + (l2 - l3) = 0 := by nlinarith
        have h1 : 0 ≤ l1 - l3 := by linarith
        have h2 : 0 ≤ l2 - l3 := by linarith
        nlinarith [hsum]
      linarith
    have hl2 : l2 = l3 := by
      unfold sectionalSum3 at hS'
      have hdiff : l2 - l3 = 0 := by
        have hsum : (l1 - l3) + (l2 - l3) = 0 := by nlinarith
        have h1 : 0 ≤ l1 - l3 := by linarith
        have h2 : 0 ≤ l2 - l3 := by linarith
        nlinarith [hsum]
      linarith
    have hphi : reactionSectionalSum3 l1 l2 l3
        - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3
        - (-l3) * (2 * K / (1 + 2 * K * τ)) = 2 * (-l3) ^ 2 := by
      rw [hl1, hl2, hlog]
      have h1 : reactionSectionalSum3 l3 l3 l3 = 12 * l3 ^ 2 := by
        unfold reactionSectionalSum3
          DifferentialGeometry.Dim3Reaction.sectionalReaction12
          DifferentialGeometry.Dim3Reaction.sectionalReaction13
          DifferentialGeometry.Dim3Reaction.sectionalReaction23
        ring
      have h2 : reactionPinchHeight3 l3 l3 l3 = -4 * l3 ^ 2 := by
        unfold reactionPinchHeight3
          DifferentialGeometry.Dim3Reaction.sectionalReaction23
        ring
      rw [h1, h2]
      have h3 : 12 * l3 ^ 2 - (0 - 2) * (-4 * l3 ^ 2) - (-l3) * (2 * K / (1 + 2 * K * τ)) =
          4 * l3 ^ 2 + 2 * K * l3 / (1 + 2 * K * τ) := by
        ring
      rw [h3]
      have h4 : 2 * (-l3) ^ 2 = 2 * l3 ^ 2 := by ring
      rw [h4]
      have h5 : l3 + K / (1 + 2 * K * τ) = 0 := by nlinarith [hXeq]
      have h6 : K / (1 + 2 * K * τ) = -l3 := by linarith
      rw [show 2 * K * l3 / (1 + 2 * K * τ) = 2 * (K / (1 + 2 * K * τ)) * l3 by ring]
      rw [h6]
      ring
    rw [hphi]
    exact mul_pos two_pos (sq_pos_of_ne_zero hXpos.ne')
  · have hgt : K / (1 + 2 * K * τ) < -l3 := lt_of_not_ge hXsub
    have hpos : 0 < 2 * (-l3) * ((-l3) - K / (1 + 2 * K * τ)) :=
      mul_pos (mul_pos two_pos hXpos) (sub_pos.mpr hgt)
    exact lt_of_lt_of_le hpos hgen

end DifferentialGeometry.Geometry.Curvature.DimensionThree
