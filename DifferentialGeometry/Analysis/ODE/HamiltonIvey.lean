import DifferentialGeometry.Analysis.Calculus.MatrixInverseSmooth
import DifferentialGeometry.Analysis.ODE.Nagumo
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Analysis.ODE
open Filter Set
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem contDiff_curvatureOperatorReaction3 :
    ContDiff Real ∞ curvatureOperatorReaction3 := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff Real ∞ (fun A : Matrix (Fin 3) (Fin 3) Real =>
    (A * A) i j + A.adjugate i j)
  apply ContDiff.add
  · simp only [Matrix.mul_apply]
    exact ContDiff.sum (fun _ _ => by fun_prop)
  · exact DifferentialGeometry.Analysis.contDiff_adjugate_of_entries id
      (fun i j => by fun_prop) i j

theorem smul_add_curvatureOperatorReaction3_mem_posTangentConeAt
    {K : Real} (hK : 0 < K) {A : Matrix (Fin 3) (Fin 3) Real}
    (hA : A ∈ hamiltonIveyConvexMatrixRegion K 0) :
    K • A + curvatureOperatorReaction3 A ∈
      posTangentConeAt (hamiltonIveyConvexMatrixRegion K 0) A := by
  obtain ⟨eps, heps, hstep⟩ :=
    hamiltonIveyConvexMatrixRegion_reaction_small_time hK le_rfl A hA
  let γ : Real → Matrix (Fin 3) (Fin 3) Real := fun t =>
    (1 + K * t) • (A + (t / 2) • hamiltonIveyMatrixReaction A)
  have hγ₀ : γ 0 = A := by simp [γ]
  have hreaction : (1 / 2 : Real) • hamiltonIveyMatrixReaction A =
      curvatureOperatorReaction3 A := by
    unfold hamiltonIveyMatrixReaction curvatureOperatorReaction3
    module
  have hγ : HasDerivAt γ (K • A + curvatureOperatorReaction3 A) 0 := by
    have hc : HasDerivAt (fun t : Real => 1 + K * t) K 0 := by
      simpa using ((hasDerivAt_id (0 : Real)).const_mul K).const_add 1
    have hB : HasDerivAt (fun t : Real => A + (t / 2) • hamiltonIveyMatrixReaction A)
        ((1 / 2 : Real) • hamiltonIveyMatrixReaction A) 0 :=
      (((hasDerivAt_id (0 : Real)).div_const 2).smul_const _).const_add A
    simpa only [γ, mul_zero, add_zero, zero_div, zero_smul,
      zero_add, one_smul, hreaction, add_comm] using! hc.smul hB
  have hmem : ∀ᶠ t in 𝓝[>] (0 : Real), γ (0 + t) ∈
      hamiltonIveyConvexMatrixRegion K 0 := by
    have hsmall : ∀ᶠ t : Real in 𝓝[>] 0, t < 2 * eps :=
      (eventually_lt_nhds (by positivity : (0 : Real) < 2 * eps)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htSmall
    have htPos : 0 < t := ht
    have ht' : t / 2 ∈ Icc 0 eps := ⟨by positivity, by linarith⟩
    have hscaled := smul_mem_hamiltonIveyConvexMatrixRegion_initial hK ht'.1
      (by simpa only [zero_add] using hstep (t / 2) ht')
    have hcoef : 1 + 2 * K * (t / 2) = 1 + K * t := by ring
    simpa only [hcoef, γ, zero_add] using hscaled
  simpa only [hγ₀] using!
    HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right hγ hmem

theorem isForwardInvariantForODE_hamiltonIveyConvexMatrixRegion_initial
    {K : Real} (hK : 0 < K) :
    IsForwardInvariantForODE
      (fun _ A => K • A + curvatureOperatorReaction3 A)
      (hamiltonIveyConvexMatrixRegion K 0) := by
  apply nagumo_isForwardInvariantForODE_of_contDiff
    (isClosed_hamiltonIveyConvexMatrixRegion hK)
    (convex_hamiltonIveyConvexMatrixRegion hK le_rfl)
    (fun _ _ hA => smul_add_curvatureOperatorReaction3_mem_posTangentConeAt hK hA)
  change ContDiff Real 1 (fun p : Real × Matrix (Fin 3) (Fin 3) Real =>
    K • p.2 + curvatureOperatorReaction3 p.2)
  have hQ : ContDiff Real 1 curvatureOperatorReaction3 :=
    contDiff_curvatureOperatorReaction3.of_le (by norm_num)
  have hlin : ContDiff Real 1 (fun p : Real × Matrix (Fin 3) (Fin 3) Real => K • p.2) := by
    simpa only [Pi.smul_apply'] using!
      (contDiff_snd : ContDiff Real 1
        (Prod.snd : Real × Matrix (Fin 3) (Fin 3) Real → _)).const_smul K
  exact hlin.add (hQ.comp contDiff_snd)

theorem isForwardInvariantForODE_hamiltonIveyConvexMatrixRegion_normalized :
    IsForwardInvariantForODE
      (fun _ A => A + curvatureOperatorReaction3 A)
      (hamiltonIveyConvexMatrixRegion 1 0) := by
  simpa only [one_smul] using
    isForwardInvariantForODE_hamiltonIveyConvexMatrixRegion_initial zero_lt_one

theorem hasDerivWithinAt_pinchingRatioLog_of_reaction
    {l m n : ℝ → ℝ} {t a b : ℝ} {J : Set ℝ}
    (hn : n t ≠ 0)
    (hl : HasDerivWithinAt l (a * l t + b * (l t ^ 2 + m t * n t)) J t)
    (hm : HasDerivWithinAt m (a * m t + b * (m t ^ 2 + l t * n t)) J t)
    (hn' : HasDerivWithinAt n (a * n t + b * (n t ^ 2 + l t * m t)) J t) :
    HasDerivWithinAt
      (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s))
      (b * (-n t) - a + b *
        (l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2)) /
          (-n t) ^ 2) J t := by
  have hq : HasDerivWithinAt (fun s => -n s) (- (a * n t + b * (n t ^ 2 + l t * m t))) J t := hn'.neg
  have hq0 : -n t ≠ 0 := neg_ne_zero.mpr hn
  have hS : HasDerivWithinAt (fun s => l s + m s + n s)
      (a * (l t + m t + n t) + b *
        (l t ^ 2 + m t ^ 2 + n t ^ 2 + l t * m t + l t * n t + m t * n t)) J t := by
    exact ((hl.add hm).add hn').congr_deriv (by ring)
  have hquot := hS.div hq hq0
  have hlog := hq.log hq0
  have hsum := hquot.sub hlog
  have hfun : (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s)) =
      ((fun s => l s + m s + n s) / (fun s => -n s)) - (fun y => Real.log (-n y)) := by
    funext s
    rfl
  rw [hfun]
  exact hsum.congr_deriv (by field_simp [hq0, hn]; ring)

theorem hasDerivAt_pinchingRatioLog_of_reaction
    {l m n : ℝ → ℝ} {t a b : ℝ}
    (hn : n t ≠ 0)
    (hl : HasDerivAt l (a * l t + b * (l t ^ 2 + m t * n t)) t)
    (hm : HasDerivAt m (a * m t + b * (m t ^ 2 + l t * n t)) t)
    (hn' : HasDerivAt n (a * n t + b * (n t ^ 2 + l t * m t)) t) :
    HasDerivAt
      (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s))
      (b * (-n t) - a + b *
        (l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2)) /
          (-n t) ^ 2) t := by
  exact hasDerivWithinAt_univ.mp
    (hasDerivWithinAt_pinchingRatioLog_of_reaction hn
      hl.hasDerivWithinAt hm.hasDerivWithinAt hn'.hasDerivWithinAt)

theorem deriv_pinchingRatioLog_of_reaction
    {l m n : ℝ → ℝ} {t a b : ℝ}
    (hn : n t ≠ 0)
    (hl : HasDerivAt l (a * l t + b * (l t ^ 2 + m t * n t)) t)
    (hm : HasDerivAt m (a * m t + b * (m t ^ 2 + l t * n t)) t)
    (hn' : HasDerivAt n (a * n t + b * (n t ^ 2 + l t * m t)) t) :
    deriv (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s)) t =
      b * (-n t) - a + b *
        (l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2)) /
          (-n t) ^ 2 :=
  (hasDerivAt_pinchingRatioLog_of_reaction hn hl hm hn').deriv

theorem deriv_pinchingRatioLog_ge_of_reaction
    {l m n : ℝ → ℝ} {t a b : ℝ}
    (hnl : n t ≤ l t) (hnm : n t ≤ m t) (hn : n t < 0)
    (hb : 0 ≤ b)
    (hl : HasDerivAt l (a * l t + b * (l t ^ 2 + m t * n t)) t)
    (hm : HasDerivAt m (a * m t + b * (m t ^ 2 + l t * n t)) t)
    (hn' : HasDerivAt n (a * n t + b * (n t ^ 2 + l t * m t)) t) :
    b * (-n t) - a ≤
      deriv (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s)) t := by
  rw [deriv_pinchingRatioLog_of_reaction hn.ne hl hm hn']
  have hraw := hamilton_ivey_algebraic_inequality hnl hnm hn.le
  have hpi : 0 ≤ l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2) := by
    nlinarith only [hraw]
  have hden : 0 ≤ (-n t) ^ 2 := sq_nonneg _
  have hfrac : 0 ≤ b *
      (l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2)) /
        (-n t) ^ 2 := by
    exact div_nonneg (mul_nonneg hb hpi) hden
  linarith


end DifferentialGeometry.Geometry.Curvature.DimensionThree
