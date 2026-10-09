import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierActionContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.MinimizerNonnegativity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bundle Set MeasureTheory Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.lRegAction_lower
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (b : ℝ) (hb : 0 ≤ b) (hbT : b ^ 2 ≤ T)
    (alpha : ℝ → E3)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) (𝓡 3) 1 alpha) :
    (2 / 3 : ℝ) * b ^ 3 ≤ lRegularizedAction S.toSolutionOn T alpha 0 b := by
  have hTlife : ENNReal.ofReal T < S.lifetime :=
    ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos T).mp hT).2
  have hback (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      T - s ^ 2 ∈ S.domain := by
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).mpr hs.2
    exact (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos (T - s ^ 2)).mpr
      ⟨sub_nonneg.mpr (hs2.trans hbT),
        (ENNReal.ofReal_le_ofReal (sub_le_self T (sq_nonneg s))).trans_lt hTlife⟩
  have hLag : IntervalIntegrable (lRegularizedLagrangian S.toSolutionOn T alpha) volume 0 b :=
    lRegLag_integrable_on_carrier S.toSolutionOn S.isSolutionOn.smoothMetric
      ⟨S.isSolutionOn.scalarCont⟩ T 0 b alpha halpha
      (fun s hs ↦ hback s (by simpa only [uIcc_of_le hb] using hs))
  have hpotInt : IntervalIntegrable (fun s : ℝ ↦ 2 * s ^ 2) volume 0 b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 b
  have hpoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      2 * s ^ 2 ≤ lRegularizedLagrangian S.toSolutionOn T alpha s := by
    have hscalar : 1 ≤ S.toSolutionOn.scalar (T - s ^ 2) (alpha s) := by
      change 1 ≤ metricScalarAt (S.metric (T - s ^ 2)) (alpha s)
      exact S.one_le_scalar (T - s ^ 2) (hback s hs) (alpha s)
    have hkin : 0 ≤ (S.toSolutionOn.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := 𝓡 3) alpha s) (lVelocity (I := 𝓡 3) alpha s) := by
      by_cases hv : lVelocity (I := 𝓡 3) alpha s = 0
      · rw [hv]
        simp
      · exact ((S.toSolutionOn.base.metric (T - s ^ 2)).pos (alpha s) _ hv).le
    have hpot := mul_le_mul_of_nonneg_left hscalar
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg s))
    change 2 * s ^ 2 ≤
      (1 / 2 : ℝ) * (S.toSolutionOn.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := 𝓡 3) alpha s) (lVelocity (I := 𝓡 3) alpha s) +
        2 * s ^ 2 * S.toSolutionOn.scalar (T - s ^ 2) (alpha s)
    nlinarith only [hkin, hpot]
  have hmono := intervalIntegral.integral_mono_on hb hpotInt hLag hpoint
  have hpoly : (∫ s in (0 : ℝ)..b, 2 * s ^ 2) = (2 / 3 : ℝ) * b ^ 3 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    ring
  rw [hpoly] at hmono
  exact hmono

theorem PartialStandardSolution.lCost_competitors_bddBelow
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (x y : E3) (tau : ℝ) (htau : 0 ≤ tau) (htauT : tau ≤ T) :
    BddBelow {r : ℝ | ∃ alpha : ℝ → E3,
      ContMDiff (modelWithCornersSelf ℝ ℝ) (𝓡 3) 1 alpha ∧
        alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
        lLength S.toSolutionOn T (squareRootReparametrization alpha) 0 tau = r} := by
  refine ⟨(2 / 3 : ℝ) * (Real.sqrt tau) ^ 3, ?_⟩
  rintro r ⟨alpha, halpha, _hstart, _hend, hr⟩
  rw [← hr, lLength_squareRootReparametrization_eq_lRegularizedAction (I := 𝓡 3) S.toSolutionOn T alpha tau htau]
  exact S.lRegAction_lower T hT (Real.sqrt tau) (Real.sqrt_nonneg tau)
    (by simpa only [Real.sq_sqrt htau] using htauT) alpha halpha

theorem PartialStandardSolution.lCost_competitors_nonempty
    (S : PartialStandardSolution) (T : ℝ)
    (x y : E3) (tau : ℝ) (htau : 0 < tau) :
    ({r : ℝ | ∃ alpha : ℝ → E3,
      ContMDiff (modelWithCornersSelf ℝ ℝ) (𝓡 3) 1 alpha ∧
        alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
        lLength S.toSolutionOn T (squareRootReparametrization alpha) 0 tau = r} : Set ℝ).Nonempty := by
  let b : ℝ := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  let alpha : ℝ → E3 := fun s ↦ x + (s / b) • (y - x)
  have halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) (𝓡 3) 1 alpha := by
    have haff : ContDiff ℝ 1 alpha :=
      contDiff_const.add ((contDiff_id.div_const b).smul contDiff_const)
    exact haff.contMDiff
  have hstart : alpha 0 = x := by
    simp only [alpha, zero_div, zero_smul, add_zero]
  have hend : alpha (Real.sqrt tau) = y := by
    change x + (b / b) • (y - x) = y
    rw [div_self hb.ne', one_smul]
    abel
  exact ⟨lLength S.toSolutionOn T (squareRootReparametrization alpha) 0 tau,
    alpha, halpha, hstart, hend, rfl⟩

theorem PartialStandardSolution.lCost_lower
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (x y : E3) (tau : ℝ) (htau : 0 < tau) (htauT : tau ≤ T) :
    (2 / 3 : ℝ) * (Real.sqrt tau) ^ 3 ≤ lCost S.toSolutionOn T x y tau := by
  let C : Set ℝ := {r : ℝ | ∃ beta : ℝ → E3,
    ContMDiff (modelWithCornersSelf ℝ ℝ) (𝓡 3) 1 beta ∧
      beta 0 = x ∧ beta (Real.sqrt tau) = y ∧
      lLength S.toSolutionOn T (squareRootReparametrization beta) 0 tau = r}
  have hC : C.Nonempty :=
    S.lCost_competitors_nonempty T x y tau htau
  change (2 / 3 : ℝ) * (Real.sqrt tau) ^ 3 ≤ sInf C
  apply le_csInf hC
  rintro r ⟨beta, hbeta, _hstart, _hend, hr⟩
  rw [← hr, lLength_squareRootReparametrization_eq_lRegularizedAction (I := 𝓡 3) S.toSolutionOn T beta tau htau.le]
  exact S.lRegAction_lower T hT (Real.sqrt tau) (Real.sqrt_nonneg tau)
    (by simpa only [Real.sq_sqrt htau.le] using htauT) beta hbeta

theorem PartialStandardSolution.redLength_lower
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (x y : E3) (tau : ℝ) (htau : 0 < tau) (htauT : tau ≤ T) :
    tau / 3 ≤ redLength S.toSolutionOn T x y tau := by
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hden : 0 < 2 * Real.sqrt tau := mul_pos (by norm_num) hb
  have hcost := S.lCost_lower T hT x y tau htau htauT
  change tau / 3 ≤ lCost S.toSolutionOn T x y tau / (2 * Real.sqrt tau)
  apply (le_div_iff₀ hden).mpr
  calc
    tau / 3 * (2 * Real.sqrt tau) = (2 / 3 : ℝ) * tau * Real.sqrt tau := by ring
    _ = (2 / 3 : ℝ) * (Real.sqrt tau) ^ 2 * Real.sqrt tau := by
      rw [Real.sq_sqrt htau.le]
    _ = (2 / 3 : ℝ) * (Real.sqrt tau) ^ 3 := by ring
    _ ≤ lCost S.toSolutionOn T x y tau := hcost

end DifferentialGeometry.PDE.RicciFlow

end
