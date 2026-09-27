import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierActionDilation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCarrierActionLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import Mathlib.Topology.Semicontinuity.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Set Filter Bundle DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.lCost_upperSemicontinuousWithinAt
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (x y : E3) (tau : ℝ) (htau : 0 < tau) (htauT : tau ≤ T) :
    UpperSemicontinuousWithinAt
      (fun r : ℝ ↦ lCost S.toSolutionOn T x y r) (Ioc 0 tau) tau := by
  rw [upperSemicontinuousWithinAt_iff]
  intro A hA
  obtain ⟨a, ⟨alpha, halpha, hstart, hend, ha⟩, haA⟩ :=
    exists_lt_of_csInf_lt (S.lCost_competitors_nonempty T x y tau htau) hA
  have hact : lRegularizedAction S.toSolutionOn T alpha 0 (Real.sqrt tau) < A := by
    rw [← lLength_squareRootReparametrization_eq_lRegularizedAction (I := 𝓡 3) S.toSolutionOn T alpha tau htau.le, ha]
    exact haA
  have hTpos : 0 < T := htau.trans_le htauT
  have hTlife : ENNReal.ofReal T < S.lifetime :=
    ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos T).mp hT).2
  have hcarrier : Icc (0 : ℝ) T ⊆ S.domain :=
    (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos T hTpos.le).mpr hTlife
  have hslab : Icc (T - (Real.sqrt tau) ^ 2) T ⊆
      (lifetimeInterval S.lifetime S.lifetime_pos).carrier := by
    intro t ht
    apply hcarrier
    rw [Real.sq_sqrt htau.le] at ht
    exact ⟨(sub_nonneg.mpr htauT).trans ht.1, ht.2⟩
  have hdil := lRegAction_dilation_tendsto_on_carrier
    S.toSolutionOn S.isSolutionOn.smoothMetric ⟨S.isSolutionOn.scalarCont⟩
    T (Real.sqrt tau) (Real.sqrt_pos.mpr htau) hslab alpha halpha
  have hsqrt : Tendsto Real.sqrt (𝓝[Ioc (0 : ℝ) tau] tau)
      (𝓝[Ioc (0 : ℝ) (Real.sqrt tau)] (Real.sqrt tau)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Real.continuous_sqrt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ⟨Real.sqrt_pos.mpr hr.1, Real.sqrt_le_sqrt hr.2⟩
  have hnear := (hdil.comp hsqrt).eventually (Iio_mem_nhds hact)
  filter_upwards [hnear, self_mem_nhdsWithin] with r hrA hr
  let beta : ℝ → E3 := fun s ↦ alpha (Real.sqrt tau * s / Real.sqrt r)
  have hbeta : ContMDiff (modelWithCornersSelf ℝ ℝ) (𝓡 3) 1 beta := by
    have hclock : ContDiff ℝ 1
        (fun s : ℝ ↦ Real.sqrt tau * s / Real.sqrt r) :=
      (contDiff_const.mul contDiff_id).div_const (Real.sqrt r)
    exact halpha.comp hclock.contMDiff
  have hbstart : beta 0 = x := by
    simpa only [beta, mul_zero, zero_div] using hstart
  have hbend : beta (Real.sqrt r) = y := by
    simpa only [beta, mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hr.1).ne'] using hend
  have hcost : lCost S.toSolutionOn T x y r ≤
      lRegularizedAction S.toSolutionOn T beta 0 (Real.sqrt r) := by
    change sInf _ ≤ _
    apply csInf_le (S.lCost_competitors_bddBelow T hT x y r hr.1.le
      (hr.2.trans htauT))
    exact ⟨beta, hbeta, hbstart, hbend,
      lLength_squareRootReparametrization_eq_lRegularizedAction (I := 𝓡 3) S.toSolutionOn T beta r hr.1.le⟩
  exact hcost.trans_lt hrA

theorem PartialStandardSolution.redDensity_lowerSemicontinuousWithinAt
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (x y : E3) (tau : ℝ) (htau : 0 < tau) (htauT : tau ≤ T) :
    LowerSemicontinuousWithinAt
      (fun r : ℝ ↦ ENNReal.ofReal (redDensity S.toSolutionOn T x y r))
      (Ioc 0 tau) tau := by
  have hcost := S.lCost_upperSemicontinuousWithinAt T hT x y tau htau htauT
  have hred : UpperSemicontinuousWithinAt
      (fun r : ℝ ↦ redLength S.toSolutionOn T x y r) (Ioc 0 tau) tau := by
    rw [upperSemicontinuousWithinAt_iff]
    intro A hA
    have hden : 0 < 2 * Real.sqrt tau := mul_pos (by norm_num) (Real.sqrt_pos.mpr htau)
    have hgap : lCost S.toSolutionOn T x y tau < A * (2 * Real.sqrt tau) :=
      (div_lt_iff₀ hden).mp hA
    obtain ⟨C, hC, hCA⟩ := exists_between hgap
    have hnearCost := (upperSemicontinuousWithinAt_iff.mp hcost) C hC
    have hdenCont : ContinuousAt (fun r : ℝ ↦ A * (2 * Real.sqrt r)) tau :=
      continuousAt_const.mul (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
    have hnearDen : ∀ᶠ r in 𝓝[Ioc (0 : ℝ) tau] tau,
        C < A * (2 * Real.sqrt r) :=
      (hdenCont.tendsto.mono_left nhdsWithin_le_nhds).eventually (Ioi_mem_nhds hCA)
    filter_upwards [hnearCost, hnearDen, self_mem_nhdsWithin] with r hrC hrDen hr
    change lCost S.toSolutionOn T x y r / (2 * Real.sqrt r) < A
    exact (div_lt_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr hr.1))).mpr
      (hrC.trans hrDen)
  let n : ℝ := Module.finrank ℝ E3
  have hlog : ContinuousAt (fun r : ℝ ↦ (n / 2) * Real.log r) tau :=
    continuousAt_const.mul (Real.continuousAt_log htau.ne')
  have hsum : UpperSemicontinuousWithinAt
      (fun r : ℝ ↦ redLength S.toSolutionOn T x y r +
        (n / 2) * Real.log r + (n / 2) * Real.log (4 * Real.pi))
      (Ioc 0 tau) tau :=
    (hred.add hlog.continuousWithinAt.upperSemicontinuousWithinAt).add
      upperSemicontinuousWithinAt_const
  have houter : Continuous (fun q : ℝ ↦ Real.exp (-q)) :=
    Real.continuous_exp.comp continuous_neg
  have hanti : Antitone (fun q : ℝ ↦ Real.exp (-q)) :=
    fun _ _ hab ↦ Real.exp_le_exp.mpr (neg_le_neg hab)
  have hexp := houter.continuousAt.comp_upperSemicontinuousWithinAt_antitone hsum hanti
  have hof := ENNReal.continuous_ofReal.continuousAt.comp_lowerSemicontinuousWithinAt
    hexp (fun _ _ hab ↦ ENNReal.ofReal_le_ofReal hab)
  have heq : (ENNReal.ofReal ∘ (fun q : ℝ ↦ Real.exp (-q)) ∘
      fun r : ℝ ↦ redLength S.toSolutionOn T x y r +
        (n / 2) * Real.log r + (n / 2) * Real.log (4 * Real.pi)) =
      fun r : ℝ ↦ ENNReal.ofReal (redDensity S.toSolutionOn T x y r) := by
    funext r
    apply congrArg ENNReal.ofReal
    apply congrArg Real.exp
    dsimp only [Function.comp_apply, redDensity, n]
    ring
  rw [heq] at hof
  exact hof

end DifferentialGeometry.PDE.RicciFlow

end
