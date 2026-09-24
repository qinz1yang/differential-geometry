import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SquareClock
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lRegularizedAction_sqrt_add_sq_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {d a c : ℝ} (hd : 0 < d) (ha : 0 < a) (hac : a ≤ c)
    (hcarrier : ∀ r ∈ Icc a c, -d - r ^ 2 ∈ D.carrier)
    (hscalar : ∀ r ∈ Icc a c, ∀ x : M, 0 ≤ S.scalar (-d - r ^ 2) x)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lRegularizedAction S (-d) (fun r => alpha (Real.sqrt (r ^ 2 + d))) a c ≤
      lRegularizedAction S 0 alpha
        (Real.sqrt (a ^ 2 + d)) (Real.sqrt (c ^ 2 + d)) := by
  let beta : ℝ → M := fun r => alpha (Real.sqrt (r ^ 2 + d))
  have hclock : ContDiff ℝ 1 (fun r : ℝ => Real.sqrt (r ^ 2 + d)) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt (fun r => by positivity)
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) I 1 beta := halpha.comp hclock.contMDiff
  have hsqrtOrder : Real.sqrt (a ^ 2 + d) ≤ Real.sqrt (c ^ 2 + d) := by
    apply Real.sqrt_le_sqrt
    exact add_le_add_left (pow_le_pow_left₀ ha.le hac 2) d
  have hinverse : Set.EqOn
      (fun s => beta (Real.sqrt (s ^ 2 - d))) alpha
      (uIoo (Real.sqrt (a ^ 2 + d)) (Real.sqrt (c ^ 2 + d))) := by
    intro s hs
    have hs0 : Real.sqrt (a ^ 2 + d) < s := by
      simpa only [min_eq_left hsqrtOrder] using hs.1
    have hspos : 0 < s := lt_of_le_of_lt (Real.sqrt_nonneg _) hs0
    have hsquare : a ^ 2 + d ≤ s ^ 2 := by
      calc
        a ^ 2 + d = (Real.sqrt (a ^ 2 + d)) ^ 2 :=
          (Real.sq_sqrt (add_nonneg (sq_nonneg a) hd.le)).symm
        _ ≤ s ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs0.le 2
    have hrad : 0 ≤ s ^ 2 - d := by nlinarith [sq_nonneg a]
    dsimp only [beta]
    rw [Real.sq_sqrt hrad, sub_add_cancel, Real.sqrt_sq hspos.le]
  have haction :
      lRegularizedAction S 0 (fun s => beta (Real.sqrt (s ^ 2 - d)))
        (Real.sqrt (a ^ 2 + d)) (Real.sqrt (c ^ 2 + d)) =
      lRegularizedAction S 0 alpha
        (Real.sqrt (a ^ 2 + d)) (Real.sqrt (c ^ 2 + d)) :=
    lRegularizedAction_congr S 0 _ _ _ _ hinverse
  have hid := lRegularizedAction_sqrt_sub_sq S hd.le ha hac beta hbeta
  have hlag : ContinuousOn (lRegularizedLagrangian S (-d) beta) (Icc a c) := by
    have h := lRegularizedLagrangian_continuousOn_carrier S hS beta hbeta
    simpa only [Function.comp_def, id_eq] using
      h.comp (continuous_const.prodMk continuous_id).continuousOn hcarrier
  have hweight : ContinuousOn (fun r : ℝ => Real.sqrt (r ^ 2 + d) / r) (Icc a c) := by
    have hnum : Continuous (fun r : ℝ => Real.sqrt (r ^ 2 + d)) := by fun_prop
    exact hnum.continuousOn.div continuousOn_id
      (fun r hr => (ha.trans_le hr.1).ne')
  have hint := intervalIntegral.integral_mono_on (μ := volume) hac
    (hlag.intervalIntegrable_of_Icc hac)
    ((hweight.mul hlag).intervalIntegrable_of_Icc hac) (fun r hr => by
      have hrpos : 0 < r := ha.trans_le hr.1
      have hratio : 1 ≤ Real.sqrt (r ^ 2 + d) / r := by
        apply (le_div_iff₀ hrpos).mpr
        simpa only [one_mul] using
          (Real.le_sqrt_of_sq_le (le_add_of_nonneg_right hd.le) :
            r ≤ Real.sqrt (r ^ 2 + d))
      have hnonneg : 0 ≤ lRegularizedLagrangian S (-d) beta r := by
        dsimp only [lRegularizedLagrangian]
        exact add_nonneg
          (mul_nonneg (by norm_num) (metric_inner_self_nonneg _ _ _))
          (mul_nonneg (by positivity) (hscalar r hr (beta r)))
      simpa only [one_mul, Pi.mul_apply] using mul_le_mul_of_nonneg_right hratio hnonneg)
  change lRegularizedAction S (-d) beta a c ≤ _
  exact hint.trans_eq (hid.symm.trans haction)

end DifferentialGeometry.PDE.RicciFlow.Perelman
