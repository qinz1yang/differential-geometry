import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.FlowBall.DistanceComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Metric.Family.Comparison

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}

variable [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem inner_exp_bounds
    (hS : IsSolutionOn S) {time : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {s t : ℝ} (hst : s ≤ t) (hreg : Ioo s t ⊆ D.regular)
    (hstB : Icc s t ⊆ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ))
    (hcomplete : RiemannianMetricComplete (S.base.metric t))
    {x : M}
    (hx : ENNReal.ofReal (Real.exp
      (((Module.finrank ℝ E : ℝ) ^ 2 / B.radius ^ 2) * (t - s))) *
        riemannianEDistOf (S.base.metric t) B.center x < ENNReal.ofReal B.radius)
    (v : TangentSpace I x) :
    Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) ^ 2 / B.radius ^ 2) * (t - s))) *
        (S.base.metric t).inner x v v ≤ (S.base.metric s).inner x v v ∧
      (S.base.metric s).inner x v v ≤
        Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 / B.radius ^ 2) * (t - s)) *
          (S.base.metric t).inner x v v := by
  let K : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 / B.radius ^ 2
  have hK : 0 ≤ K := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmem : ∀ q ∈ Icc s t, x ∈ B.setAt q := by
    intro q hq
    have hscaled : ENNReal.ofReal (Real.exp (K * (t - q))) *
        riemannianEDistOf (S.base.metric t) B.center x < ENNReal.ofReal B.radius := by
      refine (mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) _).trans_lt hx
      change K * (t - q) ≤ K * (t - s)
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left hq.1 t) hK
    have hd := riemannianEDistOf_le_exp_mul
      hS B hB hq.2 (fun _ hu => hreg ⟨hq.1.trans_lt hu.1, hu.2⟩)
      (fun _ hu => hstB ⟨hq.1.trans hu.1, hu.2⟩) hcomplete hscaled
    exact hd.trans_lt hscaled
  have hsqrt : Real.sqrt (1 / B.radius ^ 4) = 1 / B.radius ^ 2 := by
    have hr : 0 < B.radius ^ 2 := sq_pos_of_pos B.radius_pos
    rw [show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring]
    rw [show 1 / (B.radius ^ 2) ^ 2 = (1 / B.radius ^ 2) ^ 2 by field_simp]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr)]
  have hderiv : ∀ q ∈ Icc s t,
      ∃ d : ℝ, HasDerivWithinAt (fun u => (S.base.metric u).inner x v v) d (Icc s t) q ∧
        |d| ≤ (2 * K) * (S.base.metric q).inner x v v := by
    intro q hq
    have hr := ricci_abs_of_rm B hB (hstB hq) (hmem q hq) v
    rw [hsqrt] at hr
    have hr' : |ricciTensor (S.base.metric q) x v v| ≤
        K * (S.base.metric q).inner x v v := by
      simpa only [K, div_eq_mul_inv, one_mul] using hr
    refine ⟨_, metricPDE_Icc S hS (fun _ hu => hB.1 (hstB hu))
      hreg q hq x v v, ?_⟩
    rw [abs_mul]
    norm_num
    nlinarith [hr']
  have hf := inner_le_exp_mul_inner_of_abs_deriv_le S.base.metric x v hderiv
    (right_mem_Icc.mpr hst) (left_mem_Icc.mpr hst)
  have hb := inner_le_exp_mul_inner_of_abs_deriv_le S.base.metric x v hderiv
    (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)
  rw [abs_of_nonneg (sub_nonneg.mpr hst)] at hf
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)] at hb
  refine ⟨?_, hb⟩
  calc
    _ ≤ Real.exp (-(2 * K * (t - s))) *
        (Real.exp (2 * K * (t - s)) * (S.base.metric s).inner x v v) :=
      mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
    _ = (S.base.metric s).inner x v v := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [neg_add_cancel, Real.exp_zero, one_mul]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_inner_exp_bounds_on_terminal_ball :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
        IsSolutionOn (I := I) S →
        ∀ {time : RealTimeInterval.FlowTime D}
          (B : FlowMetricBall S time), B.IsRmControlled →
          Set.Ioo ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
          RiemannianMetricComplete (I := I) (S.base.metric (time : Real)) →
          ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
            ∀ t ∈ Set.Icc
              ((time : Real) - eps * B.radius ^ 2) (time : Real),
              ∀ x : M,
                riemannianEDistOf (I := I) (S.base.metric (time : Real))
                    B.center x ≤ ENNReal.ofReal (B.radius / 32) →
                ∀ v : TangentSpace I x,
                  Real.exp (-(2 * (Module.finrank Real E : Real) ^ 2 * eps)) *
                      (S.base.metric (time : Real)).inner x v v ≤
                        (S.base.metric t).inner x v v ∧
                    (S.base.metric t).inner x v v ≤
                      Real.exp (2 * (Module.finrank Real E : Real) ^ 2 * eps) *
                        (S.base.metric (time : Real)).inner x v v := by
  let n : Real := Module.finrank Real E
  let eps₀ : Real := Real.log 2 / (4 * (n ^ 2 + 1))
  have hn0 : 0 ≤ n ^ 2 := sq_nonneg n
  have hden : 0 < 4 * (n ^ 2 + 1) := by positivity
  have heps₀ : 0 < eps₀ :=
    div_pos (Real.log_pos (by norm_num)) hden
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hB hreg hcomplete eps heps heps₀ t ht x hx v
  have hepsLog : n ^ 2 * eps ≤ Real.log 2 := by
    have hmul : eps * (4 * (n ^ 2 + 1)) ≤ Real.log 2 := by
      apply (le_div_iff₀ hden).mp
      simpa only [eps₀] using heps₀
    nlinarith [hn0]
  have htBig : Set.Icc t (time : Real) ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
    intro q hq
    have hepsOne : eps ≤ 1 := by
      have hlogTwo : Real.log 2 < 1 := by
        nlinarith [Real.log_lt_sub_one_of_pos
          (by norm_num : (0 : Real) < 2) (by norm_num : (2 : Real) ≠ 1)]
      have hepsSmall : eps < 1 := by
        have hmulPos : 0 < 4 * (n ^ 2 + 1) := hden
        have hbound : eps * (4 * (n ^ 2 + 1)) ≤ Real.log 2 := by
          apply (le_div_iff₀ hden).mp
          simpa only [eps₀] using heps₀
        nlinarith [hn0]
      exact hepsSmall.le
    constructor
    · have hr2 := sq_nonneg B.radius
      nlinarith [ht.1, hq.1]
    · exact hq.2
  have hregSmall : Set.Ioo t (time : Real) ⊆ D.regular := by
    intro q hq
    apply hreg
    exact ⟨(htBig ⟨le_rfl, ht.2⟩).1.trans_lt hq.1, hq.2⟩
  have hdelta : (time : Real) - t ≤ eps * B.radius ^ 2 := by linarith [ht.1]
  have harg : n ^ 2 / B.radius ^ 2 * ((time : Real) - t) ≤ n ^ 2 * eps := by
    calc
      _ ≤ (n ^ 2 / B.radius ^ 2) * (eps * B.radius ^ 2) :=
        mul_le_mul_of_nonneg_left hdelta (div_nonneg hn0 (sq_nonneg _))
      _ = n ^ 2 * eps := by field_simp [B.radius_pos.ne']
  have hexp : Real.exp (n ^ 2 / B.radius ^ 2 * ((time : Real) - t)) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (harg.trans hepsLog)
      _ = 2 := Real.exp_log (by norm_num)
  have hscaled : ENNReal.ofReal (Real.exp
        (n ^ 2 / B.radius ^ 2 * ((time : Real) - t))) *
      riemannianEDistOf (S.base.metric (time : Real)) B.center x <
        ENNReal.ofReal B.radius := by
    calc
      _ ≤ ENNReal.ofReal 2 *
          riemannianEDistOf (S.base.metric (time : Real)) B.center x :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hexp) _
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (B.radius / 32) :=
        mul_le_mul_right hx _
      _ = ENNReal.ofReal (B.radius / 16) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
        congr 1
        ring
      _ < ENNReal.ofReal B.radius :=
        (ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by nlinarith [B.radius_pos])
  have hpair := inner_exp_bounds hS B hB ht.2 hregSmall htBig hcomplete hscaled v
  have hnn : 0 ≤ (S.base.metric (time : Real)).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((S.base.metric (time : Real)).pos x v hv).le
  constructor
  · calc
      _ ≤ Real.exp (-(2 * (n ^ 2 / B.radius ^ 2) * ((time : Real) - t))) *
          (S.base.metric (time : Real)).inner x v v :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [harg])) hnn
      _ ≤ (S.base.metric t).inner x v v := hpair.1
  · calc
      (S.base.metric t).inner x v v ≤
          Real.exp (2 * (n ^ 2 / B.radius ^ 2) * ((time : Real) - t)) *
            (S.base.metric (time : Real)).inner x v v := hpair.2
      _ ≤ Real.exp (2 * n ^ 2 * eps) * (S.base.metric (time : Real)).inner x v v :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [harg])) hnn

end DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall
