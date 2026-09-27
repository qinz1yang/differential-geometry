import DifferentialGeometry.Geometry.Metric.LocalMetricBallContainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.FixedSetVolumeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

section General

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

theorem fixed_ball_moving_rm_control
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time)
    (hslab : Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hreg : Ioc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.regular)
    (hRm : ∀ s ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ),
      ∀ z ∈ B.set, B.radius ^ 4 * FlowMetricBall.rmNormSq S s z ≤ 1)
    (y : M)
    (hy : riemannianEDistOf (I := I) (S.base.metric (time : ℝ)) B.center y <
      ENNReal.ofReal (B.radius / 2))
    (t : RealTimeInterval.FlowTime D)
    (ht : (t : ℝ) ∈ Icc ((time : ℝ) - B.radius ^ 2 / 2) (time : ℝ)) :
    ∃ C : FlowMetricBall S t,
      C.center = y ∧
      C.radius = B.radius / (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2)) ∧
      Icc ((t : ℝ) - C.radius ^ 2) (t : ℝ) ⊆ D.regular ∧
      (∀ s ∈ Icc ((t : ℝ) - C.radius ^ 2) (t : ℝ), C.setAt s ⊆ B.set) ∧
      C.IsRmControlled := by
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let : RegularSpace M := inferInstance
  let n : ℝ := Module.finrank ℝ E
  let a : ℝ := Real.exp (n ^ 2)
  let R : ℝ := B.radius / (4 * a)
  let Q : ℝ := Real.exp (2 * n ^ 2 * (3 / 4 : ℝ))
  have ha : 0 < a := Real.exp_pos _
  have ha1 : 1 ≤ a := by
    change 1 ≤ Real.exp (n ^ 2)
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (sq_nonneg n)
  have hR : 0 < R := div_pos B.radius_pos (mul_pos (by norm_num) ha)
  have hRa : R * a = B.radius / 4 := by
    dsimp only [R]
    field_simp [ha.ne']
  have hRquarter : R ≤ B.radius / 4 := by
    calc
      R = R * 1 := by ring
      _ ≤ R * a := mul_le_mul_of_nonneg_left ha1 hR.le
      _ = B.radius / 4 := hRa
  have hRle : R ≤ B.radius := by linarith [B.radius_pos]
  have hR2 : R ^ 2 ≤ B.radius ^ 2 / 16 := by
    calc
      R ^ 2 ≤ (B.radius / 4) ^ 2 := pow_le_pow_left₀ hR.le hRquarter 2
      _ = B.radius ^ 2 / 16 := by ring
  have hQ : 0 < Q := Real.exp_pos _
  have hQle : Q ≤ a ^ 2 := by
    dsimp only [Q, a]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith only [sq_nonneg n]
  have hroot : Real.sqrt Q ≤ a := by
    calc
      Real.sqrt Q ≤ Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt hQle
      _ = a := Real.sqrt_sq ha.le
  have hRcompare : R ≤ B.radius / (2 * Real.sqrt Q) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr hQ))).mpr
    calc
      R * (2 * Real.sqrt Q) ≤ R * (2 * a) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hroot (by norm_num)) hR.le
      _ = B.radius / 2 := by nlinarith only [hRa]
      _ ≤ B.radius := by linarith [B.radius_pos]
  let C : FlowMetricBall S t := ⟨y, R, hR⟩
  have hwindow : Icc ((t : ℝ) - R ^ 2) (t : ℝ) ⊆
      Icc ((time : ℝ) - (3 / 4 : ℝ) * B.radius ^ 2) (time : ℝ) := by
    intro s hs
    refine ⟨?_, hs.2.trans ht.2⟩
    nlinarith only [hs.1, ht.1, hR2, sq_nonneg B.radius]
  have hlarge : Icc ((t : ℝ) - R ^ 2) (t : ℝ) ⊆
      Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) := by
    intro s hs
    have hw := hwindow hs
    refine ⟨?_, hw.2⟩
    nlinarith only [hw.1, sq_nonneg B.radius]
  have hregular : Icc ((t : ℝ) - R ^ 2) (t : ℝ) ⊆ D.regular := by
    intro s hs
    have hw := hwindow hs
    apply hreg
    refine ⟨?_, hw.2⟩
    nlinarith only [hw.1, sq_pos_of_pos B.radius_pos]
  have hmetric := fixed_set_metric_comparison_of_rm S hS (time : ℝ) B.radius
    (U := B.set) B.radius_pos hslab hreg
    (by simpa only [FlowMetricBall.rmNormSq] using hRm)
    (eps := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hcontain : ∀ s ∈ Icc ((t : ℝ) - R ^ 2) (t : ℝ), C.setAt s ⊆ B.set := by
    intro s hs z hz
    have hm := hmetric s (hwindow hs)
    have hlocal : ∀ q : M,
        riemannianEDistOf (I := I) (S.base.metric (time : ℝ)) B.center q <
          ENNReal.ofReal B.radius →
        ∀ v : TangentSpace I q,
          (S.base.metric (time : ℝ)).inner q v v ≤
            Q * (S.base.metric s).inner q v v := by
      intro q hq v
      exact (hm.2 q hq v).1
    have hsub := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_local_quad
      (S.base.metric (time : ℝ)) (S.base.metric s) B.center y
      B.radius_pos hQ hy hlocal
    apply hsub
    change riemannianEDistOf (I := I) (S.base.metric s) y z < ENNReal.ofReal R at hz
    exact hz.trans_le (ENNReal.ofReal_le_ofReal hRcompare)
  refine ⟨C, rfl, rfl, hregular, hcontain, ?_⟩
  constructor
  · exact fun s hs ↦ hslab (hlarge hs)
  · intro s hs z hz
    have hcurv := hRm s (hlarge hs) z (hcontain s hs hz)
    have hRm0 : 0 ≤ FlowMetricBall.rmNormSq S s z :=
      normSq0S_nonneg (I := I) (S.base.metric s) z 4 (S.base.rm04 s z)
    have hpow : R ^ 4 ≤ B.radius ^ 4 := pow_le_pow_left₀ hR.le hRle 4
    exact (mul_le_mul_of_nonneg_right hpow hRm0).trans hcurv

end General

end DifferentialGeometry.PDE.RicciFlow

end
