import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedBadTimesCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S

set_option autoImplicit false

/-!
# CX-SPINE：从 P6(c) 的实际否定抽取同一 A 的坏种子序列

第 i 次直接测试 `LargerBallScalarAt_C11S` 的 rbar=1/(i+1)、K=i+1。
输出保留原 F、原 observation index、原 seed、原 A 的 volume 和 A*r ball，
以及原 delta/alpha 在 [t/2,t] 上的 accuracy 条件。
r/sqrt(t) -> 0 和 R*r² -> infinity 均由这些实际反例产生，不借 P6(b) 序列。

第二定理消费 `P6SeedBadTimesCXSP` 当前 G37 source：prepared chain 的实际
bounded-time estimate 排除全部有界时间子列，因此同一原坏序列已有 t -> infinity。
这里不选择 nr guard，也不假设 r/nr 有界；该 ratio 的子列分支留给之后的消费。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 对实际 larger-ball scalar 结论取否定，保留所有原 seed 数据和原 A。 -/
theorem exists_scalar_bad_sequence_of_not_larger_ball_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {delta : ℝ → ℝ} {alpha : ℝ → ℝ → ℝ} {A : ℝ}
    (hnot : ¬ LargerBallScalarAt_C11S F delta alpha A) :
    ∃ (idx : ℕ → ℕ)
      (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon)
      (p x : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
      (r : ℕ → ℝ),
      let R := fun i => metricScalarAt
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (x i)
      (∀ i, 0 < r i) ∧ (∀ i, 0 < (t i : ℝ)) ∧
      (∀ i, 2 * r i ^ 2 < (t i : ℝ)) ∧
      (∀ i, ∀ s ∈ Icc ((t i : ℝ) / 2) (t i), delta s < alpha A s) ∧
      (∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory
        (t i) (p i) (r i)) ∧
      (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤ ballVolume
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i)) ∧
      (∀ i, r i ≤ Real.sqrt (t i : ℝ) / ((i : ℝ) + 1)) ∧
      (∀ i, x i ∈ riemannianBallOf
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (A * r i)) ∧
      (∀ i : ℕ, (i : ℝ) + 1 < R i * r i ^ 2) ∧
      Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun i => R i * r i ^ 2) atTop atTop := by
  classical
  have hcounter (i : ℕ) :
      ∃ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).horizon)
        (p : ((F.tower.history n).toHistory.stageAt t).Carrier) (r : ℝ)
        (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
        2 * r ^ 2 < (t : ℝ) ∧
        (∀ s ∈ Icc ((t : ℝ) / 2) t, delta s < alpha A s) ∧
        hasSmallParabolicCurvature (F.tower.history n).toHistory t p r ∧
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) p r ∧
        r ≤ Real.sqrt (t : ℝ) / ((i : ℝ) + 1) ∧
        x ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) p (A * r) ∧
        (i : ℝ) + 1 < metricScalarAt ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) x * r ^ 2 := by
    by_contra hcounter
    apply hnot
    refine ⟨1 / ((i : ℝ) + 1), (i : ℝ) + 1, by positivity, by positivity, ?_⟩
    intro n H t p r htime hacc hsmall hvol hscale x hx
    by_contra hbound
    have hhigh := mul_lt_mul_of_pos_right (lt_of_not_ge hbound)
      (sq_pos_of_pos hsmall.1)
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hsmall.1.ne'), mul_one] at hhigh
    apply hcounter
    refine ⟨n, t, p, r, x, htime, hacc, hsmall, hvol, ?_, hx, hhigh⟩
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hscale
  choose idx t p r x htime hacc hsmall hvol hscale hx hbad using hcounter
  let R := fun i => metricScalarAt
    ((F.tower.history (idx i)).toHistory.stageMetric
      ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (x i)
  have hr (i : ℕ) : 0 < r i := (hsmall i).1
  have ht (i : ℕ) : 0 < (t i : ℝ) :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (r i))).trans_lt (htime i)
  have hnat : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hratio : Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => div_nonneg (hr i).le (Real.sqrt_nonneg _)) ?_ hinv
    intro i
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (ht i))).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hscale i
  have hescape : Tendsto (fun i => R i * r i ^ 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [hnat.eventually_ge_atTop B] with i hi
    exact hi.trans (hbad i).le
  exact ⟨idx, t, p, x, r, hr, ht, htime, hacc, hsmall, hvol, hscale,
    hx, hbad, hratio, hescape⟩

/-- prepared chain 上，同一实际坏序列的原时间趋无穷；无需预先选择 guard。 -/
theorem exists_prepared_scalar_bad_sequence_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) {delta : ℝ → ℝ} {alpha : ℝ → ℝ → ℝ}
    {A : ℝ} (hA : 0 < A) (hnot : ¬ LargerBallScalarAt_C11S F delta alpha A) :
    ∃ (idx : ℕ → ℕ)
      (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon)
      (p x : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
      (r : ℕ → ℝ),
      let R := fun i => metricScalarAt
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (x i)
      (∀ i, 0 < r i) ∧ (∀ i, 0 < (t i : ℝ)) ∧
      (∀ i, 2 * r i ^ 2 < (t i : ℝ)) ∧
      (∀ i, ∀ s ∈ Icc ((t i : ℝ) / 2) (t i), delta s < alpha A s) ∧
      (∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory
        (t i) (p i) (r i)) ∧
      (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤ ballVolume
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i)) ∧
      (∀ i, r i ≤ Real.sqrt (t i : ℝ) / ((i : ℝ) + 1)) ∧
      (∀ i, x i ∈ riemannianBallOf
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (A * r i)) ∧
      (∀ i : ℕ, (i : ℝ) + 1 < R i * r i ^ 2) ∧
      Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun i => R i * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => (t i : ℝ)) atTop atTop := by
  obtain ⟨idx, t, p, x, r, hr, ht, htime, hacc, hsmall, hvol, hscale,
    hx, hbad, hratio, hescape⟩ := exists_scalar_bad_sequence_of_not_larger_ball_CXSP hnot
  refine ⟨idx, t, p, x, r, hr, ht, htime, hacc, hsmall, hvol, hscale,
    hx, hbad, hratio, hescape, ?_⟩
  exact seed_bad_times_tendsto_atTop_CXSP S F hTower A hA
    idx t p x r hsmall hx hscale hescape

end GC.LongTime.Ch11

end
