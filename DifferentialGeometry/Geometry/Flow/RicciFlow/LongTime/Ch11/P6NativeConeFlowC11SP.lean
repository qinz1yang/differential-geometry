import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardSecondFlowC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.IntervalTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

/-!
# native cone 点 flow（O-CH11-NATIVE-NJ G3，后缀 `_C11SP`）

* `secondFlow_rescale_C11SP`：二次 blow-up 反向 flow 结论的 `×λ` 抛物 rescale
  （ratio `→ λ`、base scalar `λ⁻¹` ⇒ ratio `→ 1`、base scalar `1`）。
* `secondBlowup_flow_of_traced_scaled_C11SP`：A1 kernel `secondBlowup_flow_of_traced_C11SP` 的孪生，
  `hRy` 换成 `R(y) · λ = R`（kernel 在 `λ` 倍 scalar 尺度上 blow up）。
* `secondBlowup_assemble_neck_C11SP`：A1 `secondBlowup_assemble_C11SP` 的孪生，`hpay` 换成 S16 neck
  （G47 `native_chosen_neck_traced_of_chain_CXSP`）的 traced region 形 `1/(2√R)`、`1/R`、`1200R`；
  内部取 `λ = 4`、`θ = 4`、`K0 = 300` 喂 kernel，再 rescale 回 base scalar 1。
* `native_coneFlow_of_neckTraced_C11SP`：native 第一层数据（无 `nr ≤ r`）+ 点列 `xW` 的映射点处
  eventual G47 形 traced region ⇒ 冻结 hflowN flow 子句结论（对该 `xW`）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- 时间 `×λ` 的区间端点换算。 -/
theorem scaled_time_iff_C11SP {lam : ℝ} (hlam : 0 < lam) (tau s : ℝ) :
    ((-tau ≤ s * lam ↔ -(tau * lam⁻¹) ≤ s) ∧ (s * lam ≤ 0 ↔ s ≤ 0)) ∧
    ((-tau < s * lam ↔ -(tau * lam⁻¹) < s) ∧ (s * lam < 0 ↔ s < 0)) := by
  have e : -(tau * lam⁻¹) * lam = -tau := by field_simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [← e]
    exact mul_le_mul_iff_of_pos_right hlam
  · constructor
    · intro h
      by_contra hc
      have := mul_pos (lt_of_not_ge hc) hlam
      linarith
    · intro h
      nlinarith
  · rw [← e]
    exact mul_lt_mul_iff_of_pos_right hlam
  · constructor
    · intro h
      by_contra hc
      have := mul_nonneg (le_of_not_gt hc) hlam.le
      linarith
    · intro h
      nlinarith

/-- 限制到开集与放缩交换。 -/
theorem restrictOpen_scaleMetric_C11SP {N : Type*} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric ThreeModel N) {c : ℝ} (hc : 0 < c)
    (U : TopologicalSpace.Opens N) :
    (scaleMetric c hc g).restrictOpen U = scaleMetric c hc (g.restrictOpen U) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

/-- **`×λ` 抛物 rescale**：二次 blow-up flow 结论（ratio `→ λ`、base scalar `λ⁻¹`）⇒
标准形（ratio `→ 1`、base scalar `1`）。`P₂' = λ⁻¹ P₂`，`g'(s) = λ⁻¹ g(λ s)`，`r' = √λ⁻¹ r`。 -/
theorem secondFlow_rescale_C11SP (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (W : TopologicalSpace.Opens Pl.M) (xW : ℕ → W) {lam : ℝ} (hlam : 0 < lam)
    (h : ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 lam) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (gV : ℝ → SmoothRiemannianMetric ThreeModel V),
        gV 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := gV } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ s ∈ Icc (-tau) 0, ∀ z : V, metricAlgebraicCurvatureTensorAt (gV s) z ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = lam⁻¹ ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop,
            riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆
                (C n) '' riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf
                  (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                  (C n a) (C n b)).toReal -
                (riemannianEDistOf (gV 0) a b).toReal| < eta) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (gV : ℝ → SmoothRiemannianMetric ThreeModel V),
        gV 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := gV } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ s ∈ Icc (-tau) 0, ∀ z : V, metricAlgebraicCurvatureTensorAt (gV s) z ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = 1 ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop,
            riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆
                (C n) '' riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf
                  (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                  (C n a) (C n b)).toReal -
                (riemannianEDistOf (gV 0) a b).toReal| < eta := by
  obtain ⟨j, hj, A₂, hA₂, hrat, P₂, V, hp, hpath, tau, htau, gV, hG0, hsol, hnn, hbase, C, hC,
    r, hr, hcpt, hcap, hdist⟩ := h
  have hli : 0 < lam⁻¹ := inv_pos.mpr hlam
  let P₂' : PointedRiemannianManifold.{u, 0, 0} ThreeModel :=
    { P₂ with metric := scaleMetric lam⁻¹ hli P₂.metric }
  let gV' : ℝ → SmoothRiemannianMetric ThreeModel V := fun s =>
    scaleMetric lam⁻¹ hli (gV (parabolicTime 0 lam⁻¹ s))
  have hgV0 : gV' 0 = scaleMetric lam⁻¹ hli (gV 0) := by
    change scaleMetric lam⁻¹ hli (gV (parabolicTime 0 lam⁻¹ 0)) = _
    rw [parabolicTime_zero]
  have hpt : ∀ s : ℝ, parabolicTime 0 lam⁻¹ s = s * lam := by
    intro s
    unfold parabolicTime
    rw [zero_add, div_inv_eq_mul]
  have htau' : 0 < tau * lam⁻¹ := mul_pos htau hli
  have h0mem : (0 : ℝ) ∈ (RealTimeInterval.closed (-tau) 0 (by linarith)).carrier :=
    ⟨by linarith, le_rfl⟩
  have hcar : (parabolicInterval (RealTimeInterval.closed (-tau) 0 (by linarith)) 0 lam⁻¹
      h0mem).carrier = (RealTimeInterval.closed (-(tau * lam⁻¹)) 0 (by linarith)).carrier := by
    ext s
    change parabolicTime 0 lam⁻¹ s ∈ Icc (-tau) 0 ↔ s ∈ Icc (-(tau * lam⁻¹)) 0
    rw [hpt, mem_Icc, mem_Icc, (scaled_time_iff_C11SP hlam tau s).1.1,
      (scaled_time_iff_C11SP hlam tau s).1.2]
  have hreg : (parabolicInterval (RealTimeInterval.closed (-tau) 0 (by linarith)) 0 lam⁻¹
      h0mem).regular = (RealTimeInterval.closed (-(tau * lam⁻¹)) 0 (by linarith)).regular := by
    ext s
    change parabolicTime 0 lam⁻¹ s ∈ Ioo (-tau) 0 ↔ s ∈ Ioo (-(tau * lam⁻¹)) 0
    rw [hpt, mem_Ioo, mem_Ioo, (scaled_time_iff_C11SP hlam tau s).2.1,
      (scaled_time_iff_C11SP hlam tau s).2.2]
  have hsol' := isSolutionOn_cast (I := ThreeModel)
    (parabolicSolution_isSolutionOn (I := ThreeModel) _ hsol 0 lam⁻¹ hli h0mem) hcar hreg
  have hball : ∀ x : V, riemannianClosedBallOf (gV' 0) x (Real.sqrt lam⁻¹ * r) =
      riemannianClosedBallOf (gV 0) x r := by
    intro x
    rw [hgV0]
    exact riemannianClosedBallOf_scaleMetric lam⁻¹ hli (gV 0) x r
  have hA₂' : ∀ n, 0 < A₂ n * lam⁻¹ := fun n => mul_pos (hA₂ n) hli
  have hmetA : ∀ n, scaleMetric (A₂ n * lam⁻¹) (hA₂' n) (Pl.metric.restrictOpen W) =
      scaleMetric lam⁻¹ hli (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W)) :=
    fun n => scaleMetric_mul_eq_C11SP _ hli (hA₂ n) (hA₂' n) (by ring)
  have hsq : 0 < Real.sqrt lam⁻¹ := Real.sqrt_pos.mpr hli
  refine ⟨j, hj, fun n => A₂ n * lam⁻¹, hA₂', ?_, P₂', V, hp, hpath, tau * lam⁻¹, htau', gV',
    ?_, hsol', ?_, ?_, C, hC, Real.sqrt lam⁻¹ * r, mul_pos hsq hr, ?_, ?_, ?_⟩
  · have h1 := hrat.mul_const lam⁻¹
    rw [mul_inv_cancel₀ hlam.ne'] at h1
    refine h1.congr fun n => ?_
    ring
  · change gV' 0 = (scaleMetric lam⁻¹ hli P₂.metric).restrictOpen V
    rw [hgV0, hG0, restrictOpen_scaleMetric_C11SP]
  · intro s hs z
    have hs' : parabolicTime 0 lam⁻¹ s ∈ Icc (-tau) 0 := by
      rw [hpt, mem_Icc, (scaled_time_iff_C11SP hlam tau s).1.1,
        (scaled_time_iff_C11SP hlam tau s).1.2]
      exact hs
    change metricAlgebraicCurvatureTensorAt
      (scaleMetric lam⁻¹ hli (gV (parabolicTime 0 lam⁻¹ s))) z ∈ _
    rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
    exact algebraicCurvatureOperatorNonnegativeCone.smul_mem (hnn _ hs' z) hli.le
  · change metricScalarAt (scaleMetric lam⁻¹ hli P₂.metric) P₂.basepoint = 1
    rw [metricScalarAt_scaleMetric, hbase, inv_inv, mul_inv_cancel₀ hlam.ne']
  · rw [hball]
    exact hcpt
  · filter_upwards [hcap] with n hn
    refine ⟨?_, ?_⟩
    · rw [hball]
      exact hn.1
    · rw [hball, hmetA n, show Real.sqrt lam⁻¹ * r / 4 = Real.sqrt lam⁻¹ * (r / 4) by ring,
        riemannianClosedBallOf_scaleMetric]
      exact hn.2
  · intro eta heta
    filter_upwards [hdist (eta / Real.sqrt lam⁻¹) (div_pos heta hsq)] with n hn
    intro a ha b hb
    rw [hball] at ha hb
    have h1 := hn a ha b hb
    have e1 := edistOf_scale lam⁻¹ hli (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
      (C n a) (C n b)
    have e2 := edistOf_scale lam⁻¹ hli (gV 0) a b
    rw [hmetA n, e1, hgV0, e2, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hsq.le, ← mul_sub, abs_mul, abs_of_pos hsq]
    calc Real.sqrt lam⁻¹ * |_| < Real.sqrt lam⁻¹ * (eta / Real.sqrt lam⁻¹) :=
          mul_lt_mul_of_pos_left h1 hsq
      _ = eta := by field_simp

/-- `4` 倍放缩的闭球 = 原度量半径减半的闭球。 -/
theorem closedBall_scale_four_C11SP {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] (X : SmoothRiemannianMetric ThreeModel N) (y : N) (ρ : ℝ) :
    riemannianClosedBallOf (scaleMetric 4 four_pos X) y ρ = riemannianClosedBallOf X y (ρ / 2) := by
  have h := riemannianClosedBallOf_scaleMetric 4 four_pos X y (ρ / 2)
  have hsq4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsq4, show 2 * (ρ / 2) = ρ by ring] at h
  exact h

/-- A1 kernel 的 `λ` 孪生：`R(y)·λ = R`（在 `λ` 倍 scalar 尺度 blow up），输出 ratio `→ λ`、
base scalar `λ⁻¹`（其余逐字同 `secondBlowup_flow_of_traced_C11SP`）。 -/
theorem secondBlowup_flow_of_traced_scaled_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (chain : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = chain.tower) (θ K0 : ℝ) (hθ : 0 < θ) (hK0 : 0 < K0)
    {lam : ℝ} (hlam : 0 < lam)
    (ε C1 C2 : ℝ)
    (idx : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (idx n)).toHistory.horizon)
    (y : ∀ n, ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRy : ∀ n, metricScalarAt ((F.tower.history (idx n)).toHistory.stageMetric
      ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) (y n) * lam = R n)
    (htrace : ∀ n, (F.tower.history (idx n)).toHistory.isTracedRegion (t n) (y n)
      (Real.sqrt (R n))⁻¹ (θ / R n) (K0 * R n))
    (hage : Tendsto (fun n => (t n : ℝ) * R n) atTop atTop)
    (hcan : ∀ᶠ n in atTop,
      ∃ Wc : SpatialCanonicalWitness ((F.tower.history (idx n)).toHistory.stageMetric
          ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) ε C1 C2 (y n),
        Wc.capTubeHasNeckChart ε ∧ ∃ z ∈ connectedComponent (y n),
          C2 * metricScalarAt ((F.tower.history (idx n)).toHistory.stageMetric
            ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) z <
          metricScalarAt ((F.tower.history (idx n)).toHistory.stageMetric
            ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) (y n))
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (W : TopologicalSpace.Opens Pl.M)
    (xW : ℕ → W) (qc : ℕ → ℝ) (hqc : ∀ n, 0 < qc n)
    (hratio : Tendsto (fun n => qc n / metricScalarAt Pl.metric (xW n : Pl.M)) atTop (𝓝 lam))
    (B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel W
      ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier ∞)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hBsource : ∀ n, riemannianClosedBallOf (scaleMetric (qc n) (hqc n)
      (Pl.metric.restrictOpen W)) (xW n) R₀ ⊆ (B n).source)
    (hBbase : ∀ n, B n (xW n) = y n)
    (hcapture : ∀ n, riemannianClosedBallOf (scaleMetric (R n) (hR n)
        ((F.tower.history (idx n)).toHistory.stageMetric
          ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)))
        (y n) (R₀ / 4) ⊆ (B n) '' riemannianClosedBallOf (scaleMetric (qc n) (hqc n)
          (Pl.metric.restrictOpen W)) (xW n) R₀)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ z ∈ riemannianClosedBallOf (scaleMetric (qc n) (hqc n) (Pl.metric.restrictOpen W))
        (xW n) R₀, ∀ w : TangentSpace ThreeModel z,
        (1 - eta) * (scaleMetric (qc n) (hqc n) (Pl.metric.restrictOpen W)).inner z w w ≤
          (scaleMetric (R n) (hR n)
            ((F.tower.history (idx n)).toHistory.stageMetric
              ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))).inner
          (B n z) (mfderiv ThreeModel ThreeModel (B n) z w)
          (mfderiv ThreeModel ThreeModel (B n) z w) ∧
        (scaleMetric (R n) (hR n)
            ((F.tower.history (idx n)).toHistory.stageMetric
              ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))).inner
          (B n z) (mfderiv ThreeModel ThreeModel (B n) z w)
          (mfderiv ThreeModel ThreeModel (B n) z w) ≤
            (1 + eta) * (scaleMetric (qc n) (hqc n) (Pl.metric.restrictOpen W)).inner z w w) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 lam) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (gV : ℝ → SmoothRiemannianMetric ThreeModel V),
        gV 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := gV } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ s ∈ Icc (-tau) 0, ∀ z : V, metricAlgebraicCurvatureTensorAt (gV s) z ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = lam⁻¹ ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop,
            riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆
                (C n) '' riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf
                  (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                  (C n a) (C n b)).toReal -
                (riemannianEDistOf (gV 0) a b).toReal| < eta := by
  have hjets : ∀ Rr : ℝ, 0 < Rr → Rr < 1 → ∀ k : ℕ, ∃ J : ℝ, 0 ≤ J ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound
        ({ M := ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier
           basepoint := y n
           metric := scaleMetric (R n) (hR n)
            ((F.tower.history (idx n)).toHistory.stageMetric
              ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) } :
          PointedRiemannianManifold.{u, 0, 0} ThreeModel) (y n) Rr k J := by
    intro Rr hRr hRr1 k
    obtain ⟨J, hJ, hin⟩ := exists_inner_jets_of_traced_region_CXSP Rr 1 θ K0 hRr.le hRr1 hθ hK0
    refine ⟨J k, zero_le_one.trans (hJ k), Eventually.of_forall fun n => ?_⟩
    have htr : (F.tower.history (idx n)).toHistory.isTracedRegion (t n) (y n)
        (1 / Real.sqrt (R n)) (θ / R n) (K0 * R n) := by
      rw [one_div]
      exact htrace n
    intro w hw
    exact hin _ (t n) (y n) (R n) (hR n) htr k w hw
  have hconv := exists_stage_pointed_convergence_of_jets_CXSP
    (fun n => (F.tower.history (idx n)).toHistory.stageAt (t n))
    (fun n => (F.tower.history (idx n)).toHistory.stageMetric
      ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))
    R hR y ε C1 C2 one_pos hcan hjets
  obtain ⟨j, hj, _rad, _hrad, _hradlim, P₂, maps2, M2, hcan2, _hradial2, _hcompact2,
    _hcapture2, _hmetric2⟩ := hconv
  have hscalarOne : metricScalarAt P₂.metric P₂.basepoint = lam⁻¹ :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M2 hcan2 (by
      intro n
      change metricScalarAt (scaleMetric (R (j n)) (hR (j n))
        ((F.tower.history (idx (j n))).toHistory.stageMetric
          ((F.tower.history (idx (j n))).toHistory.activeStage (t (j n))) (t (j n))))
          (y (j n)) = lam⁻¹
      have hs : metricScalarAt ((F.tower.history (idx (j n))).toHistory.stageMetric
          ((F.tower.history (idx (j n))).toHistory.activeStage (t (j n))) (t (j n)))
          (y (j n)) ≠ 0 := by
        intro h0
        have h1 := hRy (j n)
        rw [h0, zero_mul] at h1
        exact (hR (j n)).ne' h1.symm
      have hl : lam ≠ 0 := hlam.ne'
      rw [metricScalarAt_scaleMetric, ← hRy (j n)]
      field_simp)
  obtain ⟨V, hp, hpath, _hcptV, N₀, _hsrc, G, hG0, hsol, hnn, C, hC, r, hr, hcpt, hcap,
      hdist⟩ :=
    guard_stageLocalFlow_endComparison_C11SP chain F hTower θ K0 hθ hK0 idx t y R hR htrace
      hage j hj P₂ _ M2 hcan2
      (fun n => scaleMetric (qc (j n)) (hqc (j n)) (Pl.metric.restrictOpen W))
      (fun n => xW (j n)) (fun n => B (j n)) hR₀ (fun n => hBsource (j n))
      (fun n => hBbase (j n)) (fun n => hcapture (j n))
      (fun eta heta => hj.tendsto_atTop.eventually (hBconv eta heta))
  have hjN : StrictMono (fun n => j (n + N₀)) :=
    hj.comp fun a b hab => Nat.add_lt_add_right hab N₀
  refine ⟨fun n => j (n + N₀), hjN, fun n => qc (j (n + N₀)), fun n => hqc (j (n + N₀)),
    hratio.comp hjN.tendsto_atTop, P₂, V, hp, hpath, θ / 2, half_pos hθ, G, hG0, hsol, hnn,
    hscalarOne, C, hC, r, hr, hcpt, hcap, hdist⟩


/-- A1 `secondBlowup_assemble_C11SP` 的 neck 孪生：`hpay` 换成 S16 neck traced region 形
（G47：半径 `1/(2√R)`、深度 `1/R`、界 `1200R`）；内部取 `λ = 4`、`θ = 4`、`K0 = 300` 喂
`secondBlowup_flow_of_traced_scaled_C11SP`，再 `secondFlow_rescale_C11SP` 回 base scalar 1。 -/
theorem secondBlowup_assemble_neck_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γf : ClosedBirthConstants} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (hb : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime)
    (A : ℝ) (hA : 0 < A) (Hbase : ℝ) (hHpos : 0 < Hbase) (rho : ℝ)
    (hrhoH : rho / Real.sqrt Hbase ≤ A + 1 / 2)
    (idx : ℕ → ℕ)
    (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).toHistory.horizon)
    (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (htlim : Tendsto (fun i => (t i : ℝ)) atTop atTop)
    (htime : ∀ i, 2 * r i ^ 2 < (t i : ℝ))
    (hsmall : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory (t i) (p i)
      (r i))
    (hvolF : ∀ i, ENNReal.ofReal ((2 * A + 3)⁻¹ * r i ^ 3) ≤
      ballVolume ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i))
    (hanchor : ∀ i, riemannianEDistOf ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (anchor i) ≤
      ENNReal.ofReal (A * r i))
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQeq : ∀ i, Q i = Hbase * (r i ^ 2)⁻¹)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (Phi : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier
            basepoint := anchor i
            metric := scaleMetric (Q i) (hQ i)
              ((F.tower.history (idx i)).toHistory.stageMetric
                ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData Phi)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n)
    (hradial : ∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho)
    (W : TopologicalSpace.Opens Pl.M) (xW : ℕ → W) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hQW : ∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M))
    (hQWlim : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop)
    (hcompactW : ∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M)))))
    (N : ℕ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hpay : ∀ k : ℕ → ℕ, StrictMono k → ∀ m : ℕ,
      (F.tower.history (idx (f (ψ (k m))))).toHistory.isTracedRegion (t (f (ψ (k m))))
        (Phi.map (ψ (k m)) (xW (m + N) : Pl.M))
        (1 / (2 * Real.sqrt (metricScalarAt
          ((F.tower.history (idx (f (ψ (k m))))).toHistory.stageMetric
            ((F.tower.history (idx (f (ψ (k m))))).toHistory.activeStage (t (f (ψ (k m)))))
            (t (f (ψ (k m))))) (Phi.map (ψ (k m)) (xW (m + N) : Pl.M)))))
        (metricScalarAt ((F.tower.history (idx (f (ψ (k m))))).toHistory.stageMetric
          ((F.tower.history (idx (f (ψ (k m))))).toHistory.activeStage (t (f (ψ (k m)))))
          (t (f (ψ (k m))))) (Phi.map (ψ (k m)) (xW (m + N) : Pl.M)))⁻¹
        (1200 * metricScalarAt ((F.tower.history (idx (f (ψ (k m))))).toHistory.stageMetric
          ((F.tower.history (idx (f (ψ (k m))))).toHistory.activeStage (t (f (ψ (k m)))))
          (t (f (ψ (k m))))) (Phi.map (ψ (k m)) (xW (m + N) : Pl.M)))) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (gV : ℝ → SmoothRiemannianMetric ThreeModel V),
        gV 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := gV } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ s ∈ Icc (-tau) 0, ∀ z : V, metricAlgebraicCurvatureTensorAt (gV s) z ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = 1 ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop,
            riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆
                (C n) '' riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf
                  (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                  (C n a) (C n b)).toReal -
                (riemannianEDistOf (gV 0) a b).toReal| < eta := by
  obtain ⟨Kb, Tb, _hKb, _hTb, hcanTC⟩ := hb (2 * A + 3) (by linarith only [hA])
  have htail : ∀ m, ∀ᶠ n in atTop,
      riemannianEDistOf ((F.tower.history (idx (f n))).toHistory.stageMetric
        ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n)))
        (p (f n)) (Phi.map n (xW (m + N) : Pl.M)) ≤
      ENNReal.ofReal ((A + rho / Real.sqrt Hbase) * r (f n)) := fun m =>
    eventually_stage_pointed_seed_distance_CXSP
      (fun i => (F.tower.history (idx i)).toHistory.stageAt (t i))
      (fun i => (F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i))
      Q hQ anchor Pl Phi M hcanonical p r hr hHpos hA.le hQeq hanchor _ (hradial _)
  choose Nm hNm using fun m => eventually_atTop.mp (hψ.tendsto_atTop.eventually (htail m))
  obtain ⟨η, hη, hηN⟩ := exists_strictMono_ge_prefix_C11SP Nm
  have hδ : StrictMono (fun n => ψ (η n)) := hψ.comp hη
  have hcan' : ∀ n, (M.compSubseq (fun n => ψ (η n)) hδ).domain n =
      CanonicalMetricCompactness.canonicalSourceData (Phi.compSubseq (fun n => ψ (η n)) hδ) n := by
    intro n
    change (M.domain (ψ (η n))).compSubseq (fun n => ψ (η n)) hδ n = _
    rw [hcanonical (ψ (η n))]
    rfl
  have hR₀2 : 0 < R₀ / 2 := half_pos hR₀
  have hcompactW2 : ∀ m, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W)
      (xW (m + N)) (4 * (R₀ / 2) / Real.sqrt (metricScalarAt Pl.metric (xW (m + N) : Pl.M)))) :=
    fun m => (hcompactW (m + N)).of_isClosed_subset
      (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
      (riemannianClosedBallOf_mono _ _ (by gcongr; linarith only [hR₀]))
  obtain ⟨k, hk, hq1, hratio, hcmp⟩ := exists_scalar_rescaled_source_comparison _ _ Pl
    (Phi.compSubseq (fun n => ψ (η n)) hδ) (M.compSubseq (fun n => ψ (η n)) hδ) hcan' W
    (fun m => xW (m + N)) hR₀2 (fun m => hQW (m + N)) hcompactW2
  have hpay' := fun m => hpay (fun n => η (k n)) (hη.comp hk) m
  have hiMono : StrictMono (fun m => f (ψ (η (k m)))) := hf.comp (hδ.comp hk)
  let iF : ℕ → ℕ := fun m => f (ψ (η (k m)))
  let gS : ∀ m, ((F.tower.history (idx (iF m))).toHistory.stageAt (t (iF m))).Metric :=
    fun m => (F.tower.history (idx (iF m))).toHistory.stageMetric
      ((F.tower.history (idx (iF m))).toHistory.activeStage (t (iF m))) (t (iF m))
  let yF : ∀ m, ((F.tower.history (idx (iF m))).toHistory.stageAt (t (iF m))).Carrier :=
    fun m => Phi.map (ψ (η (k m))) (xW (m + N) : Pl.M)
  let R₁ : ℕ → ℝ := fun m => metricScalarAt (gS m) (yF m)
  let qo : ℕ → ℝ := fun m => metricScalarAt (scaleMetric (Q (iF m)) (hQ (iF m)) (gS m)) (yF m)
  have hR₁ : ∀ m, 0 < R₁ m := by
    intro m
    have h2 : 0 < 2 * Real.sqrt (R₁ m) := one_div_pos.mp (hpay' m).1
    exact Real.sqrt_pos.mp (by linarith only [h2])
  have hqo : ∀ m, 0 < qo m := fun m => lt_of_lt_of_le zero_lt_one (hq1 m)
  have hReq : ∀ m, R₁ m = qo m * Q (iF m) := by
    intro m
    change metricScalarAt (gS m) (yF m) =
      metricScalarAt (scaleMetric (Q (iF m)) (hQ (iF m)) (gS m)) (yF m) * Q (iF m)
    rw [metricScalarAt_scaleMetric, inv_mul_eq_div, div_mul_cancel₀ _ (hQ (iF m)).ne']
  let R₂ : ℕ → ℝ := fun m => 4 * R₁ m
  let qc : ℕ → ℝ := fun m => 4 * qo m
  have hR₂ : ∀ m, 0 < R₂ m := fun m => mul_pos four_pos (hR₁ m)
  have hqc : ∀ m, 0 < qc m := fun m => mul_pos four_pos (hqo m)
  have hmeq1 : ∀ m, scaleMetric (R₁ m) (hR₁ m) (gS m) =
      scaleMetric (qo m) (hqo m) (scaleMetric (Q (iF m)) (hQ (iF m)) (gS m)) := fun m =>
    scaleMetric_mul_eq_C11SP (gS m) (hqo m) (hQ (iF m)) (hR₁ m) (hReq m)
  have hmeq2 : ∀ m, scaleMetric (R₂ m) (hR₂ m) (gS m) =
      scaleMetric 4 four_pos (scaleMetric (R₁ m) (hR₁ m) (gS m)) := fun m =>
    scaleMetric_mul_eq_C11SP (gS m) four_pos (hR₁ m) (hR₂ m) rfl
  have hmeqW : ∀ m, scaleMetric (qc m) (hqc m) (Pl.metric.restrictOpen W) =
      scaleMetric 4 four_pos (scaleMetric (qo m) (hqo m) (Pl.metric.restrictOpen W)) := fun m =>
    scaleMetric_mul_eq_C11SP _ four_pos (hqo m) (hqc m) rfl
  have hQWN : Tendsto (fun m => metricScalarAt Pl.metric (xW (m + N) : Pl.M)) atTop atTop :=
    hQWlim.comp (tendsto_add_atTop_nat N)
  have hratio' : Tendsto (fun m => qo m / metricScalarAt Pl.metric (xW (m + N) : Pl.M))
      atTop (𝓝 1) := hratio
  have hratio4 : Tendsto (fun m => qc m / metricScalarAt Pl.metric (xW (m + N) : Pl.M))
      atTop (𝓝 4) := by
    have h := hratio'.const_mul 4
    rw [mul_one] at h
    refine h.congr fun m => ?_
    change 4 * (qo m / _) = 4 * qo m / _
    ring
  have hqtop : Tendsto qo atTop atTop := by
    have hhalf : ∀ᶠ m in atTop,
        (1 / 2 : ℝ) < qo m / metricScalarAt Pl.metric (xW (m + N) : Pl.M) :=
      hratio'.eventually (eventually_gt_nhds (by norm_num))
    apply tendsto_atTop_mono' atTop _ (hQWN.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hhalf] with m hm
    have hRp : 0 < metricScalarAt Pl.metric (xW (m + N) : Pl.M) := by
      linarith only [hQW (m + N)]
    have h := (lt_div_iff₀ hRp).mp hm
    linarith only [h]
  have htQ : ∀ i, 2 * Hbase ≤ (t i : ℝ) * Q i := by
    intro i
    have hr2 : 0 < r i ^ 2 := pow_pos (hr i) 2
    have h1 : 2 ≤ (t i : ℝ) * (r i ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hr2]
      linarith only [htime i]
    rw [hQeq i]
    calc 2 * Hbase = Hbase * 2 := by ring
      _ ≤ Hbase * ((t i : ℝ) * (r i ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 hHpos.le
      _ = (t i : ℝ) * (Hbase * (r i ^ 2)⁻¹) := by ring
  have hage : Tendsto (fun m => (t (iF m) : ℝ) * R₂ m) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hqtop.const_mul_atTop (by linarith only [hHpos] :
      (0 : ℝ) < 2 * Hbase))
    refine Eventually.of_forall fun m => ?_
    change 2 * Hbase * qo m ≤ (t (iF m) : ℝ) * (4 * R₁ m)
    rw [hReq m]
    have h3 : 0 ≤ qo m := (hqo m).le
    have h2 : 2 * Hbase * qo m ≤ (t (iF m) : ℝ) * Q (iF m) * qo m :=
      mul_le_mul_of_nonneg_right (htQ (iF m)) h3
    have h4 : 0 ≤ (t (iF m) : ℝ) * Q (iF m) * qo m :=
      le_trans (mul_nonneg (by linarith only [hHpos]) h3) h2
    nlinarith only [h2, h4]
  have hiT : Tendsto (fun m => (t (iF m) : ℝ)) atTop atTop :=
    htlim.comp hiMono.tendsto_atTop
  have hcan : ∀ᶠ m in atTop,
      ∃ Wc : SpatialCanonicalWitness (gS m) ε C1 C2 (yF m),
        Wc.capTubeHasNeckChart ε ∧ ∃ z ∈ connectedComponent (yF m),
          C2 * metricScalarAt (gS m) z < metricScalarAt (gS m) (yF m) := by
    filter_upwards [hiT.eventually_ge_atTop Tb,
      hqtop.eventually_ge_atTop (max Kb (4 * max C2 1) / Hbase)] with m hT hq
    have hyball : yF m ∈ riemannianBallOf (gS m) (p (iF m)) ((2 * A + 3) * r (iF m)) := by
      apply (hNm m (η (k m)) (hηN m (k m) (hk.id_le m))).trans_lt
      apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by linarith only [hA]) (hr _))).mpr
      apply mul_lt_mul_of_pos_right _ (hr _)
      linarith only [hrhoH, hA]
    have hhigh : max Kb (4 * max C2 1) * (r (iF m) ^ 2)⁻¹ ≤
        metricScalarAt (gS m) (yF m) := by
      change _ ≤ R₁ m
      rw [hReq m, hQeq (iF m)]
      have h := (div_le_iff₀ hHpos).mp hq
      have hi : 0 ≤ (r (iF m) ^ 2)⁻¹ := by positivity
      calc max Kb (4 * max C2 1) * (r (iF m) ^ 2)⁻¹ ≤ (qo m * Hbase) * (r (iF m) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right h hi
        _ = qo m * (Hbase * (r (iF m) ^ 2)⁻¹) := by ring
    obtain ⟨Wc, hchart, hpcomp, hgap⟩ := exists_seed_volume_base_CXSP (hsmall (iF m)) hyball
      hhigh (fun z hz hzR => (hcanTC (idx (iF m)) (t (iF m)) (p (iF m)) (r (iF m)) hT
        (htime _) (hsmall _) (hvolF _) z hz hzR).1)
    exact ⟨Wc, hchart, p (iF m), hpcomp, hgap⟩
  let Bk : ∀ m, PartialDiffeomorph ThreeModel ThreeModel W
      ((F.tower.history (idx (iF m))).toHistory.stageAt (t (iF m))).Carrier ∞ :=
    fun m => (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := ThreeModel) W
      ⟨xW (0 + N)⟩).trans ((Phi.compSubseq (fun n => ψ (η n)) hδ).partialDiffeomorph (k m))
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hsq4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have htrace4 : ∀ m, (F.tower.history (idx (iF m))).toHistory.isTracedRegion (t (iF m)) (yF m)
      (Real.sqrt (R₂ m))⁻¹ (4 / R₂ m) (300 * R₂ m) := by
    intro m
    have hR1 := (hR₁ m).ne'
    have e1 : (Real.sqrt (R₂ m))⁻¹ = 1 / (2 * Real.sqrt (R₁ m)) := by
      change (Real.sqrt (4 * R₁ m))⁻¹ = _
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsq4, one_div]
    have e2 : 4 / R₂ m = (R₁ m)⁻¹ := by
      change 4 / (4 * R₁ m) = _
      field_simp
    have e3 : 300 * R₂ m = 1200 * R₁ m := by
      change 300 * (4 * R₁ m) = _
      ring
    rw [e1, e2, e3]
    exact hpay' m
  have hBsource4 : ∀ m, riemannianClosedBallOf (scaleMetric (qc m) (hqc m)
      (Pl.metric.restrictOpen W)) (xW (m + N)) R₀ ⊆ (Bk m).source := by
    intro m
    rw [hmeqW m, closedBall_scale_four_C11SP]
    exact (hcmp m).2.1
  have hcapture4 : ∀ m, riemannianClosedBallOf (scaleMetric (R₂ m) (hR₂ m) (gS m)) (yF m)
      (R₀ / 4) ⊆ (Bk m) '' riemannianClosedBallOf (scaleMetric (qc m) (hqc m)
        (Pl.metric.restrictOpen W)) (xW (m + N)) R₀ := by
    intro m
    rw [hmeqW m, hmeq2 m, closedBall_scale_four_C11SP, closedBall_scale_four_C11SP, hmeq1 m,
      show R₀ / 4 / 2 = R₀ / 2 / 4 by ring]
    exact (hcmp m).2.2.2.1
  have hBconv4 : ∀ eta : ℝ, 0 < eta → ∀ᶠ m in atTop,
      ∀ z ∈ riemannianClosedBallOf (scaleMetric (qc m) (hqc m) (Pl.metric.restrictOpen W))
        (xW (m + N)) R₀, ∀ w : TangentSpace ThreeModel z,
        (1 - eta) * (scaleMetric (qc m) (hqc m) (Pl.metric.restrictOpen W)).inner z w w ≤
          (scaleMetric (R₂ m) (hR₂ m) (gS m)).inner
          (Bk m z) (mfderiv ThreeModel ThreeModel (Bk m) z w)
          (mfderiv ThreeModel ThreeModel (Bk m) z w) ∧
        (scaleMetric (R₂ m) (hR₂ m) (gS m)).inner
          (Bk m z) (mfderiv ThreeModel ThreeModel (Bk m) z w)
          (mfderiv ThreeModel ThreeModel (Bk m) z w) ≤
            (1 + eta) * (scaleMetric (qc m) (hqc m) (Pl.metric.restrictOpen W)).inner z w w := by
    intro eta heta
    filter_upwards [hlim.eventually (eventually_lt_nhds heta)] with m hm
    intro z hz w
    rw [hmeqW m, closedBall_scale_four_C11SP] at hz
    have hh := (hcmp m).2.2.1 z hz w
    have hg := metric_inner_self_nonneg
      (scaleMetric (qo m) (hqo m) (Pl.metric.restrictOpen W)) z w
    rw [hmeqW m, hmeq2 m, hmeq1 m,
      scaleMetric_inner 4 four_pos (scaleMetric (qo m) (hqo m) (Pl.metric.restrictOpen W)),
      scaleMetric_inner 4 four_pos
        (scaleMetric (qo m) (hqo m) (scaleMetric (Q (iF m)) (hQ (iF m)) (gS m)))]
    refine ⟨?_, ?_⟩
    · have a1 := (mul_le_mul_of_nonneg_right
        (show 1 - eta ≤ 1 - 1 / ((m : ℝ) + 2) by linarith only [hm]) hg).trans hh.1
      have a2 := mul_le_mul_of_nonneg_left a1 (show (0 : ℝ) ≤ 4 by norm_num)
      calc _ = 4 * ((1 - eta) * (scaleMetric (qo m) (hqo m)
            (Pl.metric.restrictOpen W)).inner z w w) := by ring
        _ ≤ _ := a2
    · have a1 := hh.2.trans (mul_le_mul_of_nonneg_right
        (show 1 + 1 / ((m : ℝ) + 2) ≤ 1 + eta by linarith only [hm]) hg)
      have a2 := mul_le_mul_of_nonneg_left a1 (show (0 : ℝ) ≤ 4 by norm_num)
      calc _ ≤ 4 * ((1 + eta) * (scaleMetric (qo m) (hqo m)
            (Pl.metric.restrictOpen W)).inner z w w) := a2
        _ = _ := by ring
  have hker := secondBlowup_flow_of_traced_scaled_C11SP S F hTower 4 300 four_pos
    (by norm_num) four_pos ε C1 C2 (fun m => idx (iF m)) (fun m => t (iF m)) yF R₂ hR₂
    (fun m => mul_comm (R₁ m) 4) htrace4 hage hcan Pl W (fun m => xW (m + N)) qc hqc hratio4
    Bk hR₀ hBsource4 (fun _ => rfl) hcapture4 hBconv4
  obtain ⟨j, hj, A₂, hA₂, hrat, P₂, V, hp, hpath, tau, htau, gV, h1, h2, h3, h4, C, hC, rr, hrr,
      h5, h6, h7⟩ := secondFlow_rescale_C11SP Pl W (fun m => xW (m + N)) four_pos hker
  exact ⟨fun n => j n + N, fun a b hab => Nat.add_lt_add_right (hj hab) N, A₂, hA₂, hrat, P₂, V,
    hp, hpath, tau, htau, gV, h1, h2, h3, h4, C, hC, rr, hrr, h5, h6, h7⟩


/-- **G3 native cone 点 flow**：native 第一层数据（同 A1 `guard_secondBlowupFlow_C11SP` 的输入，
**无 `nr ≤ r`**）+ 点列 `xW` 的映射点处 eventual 的 S16 neck traced region（G47 形）⇒
冻结 hflowN flow 子句对该 `xW` 的结论（`hneck` 只需对 `xW` 的尾段成立；内部平移 `N`）。
`hneck` 是 kernel 输入槽（同 A1 的 `hpay`）：ray 点列上由
G33（实际最短段双端 scalar gap ⇒ neck）+ G47 付，见 state §G3。 -/
theorem native_coneFlow_of_neckTraced_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γf : ClosedBirthConstants} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (hb : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime)
    (A : ℝ) (hA : 0 < A) (Hbase : ℝ) (hHbase : 4 ≤ Hbase) (rho : ℝ)
    (hrhoB : rho + 2 ≤ A * Real.sqrt Hbase + 3)
    (idx : ℕ → ℕ)
    (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).toHistory.horizon)
    (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (htlim : Tendsto (fun i => (t i : ℝ)) atTop atTop)
    (htime : ∀ i, 2 * r i ^ 2 < (t i : ℝ))
    (hsmall : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory (t i) (p i)
      (r i))
    (hvol : ∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
      ballVolume ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i))
    (hanchor : ∀ i, riemannianEDistOf ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (anchor i) ≤
      ENNReal.ofReal (A * r i))
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQeq : ∀ i, Q i = Hbase * (r i ^ 2)⁻¹)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (Phi : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier
            basepoint := anchor i
            metric := scaleMetric (Q i) (hQ i)
              ((F.tower.history (idx i)).toHistory.stageMetric
                ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData Phi)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n)
    (hradial : ∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho)
    (W : TopologicalSpace.Opens Pl.M) (xW : ℕ → W) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hQW : ∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M))
    (hQWlim : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop)
    (hcompactW : ∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M)))))
    (hneck : ∀ᶠ m in atTop, ∀ᶠ i in atTop,
      (F.tower.history (idx (f i))).toHistory.isTracedRegion (t (f i))
        (Phi.map i (xW m : Pl.M))
        (1 / (2 * Real.sqrt (metricScalarAt
          ((F.tower.history (idx (f i))).toHistory.stageMetric
            ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
          (Phi.map i (xW m : Pl.M)))))
        (metricScalarAt ((F.tower.history (idx (f i))).toHistory.stageMetric
            ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
          (Phi.map i (xW m : Pl.M)))⁻¹
        (1200 * metricScalarAt ((F.tower.history (idx (f i))).toHistory.stageMetric
            ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
          (Phi.map i (xW m : Pl.M)))) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (g : ℝ → SmoothRiemannianMetric ThreeModel V),
        g 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = 1 ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop,
            riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆
                (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf
                  (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                  (C n a) (C n b)).toReal -
                (riemannianEDistOf (g 0) a b).toReal| < eta := by
  have hHpos : 0 < Hbase := by linarith only [hHbase]
  have hsqrtH : 2 ≤ Real.sqrt Hbase := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]
    exact Real.sqrt_le_sqrt hHbase
  have hrhoH : rho / Real.sqrt Hbase ≤ A + 1 / 2 := by
    rw [div_le_iff₀ (by linarith only [hsqrtH])]
    nlinarith only [hrhoB, hsqrtH, hA]
  have hvolF : ∀ i, ENNReal.ofReal ((2 * A + 3)⁻¹ * r i ^ 3) ≤
      ballVolume ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i) :=
    fun i => seed_volume_of_parameter_le_CXSP (hsmall i) hA (by linarith only [hA]) (hvol i)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hneck
  choose Nm hNm using fun m => eventually_atTop.mp (hN (m + N) (Nat.le_add_left N m))
  obtain ⟨ψ, hψ, hψN⟩ := exists_strictMono_ge_prefix_C11SP Nm
  exact secondBlowup_assemble_neck_C11SP S F hTower hb A hA Hbase hHpos rho hrhoH idx t p anchor
    r hr htlim htime hsmall hvolF hanchor Q hQ hQeq f hf Pl Phi M hcanonical hradial W xW R₀ hR₀
    hQW hQWlim hcompactW N ψ hψ
    (fun k hk m => hNm m (ψ (k m)) (hψN m (k m) (hk.id_le m)))

end GC.LongTime.Ch11
