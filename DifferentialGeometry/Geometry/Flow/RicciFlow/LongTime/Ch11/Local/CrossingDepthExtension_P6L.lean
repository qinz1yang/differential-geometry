import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingWindowAnchorBound2_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionTimeZeroScalarBound_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingDepthExtension

/-!
# L7 任意深度的驱动（O-CH11-P6D2 G2，后缀 `_P6L`）

树内全局版 = `CrossingContinuationLeaf.crossingContinuation_holds`（`:130`）的 maximal-depth 段 +
`CrossingTimeZeroBound:276`（初始正深度）。这里写成 **`ObservedHistory` 序列形的抽象驱动**
`exists_subseq_forall_depthExtendable_P6L`：

* 输入（与 history 框架无关的两条"单步"）：`hsurvive`（基点 ball anchor `R ≤ Q R` + 深度
  `4·Cst·Q·T ≤ 1` ⇒ traced region；= P6B L7 单窗口 / `CrossingTimeZeroBound:108`）与 `hextend`
  （深度 `< Tstar` 全可延伸 + window anchor `M` ⇒ 深度 `Tstar + 1/(32(Cst+1)(M+1))`；
  = `CrossingDepthExtension.depthExtendable_add_of_windowAnchorBound`）。二者在 G3 由
  `RetainedCoreHistory` + `extendAt` 的数据前提（records / pinching / slab 导数 / `¬ CapWindowPoint`）
  直接实例化；
* `hanchor0`：基点时刻每个半径一个 `Q(A)` 的 ball anchor（L6 = `SLT:249_P6L` 的输出形）；
* trace-local 前提（`hseed` / `hkappa` / `hpinch` / `hwit` / `hderiv` / `hbcad`），与 G2 anchor
  `exists_subseq_windowAnchorBound_of_depthExtendable_P6L` 逐字相同。

证明：(1) `hanchor0` + `hsurvive` ⇒ 深度 schedule `τs k = 1/(4(Cst+1)Q(k+3))` 的 traced regions；
(2) 局部化的基点时刻一致界 `exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule_P6L` ⇒
`C₀`（与半径无关）⇒ 初始正深度 `1/(4(Cst+1)max(C₀,2))`；(3) `exists_strictMono_maximal_depth`：全深度
⇒ 结论；最大 `Tstar` ⇒ G2 anchor（只用深度 `< Tstar` 的已控 traced regions）+ `hextend` ⇒ 深度
`> Tstar`，与极大性矛盾。

**D-9.5**：escape / anchor 只在已控深度 `T' < Tstar` 上产生（`hall`），延伸由 `hextend`（树内
`depthExtendable_add_of_windowAnchorBound`：沿 trace 的 ODE 比较 +
`exists_isTracedRegion_or_capWindowPoint_at_scale`）
完成；没有任何一步在深度 `Tstar` 的球或未控球上调用控制（树内无 `BufferedParabolicControl`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

/-- **L7 任意深度（抽象驱动）**：`hsurvive` / `hextend` 两条单步 + 基点 anchor + trace-local 前提 ⇒
存在子列 `σ`，**所有深度** `T > 0` 都 depth-extendable（即 P6D G2 要的 `htraced`，沿 `σ`）。 -/
theorem exists_subseq_forall_depthExtendable_P6L
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n) →
        (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n)
    (hextend : ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
          ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
          (A / Real.sqrt (R (σ i))),
      ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
        (w : ℝ) = ts (σ i) - T' / R (σ i) →
      ∀ (hwt : w ≤ ts (σ i))
        (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
          ((Hs (σ i)).activeStage (ts (σ i)))
          ((Hs (σ i)).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
          (Bt.point ((Hs (σ i)).activeStage w) le_rfl
            ((Hs (σ i)).activeStage_mono hwt)) ≤
          M * R (σ i)) →
      DepthExtendable Hs ts ys R σ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwit : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    {Ctime : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderiv : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2)
    (hbcad : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T := by
  have hC0 : (0 : ℝ) ≤ Cst := Cst.coe_nonneg
  -- (1) 深度 schedule：基点 anchor（L6 形，`Q` 依赖半径）+ 单窗口 survival
  choose Q hQ2 hQev using fun k : ℕ => hanchor0 ((k + 3 : ℕ) : ℝ) (by positivity)
  have hτs0 : ∀ k : ℕ, 0 < 1 / (4 * ((Cst : ℝ) + 1) * Q k) := fun k => by
    have := hQ2 k
    positivity
  have hτs1 : ∀ k : ℕ, 1 / (4 * ((Cst : ℝ) + 1) * Q k) ≤ 1 := fun k => by
    have := hQ2 k
    rw [div_le_one (by positivity)]
    nlinarith
  have hstepk : ∀ k : ℕ, 4 * (Cst : ℝ) * Q k * (1 / (4 * ((Cst : ℝ) + 1) * Q k)) ≤ 1 := by
    intro k
    have hQ0 : 0 < Q k := by linarith [hQ2 k]
    rw [show 4 * (Cst : ℝ) * Q k * (1 / (4 * ((Cst : ℝ) + 1) * Q k)) =
      (Cst : ℝ) / ((Cst : ℝ) + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  have htr : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (Hs n).isTracedRegion (ts n) (ys n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (1 / (4 * ((Cst : ℝ) + 1) * Q k) / R n) (K * R n) := by
    intro k
    obtain ⟨K, hK, hev⟩ := hsurvive ((k + 3 : ℕ) : ℝ) _ (Q k) (by positivity) (hτs0 k) (hQ2 k)
      (hstepk k)
    exact ⟨K, hK, by filter_upwards [hev, hQev k] with n hn hq using hn hq⟩
  -- (2) 基点时刻一致界（局部化的 `TimeZeroScalarBound`）⇒ 初始正深度
  have hqsN : ∀ n, qs n ≤ R n * Cs := fun n => (hqs n).trans_eq (mul_comm _ _)
  obtain ⟨ψ, hψ, C₀, -, hball⟩ := exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule_P6L
    Hs ts ys R hR hRlim (fun k => 1 / (4 * ((Cst : ℝ) + 1) * Q k)) hτs0 hτs1 htr hr₀ hw hseed hκ
    ρnc hkappa hPhi hpinch hε hεN hqsN hwit
  have hQ₀ : 2 ≤ max C₀ 2 := le_max_right _ _
  have hstep₀ : 4 * (Cst : ℝ) * max C₀ 2 * (1 / (4 * ((Cst : ℝ) + 1) * max C₀ 2)) ≤ 1 := by
    rw [show 4 * (Cst : ℝ) * max C₀ 2 * (1 / (4 * ((Cst : ℝ) + 1) * max C₀ 2)) =
      (Cst : ℝ) / ((Cst : ℝ) + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  have hbase : DepthExtendable Hs ts ys R ψ (1 / (4 * ((Cst : ℝ) + 1) * max C₀ 2)) := by
    intro A hA
    obtain ⟨K, hK, hev⟩ := hsurvive A _ (max C₀ 2) hA (by positivity) hQ₀ hstep₀
    refine ⟨K, hK, ?_⟩
    filter_upwards [hball A hA, hψ.tendsto_atTop.eventually hev] with i hi hn
    exact hn fun z hz => (hi z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hR (ψ i)).le)
  -- (3) maximal-depth 二分（`CrossingContinuationLeaf:130` 的驱动段）
  obtain ⟨ψ', hψ', hdich⟩ := exists_strictMono_maximal_depth
    (fun σ T => DepthExtendable Hs ts ys R σ T)
    (fun _ _ _ hT' hle h => DepthExtendable.mono_depth h hR hT' hle)
    (fun _ _ _ hψ h => DepthExtendable.comp h hψ)
    (fun _ _ _ hσ h => DepthExtendable.congr h hσ) id
    ⟨ψ, hψ, _, by positivity, hbase⟩
  rcases hdich with hall | ⟨Tstar, hT, hall, hmax⟩
  · exact ⟨id ∘ ψ', strictMono_id.comp hψ', hall⟩
  · -- Tstar 分支：已控深度（`< Tstar`）的 window anchor（G2 `:555_P6L`）+ 延伸 ⇒ 与极大性矛盾
    exfalso
    obtain ⟨ψ₂, hψ₂, M, hM, hanc⟩ := exists_subseq_windowAnchorBound_of_depthExtendable_P6L
      Hs ts ys R hR hRlim (strictMono_id.comp hψ') hT hall hr₀ hw hseed hκ ρnc hradii hkappa hPhi
      hpinch hε hεX hqs hwit hqcan hderiv hbcad
    refine hmax ψ₂ hψ₂ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1)))
      (lt_add_of_pos_right _ (by positivity)) ?_
    exact hextend ((id ∘ ψ') ∘ ψ₂) ((strictMono_id.comp hψ').comp hψ₂) Tstar M hT hM
      (fun T hT0 hTT => DepthExtendable.comp (hall T hT0 hTT) hψ₂) hanc

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
