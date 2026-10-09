import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AncientWitnessP6D

/-!
# P6 精度解耦：`ε_in`（compactness / cone 小性）与 `η_out`（模型输出小性）分离（S-CH11-PREC G1，后缀 `_P6P`）

R-C11-5 D-13 "精度解耦本身——YES"：`P6AncientWitnessP6D`
（`exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D`）的证明里 ε 只被用在两个互相独立的
调用里：
* `hB13` = `exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before_P6L`：生产
  ancient limit。它只消费 `0 < ε`、`ε ≤ epsW` 与左侧 `hwit` 的 witness 精度（`SpatialCanonicalWitness … ε …`）；
  它的**输出里不再出现 ε**。这里的 ε 记作 `εin`（compactness / cone 小性）。
* `hB8` = `eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit`：从 limit 生产
  witness。它只消费 `0 < ε`、`ε < 1/11`，常数 `C` 只依赖这两个量，输出精度也是这个 ε。
  这里的 ε 记作 `ηout`（模型输出小性）。
本文件逐字重证 P6D 的证明骨架，只把两处用法分开命名：

  `∃ epsW > 0, ∀ ηout ∈ (0, 1/11), ∃ C(ηout) ≥ 1, ∀ εin ∈ (0, epsW], ∀ 序列 …，`
  `（hwit 精度 εin）⇒ 某子列上 eventually HasSpatialCanonicalTimeControl ηout C C C.toNNReal`。

量词序：**`C` 只依赖 `ηout`，不依赖 `εin`**（`εin` 在 `C` 之后取）。`εin` 与 `ηout` 之间不要求任何大小关系
（`εin < ηout`、`εin = ηout`、`εin > ηout` 都可）。原定理 = 取 `εin = ηout` 的特例（见文末 `example`）。

**义务（外审 D-13，本文件不生产）**：(O1) 冻结的 Good 常数须容纳 `C(ηout)`——见 G2
`P6GoodConstantsP6P`；(O2) 左侧序列仍须满足本定理的**完整输入**（traced regions / κ / seed / pinching /
`hwit`（精度 `εin`）/ `hderiv`）。"左侧全是 ε-Good" 不自动给出这些输入，精度解耦不生产它们。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood (IsAncientKappaSolution PointedFlowScalarAtBase
  ancientTimeInterval)
open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness CanonicalWitness I3
  eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit
  exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen
  isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative)

open private ObservedHistory.mem_Icc_of_mem_window
  ObservedHistory.riemannianBallOf_scaleMetric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

open private
  Perelman.CanonicalNeighborhood.FiniteHorn.scalar_derivative_bounds_of_local_canonicalWitness
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitCanonicalWitness

namespace ObservedHistory

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **P6 / L8 装配，精度解耦版（`_P6P`）**：`εin`-controlled compactness hypotheses
（traced regions、基点种子体积、trace-local κ / pinching / 精度 `εin` 的 witness / 时间导数）⇒
`ηout`-witness（某子列上 eventually 完整 `HasSpatialCanonicalTimeControl ηout C C C.toNNReal`）。
常数 `C = C(ηout)` 在 `εin`、序列之前取；`epsW` 是与两个精度都无关的绝对常数。 -/
theorem ancientWitness_decoupled_P6P :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ηout : ℝ, 0 < ηout → ηout < 1 / 11 →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ εin : ℝ, 0 < εin → εin ≤ epsW →
      ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n),
      (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop →
      (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
      ∀ {r₀ w : ℝ}, 0 < r₀ → 0 < w →
      (∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
            ((H n).stageMetric ((H n).activeStage (t n)) (t n))
            (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      ∀ {κ : ℝ}, 0 < κ → ∀ ρnc : ℕ → ℝ,
      Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'') →
      ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))))) →
      ∀ {C1s C2s Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ},
      (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) εin C1s C2s
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart εin) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v')
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ^ 2) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    (∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (_ : PointedRiemannianConvergenceMaps X P f)
        (G : ℝ → SmoothRiemannianMetric ThreeModel P.M)
        (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
          ancientTimeInterval)),
        IsAncientKappaSolution (κ / 250 / 30 ^ 3) (flowOfMetric ancientTimeInterval P G hG) ∧
        PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P G hG) 1) ∧
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      (H (ψ i)).HasSpatialCanonicalTimeControl ηout C C C.toNNReal (t (ψ i)) (y (ψ i)) := by
  obtain ⟨epsW, hepsW, hB13⟩ :=
    exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before_P6L.{u}
  refine ⟨epsW, hepsW, fun ηout hηout hsmall => ?_⟩
  obtain ⟨C, hC, hB8⟩ :=
    eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit.{u} hηout hsmall
  refine ⟨C, hC, fun εin hεin hεW => ?_⟩
  intro H t y R hR hscal hRlim htraced r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa Phi hPhi hpinch
    C1s C2s Cs Cq Ctime qs qcan hqs hqcan hwit hderiv X
  obtain ⟨W, h, hblock, -, -, -, f, hf, P, F, -, hPc, hconn, hballF, V, N, hV, hVF, φ, hφ, hφF, G,
    hG0, hG, ψ, hψ, hconv, hκG, CB, hCB⟩ :=
    hB13 H t y R hR hRlim htraced hr₀ hw hseed hκ ρnc hradii hkappa hPhi hpinch hεin hεW hqs hqcan
      hwit hderiv
  have hθ (k : ℕ) : 0 < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
  have hbaseX : ∀ n, metricScalarAt (X.obj n).metric (X.obj n).basepoint = 1 := by
    intro n
    change metricScalarAt (scaleMetric (R n) (hR n)
      ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) = 1
    rw [metricScalarAt_scaleMetric, hscal n, inv_mul_cancel₀ (hR n).ne']
  have hend : ∀ k : ℕ, ∀ᶠ n in atTop,
      (W k n : Set (X.obj n).M) =
        riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
      h k n 0 = (X.obj n).metric.restrictOpen (W k n) := by
    intro k
    filter_upwards [hblock k] with n hn
    refine ⟨hn.1, ?_⟩
    have hdom0 : (t n : ℝ) + 0 / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) := by
      simpa using (H n).activeStage_mem (t n)
    have hm := hn.2.2.1 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩ hdom0
    rw [zero_div, add_zero] at hm
    rw [hm]
    apply DifferentialGeometry.SmoothRiemannianMetric.ext_inner
    intro x v w
    rfl
  -- 局部化：pinching 只在 survivor maps 的 backward trace 点上用（照 P6B M8）
  have hpinchW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ q ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ x : W k n, curvatureOperatorLowerBoundAt (h k n q) x
        (metricAlgebraicCurvatureTensorAt (h k n q) x)
        (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n q) x)) := by
    intro k
    filter_upwards [hblock k, hpinch ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ))
      (by positivity) (hθ k)] with n hn hpn q hq x
    obtain ⟨hWset, -, -, ⟨a, hat, ha, fs, hfs, -, hcs, hls, hp⟩, -⟩ := hn
    have hqθ : q ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 :=
      ⟨by have := hq.1; push_cast at this ⊢; linarith, hq.2⟩
    have hv := ObservedHistory.mem_Icc_of_mem_window (hR n) ha hqθ
    let v : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + q / R n, a.2.1.trans hv.1, hv.2.trans (t n).2.2⟩
    have hav : a ≤ v := hv.1
    have hvt : v ≤ t n := hv.2
    let j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)) :=
      ⟨(H n).activeStage v, (H n).activeStage_mono hav, (H n).activeStage_mono hvt⟩
    have hq' := hp q hqθ j ((H n).activeStage_mem v)
    -- the actual backward trace of `x` carried by the survivor maps
    let tr0 : BackwardPointTrace (H n) ((H n).activeStage a) ((H n).activeStage (t n))
        ((H n).activeStage_mono hat) x.val :=
      { point := fun i hi hl => fs ⟨i, hi, hl⟩ x
        endpoint_eq := hls x
        crossing := fun i hi hl => hcs i hi hl x }
    let tr := tr0.restrictFirst ((H n).activeStage_mono hav) ((H n).activeStage_mono hvt)
    have hxW : (x : ((H n).stageAt (t n)).Carrier) ∈
        riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
      have hx := x.property
      change (x : (X.obj n).M) ∈ (W k n : Set (X.obj n).M) at hx
      rw [hWset] at hx
      change (x : ((H n).stageAt (t n)).Carrier) ∈
        riemannianBallOf (scaleMetric (R n) (hR n)
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) ((k + 3 : ℕ) : ℝ) at hx
      rwa [ObservedHistory.riemannianBallOf_scaleMetric_eq] at hx
    have hav' : (t n : ℝ) - 2 * ((k + 2 : ℕ) : ℝ) / R n ≤ v := by rw [← ha]; exact hav
    have hpt := hpn x hxW v hvt hav' tr
    have htrpt : tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt) =
        fs j x := rfl
    rw [htrpt] at hpt
    have hpull := (curvatureOperatorLowerBoundAt_localPullMetric_iff _ (fs j) (hfs j) x _).mpr
      hpt
    rw [hq', curvatureOperatorLowerBoundAt_scaleMetric_iff, metricScalarAt_scaleMetric,
      metricScalarAt_localPull]
    unfold Perelman.rescalePinchingFunction
    simp only [mul_inv_cancel_left₀ (hR n).ne']
    exact hpull
  obtain ⟨hcone, hcomplete⟩ := ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete
    hf hPc hconn hV hG0 hG hψ hconv hRlim hPhi hpinchW
  have hbaseP : metricScalarAt P.metric P.basepoint = 1 := by
    refine metricScalarAt_basepoint_eq_of_local_flow_limit hf F hV hφF hG0 hψ hconv ?_ ?_
    · intro k
      filter_upwards [hblock k] with n hn z
      have hdom0 : (t n : ℝ) + 0 / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) := by
        simpa using (H n).activeStage_mem (t n)
      rw [hn.2.2.1 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩ hdom0, zero_div, add_zero,
        metricScalarAt_scaleMetric, metricScalarAt_restrictOpen]
      exact (metricScalarAt_scaleMetric (R n) (hR n) _ _).symm
    · intro n
      change metricScalarAt (scaleMetric (R n) (hR n)
        ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) = 1
      rw [metricScalarAt_scaleMetric, hscal n, inv_mul_cancel₀ (hR n).ne']
  obtain ⟨o⟩ := haveI := hconn
    nonempty_tangentOrientationSection_of_pointedConvergence F
      (fun n => ((H n).stageAt (t n)).orientation) hV hVF
  obtain ⟨hanc, hbase⟩ := isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative
    P hG hG0 hconn hcomplete hcone hCB (div_pos hκ (by norm_num)) hκG hbaseP
  obtain ⟨k, hk, hK⟩ := hB8 X hbaseX W h
    (fun k => (hblock k).mono fun n hn => hn.2.1) hend
    f hf P F hPc hballF V N hV hVF φ hφ hφF G hG hG0 ψ hψ hconv _ hanc hbase o
  refine ⟨⟨f, hf, P, F, G, hG, hanc, hbase⟩, f ∘ ψ, hf.comp hψ, ?_⟩
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  filter_upwards [hK, hfψ.eventually (hblock k)] with i hKi hn
  obtain ⟨hy, K, hKc⟩ := hKi
  -- 空间部分：照 `CrossingAncientLimitSpatialC11X:226`
  have hdom0 : (t (f (ψ i)) : ℝ) + 0 / R (f (ψ i)) ∈
      (H (f (ψ i))).stageDomain ((H (f (ψ i))).activeStage (t (f (ψ i)))) := by
    simpa using (H (f (ψ i))).activeStage_mem (t (f (ψ i)))
  have hh0 := hn.2.2.1 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩ hdom0
  rw [zero_div, add_zero] at hh0
  have hball : riemannianClosedBallOf
      (scaleMetric (R (f (ψ i))) (hR (f (ψ i)))
        ((H (f (ψ i))).stageMetric ((H (f (ψ i))).activeStage (t (f (ψ i)))) (t (f (ψ i)))))
      (y (f (ψ i))) (2 * C + 1) ⊆
        (W k (f (ψ i)) : Set ((H (f (ψ i))).stageAt (t (f (ψ i)))).Carrier) := by
    rw [hn.1]
    intro z hz
    exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hk)
  obtain ⟨Wt, hWt, -⟩ := exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen
    ((H (f (ψ i))).stageMetric ((H (f (ψ i))).activeStage (t (f (ψ i)))) (t (f (ψ i))))
    (hR (f (ψ i))) (W k (f (ψ i))) ⟨y (f (ψ i)), hy⟩ (hscal (f (ψ i)))
    (neg_nonpos.mpr (Nat.cast_nonneg _)) (h k (f (ψ i))) hh0 K hKc hball
  unfold HasSpatialCanonicalTimeControl
  refine ⟨⟨Wt, hWt⟩, fun hlt _ => ?_⟩
  -- 时间部分（D-9.2）：`K.time_derivative` 经 private `:447` 拉回 `closedPrefixAt` 流的中心点
  set m : ℕ := f (ψ i) with hm
  let S := ((H m).closedPrefixAt (t m) hlt).flow
  have hdom : ∀ τ ∈ Icc ((H m).time ((H m).activeStage (t m))) (t m : ℝ),
      τ ∈ (H m).stageDomain ((H m).activeStage (t m)) := by
    intro τ hτ
    rcases hτ.1.eq_or_lt with he | hlo
    · rw [← he]
      exact (H m).time_mem_stageDomain _
    rcases hτ.2.eq_or_lt with he | hhi
    · rw [he]
      exact (H m).activeStage_mem (t m)
    exact (H m).mem_stageDomain_of_mem_Ioo ⟨hlo, hhi.trans_le
      ((H m).le_stageEndTime_of_mem_stageDomain ((H m).activeStage_mem (t m)))⟩
  have hfun : (fun v => S.scalar v (y m)) =
      fun v => metricScalarAt ((H m).stageMetric ((H m).activeStage (t m)) v) (y m) := by
    funext v
    change metricScalarAt (S.base.metric v) (y m) = _
    rw [(H m).closedPrefixAt_metric]
  have hSR : S.scalar (t m) (y m) = R m := by
    rw [congrFun hfun (t m)]
    exact hscal m
  have hid : ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, (t m : ℝ) + s / R m ∈
      (RealTimeInterval.closed _ _ ((H m).closedPrefixAt (t m) hlt).lt.le).carrier →
      h k m s = scaleMetric (R m) (hR m)
        ((S.base.metric ((t m : ℝ) + s / R m)).restrictOpen (W k m)) := by
    intro s hs hsD
    rw [(H m).closedPrefixAt_metric]
    exact hn.2.2.1 s hs (hdom _ hsD)
  have hηs : Icc ((t m : ℝ) - ((t m : ℝ) - (H m).time ((H m).activeStage (t m)))) (t m) ⊆
      (RealTimeInterval.closed _ _ ((H m).closedPrefixAt (t m) hlt).lt.le).carrier :=
    fun τ hτ => ⟨by linarith [hτ.1], hτ.2⟩
  have key :=
    (Perelman.CanonicalNeighborhood.FiniteHorn.scalar_derivative_bounds_of_local_canonicalWitness S
    ((H m).closedPrefixAt (t m) hlt).equation (hR m) (sub_pos.mpr hlt)
    (by positivity : (0 : ℝ) < ((k + 2 : ℕ) : ℝ)) hSR hηs (W k m) hy (h k m) hid
    (neg_nonpos.mpr (Nat.cast_nonneg _)) K).1
  rw [hfun, hSR] at key
  rw [Real.coe_toNNReal C (by linarith), hscal]
  exact key

/-- consumer（原定理 = `εin = ηout` 的特例）：解耦定理在 `εin := ε`、`ηout := ε` 处逐字给出
`P6AncientWitnessP6D` 的结论（含量词序 `epsW → ε → C → 序列`）。 -/
example : type_of% @exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D.{0} := by
  obtain ⟨epsW, hepsW, hB⟩ := ancientWitness_decoupled_P6P.{0}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall
  exact ⟨C, hC, hB' ε hε hεW⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
