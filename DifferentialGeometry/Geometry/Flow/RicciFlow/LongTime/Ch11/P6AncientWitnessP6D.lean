import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionAncientLimitScalarBound_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimitSpatialC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection

/-!
# P6 / L8 装配：局部古代 κ-solution 极限 + EXT2 witness + 完整 time control（O-CH11-P6D G2）

后缀 `_P6D`。模板 = 树内全局装配 `CrossingAncientLimitSpatialC11X:53`
（`exists_eventually_canonicalWitness_survivor_of_isTracedRegion_at_closed_time`）：
`:42` ⇒ Rm ≥ 0 + 完备 ⇒ 基点 `R = 1` ⇒ orientation ⇒
`isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative` ⇒ EXT2 的
`eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit`（astra `:43`，M7）。

* 底座换成 G1 的 `exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before_P6L`：
  前提（κ / pinching / witness / 时间导数）全部 **trace-local**，与 P6B M8 逐字同形；
  `hpinchW` 照 P6B M8（trace 点）。
* **D-9.2（外审 R-C11-1）**：恢复定理输出**完整** `HasSpatialCanonicalTimeControl`
  （`ST/CanonicalTimeControlPointSelection:44`）：空间部分照 `:226` 用
  `exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen`；时间部分 = EXT2 的
  `CanonicalWitness.time_derivative` 经树内 private
  `scalar_derivative_bounds_of_local_canonicalWitness`
  （`ST/AncientLimitCanonicalWitness:447`）拉回 ambient 中心点，ambient 流 = `closedPrefixAt`
  （`time(activeStage t) < t` 正是 time clause 的条件；`hid` 照 `CrossingAncientLimit:34`）。
  常数 `Ctime' := C.toNNReal` 与 witness 常数 `C` 同时在序列之前取（"预选 Ctime′"）。
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

/-- **P6 / L8 装配（`_P6D`）**：局部前提（traced regions、基点种子体积、trace-local κ / pinching /
witness / 时间导数）⇒ (i) 子列的局部古代极限是 `κ/250/30³`-ancient κ-solution（基点 `R = 1`）；
(ii) 另一子列上坏点 `(t, y)` **eventually 满足完整 `HasSpatialCanonicalTimeControl`**
（空间 witness + 单侧时间导数界，常数 `C` 先取）。 -/
theorem exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ∃ C : ℝ, 1 ≤ C ∧
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
          ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) ε C1s C2s
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
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
      (H (ψ i)).HasSpatialCanonicalTimeControl ε C C C.toNNReal (t (ψ i)) (y (ψ i)) := by
  obtain ⟨epsW, hepsW, hB13⟩ :=
    exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before_P6L.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW => ?_⟩
  obtain ⟨C, hC, hB8⟩ :=
    eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit.{u} hε hsmall
  refine ⟨C, hC, ?_⟩
  intro H t y R hR hscal hRlim htraced r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa Phi hPhi hpinch
    C1s C2s Cs Cq Ctime qs qcan hqs hqcan hwit hderiv X
  obtain ⟨W, h, hblock, -, -, -, f, hf, P, F, -, hPc, hconn, hballF, V, N, hV, hVF, φ, hφ, hφF, G,
    hG0, hG, ψ, hψ, hconv, hκG, CB, hCB⟩ :=
    hB13 H t y R hR hRlim htraced hr₀ hw hseed hκ ρnc hradii hkappa hPhi hpinch hε hεW hqs hqcan
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

/-- consumer：同一组局部前提下，坏点序列不可能处处违反 time-controlled canonical 条件
（P6 反证的收口形：point selection 返回 `¬ HasSpatialCanonicalTimeControl`）。 -/
example : ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ∃ C : ℝ, 1 ≤ C := by
  obtain ⟨epsW, hepsW, hB⟩ :=
    exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D.{0}
  exact ⟨epsW, hepsW, fun ε hε hs hεW => (hB ε hε hs hεW).imp fun _ hC => hC.1⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
