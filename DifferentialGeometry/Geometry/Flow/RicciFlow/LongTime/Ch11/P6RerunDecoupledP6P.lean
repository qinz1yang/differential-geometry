import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GoodConstantsP6P

/-!
# P6 精度解耦：rerun 矛盾的 P6D 级整体 binder 形（S-CH11-PREC G3，后缀 `_P6P`）

消费 G1（`ancientWitness_decoupled_P6P`）与 G2（`false_of_not_good_of_eventually_good_decoupled_P6P`）。
D-13 / S-b 左移重跑的 P6D 级收口：**selection（或左移重跑）的坏点序列**
`¬ Good εsel C1' C2' Ctime'` 与 **左侧序列满足 G1 的完整输入（hwit 精度 `εin`）** 矛盾：

  `∃ epsW, ∀ ηout, ∃ C(ηout), ∀ {εsel C1' C2' Ctime'}, ηout ≤ εsel < 1/11 → C ≤ C1' → C ≤ C2' →`
  `C.toNNReal ≤ Ctime' → ∀ εin ≤ epsW, ∀ 序列 …（P6D 全部局部前提，hwit 精度 εin）→`
  `(∀ n, ¬ Good εsel C1' C2' Ctime' (t n) (y n)) → False`。

`εin` 与 `ηout`、`εsel` 之间**没有**大小关系要求：`εin < ηout`（左侧给更细的 witness，S-b / S-c 的
情形）、`εin = ηout = εsel`（原 P6D 耦合形）都是本定理的实例（见文末 `example`）。若左侧 hwit 想由冻结
Good 区取得，则用 G2 的 `exists_witness_monoEps_P6P` 把精度 `εsel` 的 witness 搬到
`εin ≥ εsel`（`εin < 1/11`），此路线需 `εsel ≤ epsW`。

**重要（D-13 义务 (O2)，本车道不生产）**：左侧序列仍须满足完整输入——traced regions
（`htraced`）、基点种子体积（`hseed`）、trace-local κ（`hkappa`，`ρnc`、`hradii`）、pinching
（`hpinch`）、精度 `εin` 的 witness（`hwit`）与时间导数（`hderiv`）、基点标量 `hscal`、`R → ∞`。
"左侧全是 ε-Good" 不自动给出这些输入（全深度 traced regions 与共同 surviving footprint）；它们在本
定理里是**显式前提**，由调用者（S-b 的 `leftShift_rerun_P6S2`、S-c 的 stability contract）供给。
S-b 的阈值系数 `8` 对应 `qs n ≤ Cs * R n` 里取 `Cs = 8`（`Cs`、`Cq` 是左侧序列的自由 binder，
与 `C(ηout)` 无关）。P6BND2 的 `leftShift_rerun_P6S2` 在本块写成时尚未落地，故本文件只给 binder 形。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

universe u

/-- **rerun 矛盾（解耦版，P6D 级整体）**：G1 的完整输入（hwit 精度 `εin`）+ 坏点序列
`¬ Good εsel C1' C2' Ctime'`，且 `ηout ≤ εsel < 1/11`、`C ≤ C1'`、`C ≤ C2'`、`C.toNNReal ≤ Ctime'`
（D-13 (O1) 的显式 binder，`C = C(ηout)`）⇒ `False`。 -/
theorem false_of_rerun_decoupled_P6P :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ηout : ℝ, 0 < ηout → ηout < 1 / 11 →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {εsel C1' C2' : ℝ} {Ctime' : ℝ≥0}, ηout ≤ εsel → εsel < 1 / 11 →
      C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' → ∀ εin : ℝ, 0 < εin → εin ≤ epsW →
      ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (_hR : ∀ n, 0 < R n),
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
      (∀ n, ¬ (H n).HasSpatialCanonicalTimeControl εsel C1' C2' Ctime' (t n) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ := ancientWitness_decoupled_P6P.{u}
  refine ⟨epsW, hepsW, fun ηout hηout hsmall => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ηout hηout hsmall
  refine ⟨C, hC, fun {εsel C1' C2' Ctime'} hηs hss hC1 hC2 hCt εin hεin hεW => ?_⟩
  intro H t y R hR hscal hRlim htraced r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa Phi hPhi hpinch
    C1s C2s Cs Cq Ctime qs qcan hqs hqcan hwit hderiv hsel
  obtain ⟨-, ψ, hψ, hev⟩ := hB' εin hεin hεW H t y R hR hscal hRlim htraced hr₀ hw hseed hκ ρnc
    hradii hkappa hPhi hpinch hqs hqcan hwit hderiv
  exact false_of_not_good_of_eventually_good_decoupled_P6P hηs hss hC1 hC2 hCt H t y hsel
    ⟨ψ, hψ, hev⟩

/-- consumer（`εin < ηout` 版）：`ηout = εsel = 1/20`、冻结常数全取 `C(ηout)`、左侧 hwit 精度
`εin := min epsW (1/40) < ηout`——定理在这个更细的输入精度处可用。 -/
example : ∃ epsW : ℝ, 0 < epsW ∧ 0 < min epsW (1 / 40) ∧ min epsW (1 / 40) < 1 / 20 := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_rerun_decoupled_P6P.{0}
  obtain ⟨C, -, hB'⟩ := hB (1 / 20) (by norm_num) (by norm_num)
  have _ := @hB' (1 / 20) C C C.toNNReal le_rfl (by norm_num) le_rfl le_rfl le_rfl
    (min epsW (1 / 40)) (lt_min hepsW (by norm_num)) (min_le_left _ _)
  exact ⟨epsW, hepsW, lt_min hepsW (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩

/-- consumer（耦合特例）：`εin = ηout = εsel = ε` 即 P6D 的耦合形（`ε < 1/11`、`ε ≤ epsW`）。 -/
example : ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW → ∃ C : ℝ, 1 ≤ C := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_rerun_decoupled_P6P.{0}
  refine ⟨epsW, hepsW, fun ε hε hs hεW => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hs
  have _ := @hB' ε C C C.toNNReal le_rfl hs le_rfl le_rfl le_rfl ε hε hεW
  exact ⟨C, hC⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
