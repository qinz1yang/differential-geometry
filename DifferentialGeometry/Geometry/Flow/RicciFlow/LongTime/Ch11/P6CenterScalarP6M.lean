import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

/-!
# 窗口中心曲率 ⇐ traced region（O-CH11-P6ANCH G2c，后缀 `_P6M`）

G2w（窗口 BCAD）前提 `hW` 的 (i) 分量 = 窗口中心本身 `R ≤ A·R_n`。本文件：若 `(s, y)` 处有深度 `δ`、
半径 `ρ`、曲率界 `C` 的 traced region（树内 `isTracedRegion`：`B_s(y, ρ)` 中每点有到时刻 `s − δ` 的
backward trace，沿途 `|Rm| ≤ C`），则
* 分量 2：`B_s(y, ρ)` 中点 `x` 的**任一** backward trace（起点 `v ≥ s − δ`）在 event slab `e` 内时刻
  `t' > v` 的 trace 点处 `R ≤ 9·|C|`（trace 唯一性：`BackwardPointTrace` 是 `Subsingleton`，限制后与
  traced region 的 trace 相同）；
* 分量 1：`x` 自身在末 stage 窗口时刻 `τ ≥ s − δ` 处 `R ≤ 9·|C|`；
`9 = dim²`（树内 `scalar_abs_le_rm`）。序列层取 `C = K·R_n`（P6D2 G3 htraced 的形）⇒ `A = 9K`。
**注意（循环）**：htraced 是 P6D2 G3 的输出；若用它喂 P6GEO `hscal` ⇒ `hdist` ⇒ `hwit`（G3 的输入），
需在深度归纳内部交替使用（见 state HANDOVER 设计发现 2）。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- `|Rm|² ≤ C²` ⇒ `R ≤ 9|C|`（三维，`scalar_abs_le_rm`）。 -/
private theorem scalar_le_of_normSq_le_P6M {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M) {C : ℝ}
    (h : normSq0S g x 4 (metricRm04At g x) ≤ C ^ 2) : metricScalarAt g x ≤ 9 * |C| := by
  have hfin : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  have h1 := scalar_abs_le_rm g x
  rw [hfin] at h1
  have h2 : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ |C| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  have h3 := le_abs_self (metricScalarAt g x)
  push_cast at h1
  nlinarith [Real.sqrt_nonneg (normSq0S g x 4 (metricRm04At g x))]

/-- stage 指标推广：`m = m'`、点 `HEq` 时搬运 `|Rm|²` 界。 -/
private theorem normSq_congr_P6M (H : ObservedHistory.{u}) {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (v C : ℝ) (p : (H.stage m).Carrier) (p' : (H.stage m').Carrier)
    (hp : HEq p p')
    (h : normSq0S (H.stageMetric m v) p 4 (metricRm04At (H.stageMetric m v) p) ≤ C ^ 2) :
    normSq0S (H.stageMetric m' v) p' 4 (metricRm04At (H.stageMetric m' v) p') ≤ C ^ 2 := by
  subst hm
  obtain rfl := eq_of_heq hp
  exact h

/-- **`_P6M`（分量 2）**：traced region ⇒ 窗口内任一 backward trace 在 event slab 时刻 `t'` 的点处
`R ≤ 9|C|`。 -/
theorem scalar_le_of_isTracedRegion_trace_P6M (H : ObservedHistory.{u})
    (s : Icc (0 : ℝ) H.horizon) (y : (H.stageAt s).Carrier) {ρ δ C : ℝ}
    (hreg : H.isTracedRegion s y ρ δ C)
    (x : (H.stageAt s).Carrier) (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y ρ)
    (v : Icc (0 : ℝ) H.horizon) (hvs : v ≤ s) (hδv : (s : ℝ) - δ ≤ v)
    (tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x)
    (e : Fin H.eventCount) (h3 : H.activeStage v ≤ e.castSucc) (h4 : e.succ ≤ H.activeStage s)
    (t' : ℝ) (hvt : (v : ℝ) < t') (h6 : H.time e.castSucc < t') (h7 : t' < H.time e.succ) :
    metricScalarAt (H.stageMetric e.castSucc t')
      (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤ 9 * |C| := by
  obtain ⟨_, _, a, hat, ha, htr⟩ := hreg
  obtain ⟨A, hA⟩ := htr x hx
  have hs' : t' ≤ (s : ℝ) := by
    have hle := H.time_strictMono.monotone h4
    exact (h7.le.trans hle).trans (H.activeStage_time_le s)
  let τ' : Icc (0 : ℝ) H.horizon := ⟨t', v.2.1.trans hvt.le, hs'.trans s.2.2⟩
  have hav : a ≤ v := show (a : ℝ) ≤ v by rw [ha]; exact hδv
  have haτ : a ≤ τ' := show (a : ℝ) ≤ t' by linarith [show (a : ℝ) ≤ v from hav]
  have hτs : τ' ≤ s := hs'
  have hact : H.activeStage τ' = e.castSucc :=
    (H.mem_stageDomain_iff τ' e.castSucc).mp (by
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
        (show t' ∈ Ico (H.time e.castSucc) (H.time e.succ) from ⟨h6.le, h7⟩))
  have hb := hA.1 τ' haτ hτs
  have hrest : A.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvs) = tr :=
    Subsingleton.elim _ _
  have hpt : HEq (A.point (H.activeStage τ') (H.activeStage_mono haτ) (H.activeStage_mono hτs))
      (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) := by
    have key : ∀ (m : Fin (H.eventCount + 1)) (hm : H.activeStage τ' = m) (h1 : H.activeStage v ≤ m)
        (h2 : m ≤ H.activeStage s),
        HEq (A.point (H.activeStage τ') (H.activeStage_mono haτ) (H.activeStage_mono hτs))
          (tr.point m h1 h2) := by
      intro m hm h1 h2
      subst hm
      rw [← hrest]
      rfl
    exact key e.castSucc hact h3 _
  exact scalar_le_of_normSq_le_P6M _ _
    (normSq_congr_P6M H hact t' C _ _ hpt hb)

/-- **`_P6M`（分量 1）**：traced region ⇒ `B_s(y, ρ)` 中点 `x` 在末 stage 窗口时刻 `τ ≥ s − δ`
（`time (activeStage s) < τ < s`）处 `R ≤ 9|C|`。 -/
theorem scalar_le_of_isTracedRegion_window_P6M (H : ObservedHistory.{u})
    (s : Icc (0 : ℝ) H.horizon) (y : (H.stageAt s).Carrier) {ρ δ C : ℝ}
    (hreg : H.isTracedRegion s y ρ δ C)
    (x : (H.stageAt s).Carrier) (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y ρ)
    (τ : ℝ) (hδτ : (s : ℝ) - δ ≤ τ) (h1 : H.time (H.activeStage s) < τ) (h2 : τ < s) :
    metricScalarAt (H.stageMetric (H.activeStage s) τ) x ≤ 9 * |C| := by
  obtain ⟨_, _, a, hat, ha, htr⟩ := hreg
  obtain ⟨A, hA⟩ := htr x hx
  let τ' : Icc (0 : ℝ) H.horizon := ⟨τ, (H.time_nonneg _).trans h1.le, h2.le.trans s.2.2⟩
  have haτ : a ≤ τ' := show (a : ℝ) ≤ τ by rw [ha]; exact hδτ
  have hτs : τ' ≤ s := h2.le
  have hact : H.activeStage τ' = H.activeStage s :=
    le_antisymm (H.activeStage_mono hτs) (H.le_activeStage τ' _ h1.le)
  have hb := hA.1 τ' haτ hτs
  have hpt : HEq (A.point (H.activeStage τ') (H.activeStage_mono haτ) (H.activeStage_mono hτs))
      x := by
    have key : ∀ (m : Fin (H.eventCount + 1)) (hm : H.activeStage τ' = m)
        (h2' : m ≤ H.activeStage s), m = H.activeStage s →
        HEq (A.point (H.activeStage τ') (H.activeStage_mono haτ) (H.activeStage_mono hτs))
          (A.point m (hm ▸ H.activeStage_mono haτ) h2') := by
      intro m hm h2' _
      subst hm
      rfl
    refine (key _ hact le_rfl rfl).trans ?_
    exact heq_of_eq A.endpoint_eq
  exact scalar_le_of_normSq_le_P6M _ _
    (normSq_congr_P6M H hact τ C _ _ hpt hb)

/-- consumer（序列层，G2w `hW` (i) 分量 2 的形）：traced region 曲率界 `K·R_n`（P6D2 G3 htraced 形）
⇒ 窗口 trace 点 `R ≤ 9K·R_n`。 -/
example (Hs : ℕ → ObservedHistory.{u}) (s aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hreg : ∀ D T : ℝ, 0 < D → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in Filter.atTop,
      (Hs n).isTracedRegion (s n) (y n) (D / Real.sqrt (R n)) (T / R n) (K * R n)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ A : ℝ, ∀ᶠ n in Filter.atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        metricScalarAt ((Hs n).stageMetric e.castSucc t')
          (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤ A * R n := by
  intro D T hD hT
  obtain ⟨K, hK, hev⟩ := hreg D T hD hT
  refine ⟨9 * K, ?_⟩
  filter_upwards [hev] with n hn
  intro x hx v _ hvs hTv tr e h3 h4 t' h5 h6 h7
  have h := scalar_le_of_isTracedRegion_trace_P6M _ _ _ hn x hx v hvs hTv tr e h3 h4 t' h5 h6 h7
  rw [abs_of_nonneg (mul_nonneg hK (hR n).le)] at h
  linarith

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
