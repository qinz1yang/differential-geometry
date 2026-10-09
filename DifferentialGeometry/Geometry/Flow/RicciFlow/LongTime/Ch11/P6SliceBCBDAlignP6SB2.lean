import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaDriverCondP6KA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDP6SB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalCrossEventP6E

/-!
# R4 中心对齐：driver `(Hs, ts, ys)` ↔ kernel 选出族 `(K, j, t, yG)`（O-CH11-SLICE-BCBD2 G3，后缀 `_P6SB2`）

KAPPA-ADAPT G3 driver `exists_subseq_forall_depthExtendable_kappaC_P6KA` 的 `hanchor0` 槽（相对 driver 尺度
`R`）与 SLICE-BCBD 主定理（G7 / G8，kernel 帧 `(K, j, t, yG)`、相对中心标量 `R(t, yG)`）之间的对齐：
* `slab_pos_of_activeStage_P6SB2`（PROVED）：`activeStage ts < last` 且 `time (activeStage ts) < ts`
  ⇒ `ts` 落在某 event slab 的开内部（`eventInterior_data_P6X` 的 `hpos`）；
* `hanchor0_rescale_P6SB2`（PROVED）：`hanchor0` 相对 `R'` + eventually `R' ≤ C·R` ⇒ 相对 `R`
  （`Q' := max 2 (Q·C)`，半径 `A ↦ A·√C`）；
* `centerScalar_le_of_isTracedRegion_P6SB2`（PROVED）：`isTracedRegion t p ρ τ K` ⇒ `R(t, p) ≤ 9K`
  （`isTracedRegion.normSq_le` + `scalar_le_of_normSq_le_P6E`）；
* **①** `exists_kernelFrame_hanchor0_P6SB2`（PROVED，无额外前提）：`Hs := (K n).toHistory`、`ts` 在开 slab
  内、driver `R := R(ts, ys)` ⇒ `∃ j yG`（kernel 帧）使 kernel 切片 BCBD ⇒ driver `hanchor0` 逐字；
* **②** `hanchor0_driver_of_kernel_traced_P6SB2`（**PROVISIONAL[中心 isTracedRegion（R4 塔侧供给）]**）：
  driver `R := R_k` 任意，中心可比性 `R(ys) ≤ 9K₀·R_k` 由 `(ts, ys)` 处的 `isTracedRegion (… K₀·R_k)` 付；
  **该 isTracedRegion 不是 driver 字段，是 consumer 输入**（driver 内 isTracedRegion 只作 hkappaC 等的
  前件 / hsurvive 结论 / DepthExtendable 结论出现；`hanchor0` 在 `z = ys` 处等价于 `R(ys) ≤ Q·R`，故
  可比性是 `hanchor0` 的必要条件，kernel BCBD 给不出）。
* consumer `exists_subseq_forall_depthExtendable_ofKernel_P6SB2`：driver 结论 ⇐ driver 其余 binder（逐字，
  `Hs := (K n).toHistory`）+ ① 的 kernel 切片 BCBD；`hanchor0` 不再是前提。
生成器 `build-logs/scratch/O-CH11-SLICE-BCBD2/gen/gen3.py`（driver binder 逐字切出 + 替换 assert）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn

universe u

namespace ObservedHistory

/-- `activeStage ts` 不是最后一个 stage 且 `ts` 严格晚于其起点 ⇒ `ts` 在某 event slab 开内部（`_P6SB2`）。 -/
theorem slab_pos_of_activeStage_P6SB2 (H : ObservedHistory.{u}) (τ : Icc (0 : ℝ) H.horizon)
    (hlast : H.activeStage τ < Fin.last H.eventCount)
    (hin : H.time (H.activeStage τ) < τ) :
    ∃ j : Fin H.eventCount, H.time j.castSucc < (τ : ℝ) ∧ (τ : ℝ) < H.time j.succ := by
  obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt hlast)
  have hlt : (H.activeStage τ).val < H.eventCount := by
    rw [← hj]
    exact j.isLt
  have h1 := H.activeStage_before_next τ hlt
  have hfin : (⟨(H.activeStage τ).val + 1, by omega⟩ : Fin (H.eventCount + 1)) = j.succ := by
    apply Fin.ext
    change (H.activeStage τ).val + 1 = j.succ.val
    rw [Fin.val_succ, ← hj, Fin.val_castSucc]
  refine ⟨j, ?_, h1.trans_eq (congrArg H.time hfin)⟩
  rw [hj]
  exact hin

/-- **换尺度（`_P6SB2`，PROVED）**：`hanchor0` 相对 `R'`，且 eventually `R' ≤ C·R` ⇒ `hanchor0` 相对
`R`（球 `B(ys, A/√R) ⊆ B(ys, A√C/√R')`，`R(z) ≤ Q·R' ≤ Q·C·R`）。 -/
theorem hanchor0_rescale_P6SB2 {H : ℕ → ObservedHistory.{u}}
    {ts : ∀ n, Icc (0 : ℝ) (H n).horizon} {ys : ∀ n, ((H n).stageAt (ts n)).Carrier}
    {R R' : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hR' : ∀ n, 0 < R' n) {C : ℝ} (hC : 0 < C)
    (hle : ∀ᶠ n in atTop, R' n ≤ C * R n)
    (h' : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R' n)),
        metricScalarAt ((H n).stageMetric ((H n).activeStage (ts n)) (ts n)) z ≤ Q * R' n) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((H n).stageMetric ((H n).activeStage (ts n)) (ts n)) z ≤ Q * R n := by
  intro A hA
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  obtain ⟨Q, hQ, hev⟩ := h' (A * Real.sqrt C) (mul_pos hA hsC)
  refine ⟨max 2 (Q * C), le_max_left _ _, ?_⟩
  filter_upwards [hev, hle] with n hn hlen
  intro z hz
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hsR' : 0 < Real.sqrt (R' n) := Real.sqrt_pos.mpr (hR' n)
  have hsq : Real.sqrt (R' n) ≤ Real.sqrt C * Real.sqrt (R n) := by
    rw [← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt hlen
  have hrad : A / Real.sqrt (R n) ≤ A * Real.sqrt C / Real.sqrt (R' n) := by
    rw [div_le_div_iff₀ hsR hsR']
    calc A * Real.sqrt (R' n) ≤ A * (Real.sqrt C * Real.sqrt (R n)) :=
          mul_le_mul_of_nonneg_left hsq hA.le
      _ = A * Real.sqrt C * Real.sqrt (R n) := by ring
  have h1 := hn z (riemannianBallOf_mono _ _ hrad hz)
  have hQ0 : 0 ≤ Q := by linarith
  calc _ ≤ Q * R' n := h1
    _ ≤ Q * (C * R n) := mul_le_mul_of_nonneg_left hlen hQ0
    _ = Q * C * R n := by ring
    _ ≤ max 2 (Q * C) * R n := mul_le_mul_of_nonneg_right (le_max_right _ _) (hR n).le

/-- **中心标量 ⇐ traced region（`_P6SB2`，PROVED）**：`isTracedRegion t p ρ τ K`（`K ≥ 0`）⇒
`R(t, p) ≤ 9K`（中心在球内；`|Rm|² ≤ K²` ⇒ `R ≤ 9K`）。 -/
theorem centerScalar_le_of_isTracedRegion_P6SB2 {H : ObservedHistory.{u}}
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {ρ τ K : ℝ}
    (h : H.isTracedRegion t p ρ τ K) (hK : 0 ≤ K) :
    metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ 9 * K := by
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ := by
    change riemannianEDistOf _ p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr h.radius_pos
  have h1 := scalar_le_of_normSq_le_P6E _ p (h.normSq_le p hp)
  rwa [abs_of_nonneg hK] at h1

/-- **① 中心对齐，driver `R := R(ts, ys)`（`_P6SB2`，PROVED，无额外前提）**：`Hs := (K n).toHistory`、
`ts n` 在某 event slab 开内部（`hpos`）、driver 尺度 = 中心标量 ⇒ 存在 kernel 帧 `(j, yG)`（`t := ts`），
满足 kernel 主定理的帧前提 `hjt / htj / hyG / hRn`，且 kernel 切片 BCBD（G7 / G8 结论逐字）⇒ driver
`hanchor0` 槽逐字。 -/
theorem exists_kernelFrame_hanchor0_P6SB2 (Hs : ℕ → ObservedHistory.{u})
    {K : ℕ → RetainedCoreHistory.{u}} (hHs : Hs = fun n => (K n).toHistory)
    (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier)
    (hpos : ∀ n, ∃ j : Fin (Hs n).eventCount,
      (Hs n).time j.castSucc < (ts n : ℝ) ∧ (ts n : ℝ) < (Hs n).time j.succ)
    (R : ℕ → ℝ)
    (hRdef : ∀ n, R n = metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
      (ys n)) :
    ∃ (j : ∀ n, Fin (K n).eventCount) (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier),
      (∀ n, (K n).time (j n).castSucc < (ts n : ℝ)) ∧
      (∀ n, (ts n : ℝ) < (K n).time (j n).succ) ∧ (∀ n, HEq (ys n) (yG n)) ∧
      (∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n)) ∧
      ((∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (ts n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n)) →
      ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n) := by
  subst hHs
  obtain ⟨j, yG, hjt, htj, hyG, hsc⟩ := RetainedCoreHistory.eventInterior_data_P6X ts ys hpos
  have hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n) :=
    fun n => (hRdef n).trans (hsc n)
  exact ⟨j, yG, hjt, htj, hyG, hRn, fun hK =>
    hanchor0_obs_of_kernel_P6SB (t := fun n => (ts n : ℝ)) hjt htj ts (fun _ => rfl) ys yG hyG R
      hRn hK⟩

/-- **② 中心对齐，driver `R := R_k` 任意（`_P6SB2`，PROVISIONAL[中心 isTracedRegion（R4 塔侧供给）]）**：
kernel 帧 `(K, j, ts, yG)`（中心标量 `Rc`）上的切片 BCBD + `(ts, ys)` 处 eventually 的
`isTracedRegion (ρ n) (τ n) (K₀·R n)` ⇒ driver `hanchor0`（相对 `R`）逐字。中心可比性
`Rc ≤ 9K₀·R ≤ (9K₀ + 1)·R` 由该 isTracedRegion 付（`centerScalar_le_of_isTracedRegion_P6SB2`），再
`hanchor0_rescale_P6SB2`。**`htr` 不是 driver 字段，是 consumer 输入**（来源 = R4 塔侧 / BCDBOOT hTR
合同形，未做）。 -/
theorem hanchor0_driver_of_kernel_traced_P6SB2 (Hs : ℕ → ObservedHistory.{u})
    {K : ℕ → RetainedCoreHistory.{u}} (hHs : Hs = fun n => (K n).toHistory)
    (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier)
    {j : ∀ n, Fin (K n).eventCount} {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hjt : ∀ n, (K n).time (j n).castSucc < (ts n : ℝ))
    (htj : ∀ n, (ts n : ℝ) < (K n).time (j n).succ) (hyG : ∀ n, HEq (ys n) (yG n))
    (Rc : ℕ → ℝ) (hRc : ∀ n, 0 < Rc n)
    (hRcn : ∀ n, Rc n = ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (ρ τ : ℕ → ℝ)
    (htr : ∀ᶠ n in atTop,
      (Hs n).isTracedRegion (ts n) (ys n) (ρ n) (τ n) (K₀ * R n))
    (hK : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (ts n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n := by
  subst hHs
  have h' := hanchor0_obs_of_kernel_P6SB (t := fun n => (ts n : ℝ)) hjt htj ts (fun _ => rfl) ys yG
    hyG Rc hRcn hK
  have hC : (0 : ℝ) < 9 * K₀ + 1 := by linarith
  refine hanchor0_rescale_P6SB2 (H := fun n => (K n).toHistory) hR hRc hC ?_ h'
  filter_upwards [htr] with n hn
  have hKR : 0 ≤ K₀ * R n := mul_nonneg hK₀ (hR n).le
  have hc := centerScalar_le_of_isTracedRegion_P6SB2 hn hKR
  have hact : (K n).toHistory.activeStage (ts n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6SB (j n) (ts n) (hjt n).le (htj n)
  rw [(K n).scalar_of_incoming_P6X (j n) hact.symm (ts n) (yG n) (ys n) (hyG n), ← hRcn n] at hc
  nlinarith [hR n]

/-- **consumer（`_P6SB2`，PROVED ⇐ driver 其余 binder + kernel 切片 BCBD）**：KAPPA-ADAPT driver
`exists_subseq_forall_depthExtendable_kappaC_P6KA`（driver binder 逐字，删去 `hanchor0`，加
`hHs : Hs = fun n => (K n).toHistory`）的结论；`hanchor0` 由 ① 付：`ts` 在 event slab 开内部（`hpos`）、
`R = R(ts, ys)`（`hRdef`），kernel 切片 BCBD 对 ① 给出的帧 `(j, yG)` 成立（`hK`，= G7 / G8 结论逐字的供给接口）。 -/
theorem exists_subseq_forall_depthExtendable_ofKernel_P6SB2
    (Hs : ℕ → ObservedHistory.{u}) {K : ℕ → RetainedCoreHistory.{u}}
    (hHs : Hs = fun n => (K n).toHistory) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n) →
        (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
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
    (hkappaC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
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
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
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
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
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
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
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
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n)
    (hpos : ∀ n, ∃ j : Fin (Hs n).eventCount,
      (Hs n).time j.castSucc < (ts n : ℝ) ∧ (ts n : ℝ) < (Hs n).time j.succ)
    (hRdef : ∀ n, R n = metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
      (ys n))
    (hK : ∀ (j : ∀ n, Fin (K n).eventCount) (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier),
      (∀ n, (K n).time (j n).castSucc < (ts n : ℝ)) →
      (∀ n, (ts n : ℝ) < (K n).time (j n).succ) → (∀ n, HEq (ys n) (yG n)) →
      (∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n)) →
      ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (ts n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n)):
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T  := by
  obtain ⟨j, yG, hjt, htj, hyG, hRn, himp⟩ :=
    exists_kernelFrame_hanchor0_P6SB2 Hs hHs ts ys hpos R hRdef
  exact exists_subseq_forall_depthExtendable_kappaC_P6KA Hs ts ys R hR
    hRlim hsurvive (himp (hK j yG hjt htj hyG hRn)) hextend hr₀ hw hseed hκ ρnc hradii hkappaC hPhi
    hpinch hε hεX hεN hqs hwitC hqcan hderivC hbcadC

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
