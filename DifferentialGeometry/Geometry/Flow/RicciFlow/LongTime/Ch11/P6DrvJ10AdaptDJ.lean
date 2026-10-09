import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRoutePrefixNoJ10P6JG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixTracedC11G3

/-!
# DRV-J10F G1：driver `hsurvive` / `hextend` 槽的 E 帧 → K 帧适配（`_DJ`）

guarded2 driver（`exists_subseq_forall_depthExtendable_of_hPN_anyPos_guarded2_P6HK`）在 DRVWIRE 帧
`Hs := (K n).toHistory`、`ts := σ`（事件内部 `time (j n).castSucc < σ n < time (j n).succ`）吃
`hsurvive` / `hextend`；J10CORE / CXJP / J10GEN producer 的结论在
`E n := (K n).eventPrefix (j n) (σ n)`（= `(K n).prefixAt (j n).castSucc` 的 `extendAt`，定义等）。
本文件（全部 PROVED，无新前提）：
* 逐 n：K → E 的球上标量界 `ballScalar_eventPrefix_DJ`、K → E 的 backward-trace 标量界
  `traceScalar_eventPrefix_DJ`（E trace 经 `forall_trace_eventPrefix_P6M` 上推）、K → E traced region
  `isTracedRegion_eventPrefix'_DJ`（`isTracedRegion_eventPrefix_C11G3` 的 E 抽象形）；
* 序列：`depthExtendable_eventPrefix_DJ`（K → E，`depthExtendable_of_eventPrefix_P6M` 的反向）；
* 槽：`hsurvive_K_of_eventPrefix_DJ` / `hextend_K_of_eventPrefix_DJ`——E 帧槽（driver 形逐字，`Hs ts ys`）
  ⇒ K 帧槽（`(K n).toHistory`、`σ`、`y`，DrvResE_DW 文本逐字），同一 `Cst`、同一 `R`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- **K → E 球上标量界（`_DJ`）**：K 在实时刻 `τ'`、中心 `p'` 的球上 `scalar ≤ B` ⇒ E 在同一实时刻
`τ`、`HEq` 中心的同半径球上 `scalar ≤ B`。 -/
theorem ballScalar_eventPrefix_DJ (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    (ρ B : ℝ)
    (h : ∀ z ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' ρ,
      metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') z ≤ B) :
    ∀ z ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p ρ,
      metricScalarAt (E.stageMetric (E.activeStage τ) τ) z ≤ B := by
  subst hE
  intro z hz
  have hAτ := K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ
  have hl : K.toHistory.activeStage τ' = K.eIdx_C11G2 j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) := Fin.ext hAτ.symm
  let z' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hl.symm) z
  have hzz : HEq z z' := (cast_heq _ _).symm
  have hz' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ p z p' z' hp hzz ρ hz
  rw [ObservedHistory.scalar_eq_of_eventPrefix_P6JGH K j hjT hTj τ τ' hττ z z' hzz]
  exact h z' hz'

/-- **K → E trace 标量界（`_DJ`）**：K 层"球内每点、每条 `[w', τ']` backward trace 在 `w'` 处
`scalar ≤ B`（`w' = τ' − δ`）" ⇒ E 层同形（同实时刻、`HEq` 中心）。 -/
theorem traceScalar_eventPrefix_DJ (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    (ρ δ B : ℝ)
    (h : ∀ x' ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' ρ,
      ∀ (w' : Icc (0 : ℝ) K.toHistory.horizon), (w' : ℝ) = τ' - δ →
      ∀ (hwt' : w' ≤ τ')
        (Bt' : BackwardPointTrace K.toHistory (K.toHistory.activeStage w')
          (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hwt') x'),
        metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage w') w')
          (Bt'.point (K.toHistory.activeStage w') le_rfl (K.toHistory.activeStage_mono hwt')) ≤
          B) :
    ∀ x ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p ρ,
      ∀ (w : Icc (0 : ℝ) E.horizon), (w : ℝ) = τ - δ →
      ∀ (hwt : w ≤ τ)
        (Bt : BackwardPointTrace E (E.activeStage w) (E.activeStage τ)
          (E.activeStage_mono hwt) x),
        metricScalarAt (E.stageMetric (E.activeStage w) w)
          (Bt.point (E.activeStage w) le_rfl (E.activeStage_mono hwt)) ≤ B := by
  subst hE
  intro x hx w hw hwt Bt
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  have hAτ := K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ
  have hl : K.toHistory.activeStage τ' = K.eIdx_C11G2 j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) := Fin.ext hAτ.symm
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hl.symm) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ p x p' x' hp hxx ρ hx
  let w' : Icc (0 : ℝ) K.toHistory.horizon := ⟨w, w.2.1, w.2.2.trans hTH⟩
  have hw' : (w' : ℝ) = τ' - δ := by
    change (w : ℝ) = τ' - δ
    rw [← hττ]
    exact hw
  have hres := K.forall_trace_eventPrefix_P6M j hjT hTj τ w hwt τ' w' hττ rfl x x' hxx
    (fun m z => metricScalarAt (K.toHistory.stageMetric m w) z ≤ B)
    (fun hvτ' tr' => h x' hx' w' hw' hvτ' tr') Bt
  rw [K.eventPrefix_stageMetric j hjT hTj]
  exact hres

/-- **K → E traced region（`_DJ`，E 抽象形）**：`isTracedRegion_eventPrefix_C11G3` 加 `E = …` 等式。 -/
theorem isTracedRegion_eventPrefix'_DJ (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    {ρ δ C : ℝ} (h : K.toHistory.isTracedRegion τ' p' ρ δ C) : E.isTracedRegion τ p ρ δ C := by
  subst hE
  exact K.isTracedRegion_eventPrefix_C11G3 j hjT hTj τ τ' hττ p p' hp h

end RetainedCoreHistory

namespace ObservedHistory

variable {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
  {hjt : ∀ n, (K n).time (j n).castSucc < t n} {htj : ∀ n, t n < (K n).time (j n).succ}
  {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon} {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
  {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ}

/-- **K → E `DepthExtendable`（`_DJ`）**：`depthExtendable_of_eventPrefix_P6M` 的反向（同子列、同深度）。 -/
theorem depthExtendable_eventPrefix_DJ
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {ψ : ℕ → ℕ} {T : ℝ}
    (h : DepthExtendable (fun n => (K n).toHistory) σ y R ψ T) :
    DepthExtendable Hs ts ys R ψ T := by
  intro A hA
  obtain ⟨C, hC, hev⟩ := h A hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with i hi
  exact (K (ψ i)).isTracedRegion_eventPrefix'_DJ (j (ψ i)) (hjt (ψ i)) (htj (ψ i)) (Hs (ψ i))
    (hHs (ψ i)) (ts (ψ i)) (σ (ψ i)) (hσ (ψ i)) (ys (ψ i)) (y (ψ i)) (hys (ψ i)) hi

/-- **`hsurvive` 槽 E → K（`_DJ`，PROVED）**：E 帧 driver 槽（`Hs ts ys`）⇒ K 帧槽
（DrvResE_DW `hsurvive` 文本逐字，`Kh n = (K n).toHistory`），同一 `Cst`。 -/
theorem hsurvive_K_of_eventPrefix_DJ
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {Cst : ℝ≥0}
    (hE : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n) →
        (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) :
    ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((K n).toHistory.stageMetric
            ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (A / Real.sqrt (R n)),
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            z ≤ Q * R n) →
        (K n).toHistory.isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (T / R n) (Kc * R n) := by
  intro A T Q hA hT hQ hstep
  obtain ⟨Kc, hKc, hev⟩ := hE A T Q hA hT hQ hstep
  refine ⟨Kc, hKc, ?_⟩
  filter_upwards [hev] with n hn
  intro hball
  exact (K n).isTracedRegion_of_eventPrefix'_P6M (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n)
    (σ n) (hσ n) (ys n) (y n) (hys n)
    (hn ((K n).ballScalar_eventPrefix_DJ (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n)
      (hσ n) (ys n) (y n) (hys n) _ _ hball))

/-- **`hextend` 槽 E → K（`_DJ`，PROVED）**：E 帧 driver 槽 ⇒ K 帧槽（DrvResE_DW `hextend` 文本逐字），
同一 `Cst`。前提 `DepthExtendable` 经 `depthExtendable_eventPrefix_DJ`（K → E），anchor 经
`traceScalar_eventPrefix_DJ`（K → E），结论经 `depthExtendable_of_eventPrefix_P6M`（E → K）。 -/
theorem hextend_K_of_eventPrefix_DJ
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {Cst : ℝ≥0}
    (hE : ∀ σs : ℕ → ℕ, StrictMono σs → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σs T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σs i)).stageMetric
          ((Hs (σs i)).activeStage (ts (σs i))) (ts (σs i))) (ys (σs i))
          (A / Real.sqrt (R (σs i))),
      ∀ (w : Icc (0 : ℝ) (Hs (σs i)).horizon),
        (w : ℝ) = ts (σs i) - T' / R (σs i) →
      ∀ (hwt : w ≤ ts (σs i))
        (Bt : BackwardPointTrace (Hs (σs i)) ((Hs (σs i)).activeStage w)
          ((Hs (σs i)).activeStage (ts (σs i)))
          ((Hs (σs i)).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σs i)).stageMetric ((Hs (σs i)).activeStage w) w)
          (Bt.point ((Hs (σs i)).activeStage w) le_rfl
            ((Hs (σs i)).activeStage_mono hwt)) ≤
          M * R (σs i)) →
      DepthExtendable Hs ts ys R σs (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1)))) :
    ∀ σs : ℕ → ℕ, StrictMono σs → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable (fun n => (K n).toHistory) σ y R σs T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((K (σs i)).toHistory.stageMetric
          ((K (σs i)).toHistory.activeStage (σ (σs i))) (σ (σs i))) (y (σs i))
          (A / Real.sqrt (R (σs i))),
      ∀ (w : Icc (0 : ℝ) (K (σs i)).toHistory.horizon),
        (w : ℝ) = σ (σs i) - T' / R (σs i) →
      ∀ (hwt : w ≤ σ (σs i))
        (Bt : BackwardPointTrace (K (σs i)).toHistory ((K (σs i)).toHistory.activeStage w)
          ((K (σs i)).toHistory.activeStage (σ (σs i)))
          ((K (σs i)).toHistory.activeStage_mono hwt) x),
        metricScalarAt ((K (σs i)).toHistory.stageMetric ((K (σs i)).toHistory.activeStage w) w)
          (Bt.point ((K (σs i)).toHistory.activeStage w) le_rfl
            ((K (σs i)).toHistory.activeStage_mono hwt)) ≤
          M * R (σs i)) →
      DepthExtendable (fun n => (K n).toHistory) σ y R σs
        (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))) := by
  intro σs hσs Tstar M hT hM hext hanc
  refine depthExtendable_of_eventPrefix_P6M hHs hσ hys
    (hE σs hσs Tstar M hT hM (fun T hT0 hTl => depthExtendable_eventPrefix_DJ hHs hσ hys
      (hext T hT0 hTl)) ?_)
  intro T' h1 h2 A hA
  filter_upwards [hanc T' h1 h2 A hA] with i hi
  have hσi := hσ (σs i)
  refine (K (σs i)).traceScalar_eventPrefix_DJ (j (σs i)) (hjt (σs i)) (htj (σs i)) (Hs (σs i))
    (hHs (σs i)) (ts (σs i)) (σ (σs i)) hσi (ys (σs i)) (y (σs i)) (hys (σs i)) _
    (T' / R (σs i)) _ ?_
  intro x' hx' w' hw' hwt' Bt'
  exact hi x' hx' w' hw' hwt' Bt'

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
