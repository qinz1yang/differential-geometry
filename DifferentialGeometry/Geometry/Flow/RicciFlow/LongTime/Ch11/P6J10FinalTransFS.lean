import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FinalCondKRouteFullP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeFinalP6M

/-!
# FSUP W2-A：final 截断帧 `E` ↔ `K` 的 traced region / 球标量 / trace 标量搬运（`_FS`）

`P6DrvJ10AdaptDJ`（eventPrefix 帧）的 final 孪生。
`E := ((K.prefixAt last).extendAt … finalSlab …).toHistory`（时刻 `T ∈ (time last, horizon)`），
`E` 与 `K` 在 `≤ T` 的 stage / event / metric 定义等，trace 直接重组：
* `ballScalar_final_FS` / `traceScalar_final_FS`：K → E（球上标量界 / backward-trace 标量界）；
* `isTracedRegion_KtoE_final_FS`：K → E traced region（`isTracedRegion_final_P6M` 的反向）；
* `depthExtendable_KtoE_final_FS`：K → E `DepthExtendable`；
* `hsurvive_K_of_final_FS` / `hextend_K_of_final_FS`：E 帧 driver 槽 ⇒ K 帧槽（同一 `Cst`）。
PROVED，无新前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- **K → E 球上标量界（final，`_FS`）**：K 在实时刻 `τ'`、中心 `p'` 的球上 `scalar ≤ B` ⇒ E 在同一
实时刻 `τ`、`HEq` 中心的同半径球上 `scalar ≤ B`。 -/
theorem ballScalar_final_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E = ((K.prefixAt (Fin.last K.eventCount)).extendAt
      (K.prefixAt_time_last _) ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
      (K.final_initial hfin) hT hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    (ρ B : ℝ)
    (h : ∀ z ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' ρ,
      metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') z ≤ B) :
    ∀ z ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p ρ,
      metricScalarAt (E.stageMetric (E.activeStage τ) τ) z ≤ B := by
  subst hE
  intro z hz
  have hAτ := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  let z' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hAτ) z
  have hzz : HEq z z' := (cast_heq _ _).symm
  have hz' := K.mem_ball_final_P6M hfin hT hTs τ τ' hττ p z p' z' hp hzz ρ hz
  rw [ObservedHistory.scalar_eq_final_P6JAH K hfin hT hTs τ τ' hττ z z' hzz]
  exact h z' hz'

/-- **K → E trace 标量界（final，`_FS`）**：K 层"球内每点、每条 `[w', τ']` backward trace 在 `w'` 处
`scalar ≤ B`（`w' = τ' − δ`）" ⇒ E 层同形（同实时刻、`HEq` 中心）。 -/
theorem traceScalar_final_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E = ((K.prefixAt (Fin.last K.eventCount)).extendAt
      (K.prefixAt_time_last _) ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
      (K.final_initial hfin) hT hTs).toHistory)
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
  have hAτ := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hAτ) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_final_P6M hfin hT hTs τ τ' hττ p x p' x' hp hxx ρ hx
  let w' : Icc (0 : ℝ) K.toHistory.horizon := ⟨w, w.2.1, w.2.2.trans hTs.le⟩
  have hw' : (w' : ℝ) = τ' - δ := by
    change (w : ℝ) = τ' - δ
    rw [← hττ]
    exact hw
  have hres := K.forall_trace_final_P6M hfin hT hTs τ w hwt τ' w' hττ rfl x x' hxx
    (fun m z => metricScalarAt (K.toHistory.stageMetric m w) z ≤ B)
    (fun hvτ' tr' => h x' hx' w' hw' hvτ' tr') Bt
  refine le_of_eq_of_le ?_ hres
  exact congrArg (fun g => metricScalarAt g _) (K.stageMetric_final_P6M hfin hT hTs _ _)

/-- stage 指标推广：`m' = m` 时 `‖Rm‖² ≤ C²` 在两种指标写法间搬运（`_FS`）。 -/
private theorem rm_sq_bound_of_stage_eq_final_FS {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (B : BackwardPointTrace H first last hle x) {m m' : Fin (H.eventCount + 1)} (hm : m' = m)
    (h1 : first ≤ m) (h2 : m ≤ last) (h1' : first ≤ m') (h2' : m' ≤ last) (v C : ℝ)
    (h : normSq0S (H.stageMetric m' v) (B.point m' h1' h2') 4
      (metricRm04At (H.stageMetric m' v) (B.point m' h1' h2')) ≤ C ^ 2) :
    normSq0S (H.stageMetric m v) (B.point m h1 h2) 4
      (metricRm04At (H.stageMetric m v) (B.point m h1 h2)) ≤ C ^ 2 := by
  subst hm
  exact h

/-- traced region 的 stage 指标推广形（`P6SliceHistoryBridgeFinalP6M` 私有 helper 的逐字副本，`_FS`）。 -/
private theorem isTracedRegion_of_stage_index_final_FS (H : ObservedHistory.{u})
    (τ : Icc (0 : ℝ) H.horizon) (last : Fin (H.eventCount + 1)) (hlast : H.activeStage τ = last)
    (p : (H.stage last).Carrier) (p' : (H.stageAt τ).Carrier) (hp : HEq p p')
    {ρ δ C : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ τ) (ha : (a : ℝ) = (τ : ℝ) - δ)
    (first : Fin (H.eventCount + 1)) (hfirst : first ≤ H.activeStage a) (hf : first ≤ last)
    (htrace : ∀ x ∈ riemannianBallOf (H.stageMetric last τ) p ρ,
      ∃ B : BackwardPointTrace H first last hf x,
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ τ),
          normSq0S (H.stageMetric (H.activeStage v) v)
            (B.point (H.activeStage v) (hfirst.trans (H.activeStage_mono hav))
              ((H.activeStage_mono hvt).trans hlast.le)) 4
            (metricRm04At (H.stageMetric (H.activeStage v) v)
              (B.point (H.activeStage v) (hfirst.trans (H.activeStage_mono hav))
                ((H.activeStage_mono hvt).trans hlast.le))) ≤ C ^ 2) ∧
        ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc) (hil : i.succ ≤ last),
          let y : (H.event i).incoming.terminalRegularOpen :=
            ⟨B.point i.castSucc (hfirst.trans hi) (i.castSucc_lt_succ.le.trans hil),
              (B.crossing i (hfirst.trans hi) hil).mem_terminalRegularRegion (H.event i)⟩;
          normSq0S (H.event i).terminal.metric y 4
            (metricRm04At (H.event i).terminal.metric y) ≤ C ^ 2) :
    H.isTracedRegion τ p' ρ δ C := by
  subst hlast
  obtain rfl := eq_of_heq hp
  refine ⟨hρ, hδ, a, hat, ha, fun x hx => ?_⟩
  obtain ⟨B, hobs, hseam⟩ := htrace x hx
  exact ⟨B.restrictFirst hfirst (H.activeStage_mono hat), hobs, fun i hi hil => hseam i hi hil⟩

/-- **K → E traced region（final，`_FS`，PROVED）**：`isTracedRegion_final_P6M` 的反向。K 的 traced
region（时刻 `τ'`、中心 `p'`）⇒ final 截断 history `E` 的 traced region（同一实时刻 `τ ≤ T`、`HEq` 中心，
半径 / 深度 / 曲率界不变）。trace 直接重组。 -/
theorem isTracedRegion_KtoE_final_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) {ρ δ C : ℝ} :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon), (τ : ℝ) = τ' →
    ∀ (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier), HEq p p' →
      K.toHistory.isTracedRegion τ' p' ρ δ C → E.isTracedRegion τ p ρ δ C := by
  intro E τ τ' hττ p p' hp h
  obtain ⟨hρ, hδ, a', hat', ha', htr⟩ := h
  have hτT : (τ : ℝ) ≤ T := τ.2.2
  have hat'τ : (a' : ℝ) ≤ τ := by rw [hττ]; exact hat'
  let a : Icc (0 : ℝ) E.horizon := ⟨a', a'.2.1, hat'τ.trans hτT⟩
  have hat : a ≤ τ := hat'τ
  have ha : (a : ℝ) = (τ : ℝ) - δ := by
    change (a' : ℝ) = (τ : ℝ) - δ
    rw [hττ]
    exact ha'
  have hAτ : @Eq (Fin (K.toHistory.eventCount + 1)) (E.activeStage τ)
      (K.toHistory.activeStage τ') := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  have hAa : @Eq (Fin (K.toHistory.eventCount + 1)) (E.activeStage a)
      (K.toHistory.activeStage a') := K.activeStage_final_P6M hfin hT hTs a a' rfl
  refine isTracedRegion_of_stage_index_final_FS E τ (K.toHistory.activeStage τ') hAτ p' p
    hp.symm hρ hδ a hat ha (K.toHistory.activeStage a') hAa.symm.le
    (K.toHistory.activeStage_mono hat') ?_
  intro x hx
  have hm : E.stageMetric (K.toHistory.activeStage τ') τ =
      K.toHistory.stageMetric (K.toHistory.activeStage τ') τ :=
    K.stageMetric_final_P6M hfin hT hTs _ _
  have hxK : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
      p' ρ := by
    rw [hm, hττ] at hx
    exact hx
  obtain ⟨A', hA1, hA2⟩ := htr x hxK
  refine ⟨⟨A'.point, A'.endpoint_eq, A'.crossing⟩, ?_, ?_⟩
  · intro v hav hvt
    let vK : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTs.le⟩
    have hAv : @Eq (Fin (K.toHistory.eventCount + 1)) (E.activeStage v)
        (K.toHistory.activeStage vK) := K.activeStage_final_P6M hfin hT hTs v vK rfl
    have hav' : a' ≤ vK := show (a' : ℝ) ≤ v from hav
    have hvt' : vK ≤ τ' := show (v : ℝ) ≤ τ' by rw [← hττ]; exact hvt
    have hb := hA1 vK hav' hvt'
    have hmv : E.stageMetric (E.activeStage v) v =
        K.toHistory.stageMetric (E.activeStage v) v := K.stageMetric_final_P6M hfin hT hTs _ _
    rw [hmv]
    exact rm_sq_bound_of_stage_eq_final_FS A' (m' := K.toHistory.activeStage vK)
      (m := E.activeStage v) hAv.symm _ _ (K.toHistory.activeStage_mono hav')
      (K.toHistory.activeStage_mono hvt') v C hb
  · intro i hi hil
    exact hA2 i (hAa.symm.le.trans hi) hil

/-- traced region K → E（`E` 抽象 + 等式形，供序列层逐 n 调用）。 -/
theorem isTracedRegion'_KtoE_final_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E = ((K.prefixAt (Fin.last K.eventCount)).extendAt
      (K.prefixAt_time_last _) ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
      (K.final_initial hfin) hT hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    {ρ δ C : ℝ} (h : K.toHistory.isTracedRegion τ' p' ρ δ C) : E.isTracedRegion τ p ρ δ C := by
  subst hE
  exact K.isTracedRegion_KtoE_final_FS hfin hT hTs τ τ' hττ p p' hp h

end RetainedCoreHistory

namespace ObservedHistory

variable {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
  {htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n} {htK : ∀ n, t n < (K n).horizon}
  {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon} {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
  {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ}

/-- **K → E `DepthExtendable`（final，`_FS`）**：`depthExtendable_final_P6M` 的反向（同子列、同深度）。 -/
theorem depthExtendable_KtoE_final_FS
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {ψ : ℕ → ℕ} {T : ℝ}
    (h : DepthExtendable (fun n => (K n).toHistory) σ y R ψ T) :
    DepthExtendable Hs ts ys R ψ T := by
  intro A hA
  obtain ⟨C, hC, hev⟩ := h A hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with i hi
  exact (K (ψ i)).isTracedRegion'_KtoE_final_FS ((htl (ψ i)).trans (htK (ψ i))) (htl (ψ i))
    (htK (ψ i)) (Hs (ψ i)) (hHs (ψ i)) (ts (ψ i)) (σ (ψ i)) (hσ (ψ i)) (ys (ψ i)) (y (ψ i))
    (hys (ψ i)) hi

/-- **`hsurvive` 槽 E → K（final，`_FS`，PROVED）**：E 帧 driver 槽（`Hs ts ys`）⇒ K 帧槽
（DrvResE_DW `hsurvive` 文本逐字，`Kh n = (K n).toHistory`），同一 `Cst`。 -/
theorem hsurvive_K_of_final_FS
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
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
  exact (K n).isTracedRegion'_final_P6M ((htl n).trans (htK n)) (htl n) (htK n) (Hs n) (hHs n)
    (ts n) (σ n) (hσ n) (ys n) (y n) (hys n)
    (hn ((K n).ballScalar_final_FS ((htl n).trans (htK n)) (htl n) (htK n) (Hs n) (hHs n) (ts n)
      (σ n) (hσ n) (ys n) (y n) (hys n) _ _ hball))

/-- **`hextend` 槽 E → K（final，`_FS`，PROVED）**：E 帧 driver 槽 ⇒ K 帧槽（DrvResE_DW `hextend`
文本逐字），同一 `Cst`。前提 `DepthExtendable` 经 `depthExtendable_KtoE_final_FS`（K → E），anchor 经
`traceScalar_final_FS`（K → E），结论经 `depthExtendable_final_P6M`（E → K）。 -/
theorem hextend_K_of_final_FS
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
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
  refine depthExtendable_final_P6M hHs hσ hys
    (hE σs hσs Tstar M hT hM (fun T hT0 hTl => depthExtendable_KtoE_final_FS hHs hσ hys
      (hext T hT0 hTl)) ?_)
  intro T' h1 h2 A hA
  filter_upwards [hanc T' h1 h2 A hA] with i hi
  have hσi := hσ (σs i)
  refine (K (σs i)).traceScalar_final_FS ((htl (σs i)).trans (htK (σs i))) (htl (σs i))
    (htK (σs i)) (Hs (σs i)) (hHs (σs i)) (ts (σs i)) (σ (σs i)) hσi (ys (σs i)) (y (σs i))
    (hys (σs i)) _ (T' / R (σs i)) _ ?_
  intro x' hx' w' hw' hwt' Bt'
  exact hi x' hx' w' hw' hwt' Bt'

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
