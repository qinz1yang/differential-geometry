import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteHIFinalP6HF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingC11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GoodConstantsP6P

/-!
# late 主形 prefix 层的精度解耦孪生（O-CH11-RERUN8 G1a，后缀 `_P6R8`）

HREST2 handover 所说的 "`false_of_rerun_decoupled_P6P` 的 lateHI 版"：
* `false_of_selection_eventSlab_lateHI_prefix_dec_P6R8` = P6LATE
  `false_of_selection_eventSlab_lateHI_prefix_P6LT` 逐字，只换两处引理：step 3 的 P6D
  `exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D` ↦ PREC
  `ancientWitness_decoupled_P6P`（`εin := ε` = 左侧 `hwit` 精度，`ηout := η₁`），step 4 的
  `false_of_not_good_of_eventually_good_P6L` ↦ `false_of_not_good_of_eventually_good_decoupled_P6P`
  （`εsel := η₁`）。坏点 `hsel` 在 `(η₁, C1₁, C2₁, Ctime₁)`，左侧 witness 在 `ε`（`η₁`、`ε` 无大小要求）。
* `false_of_selection_finalSlab_lateHI_prefix_dec_P6R8` = HCLOSEF
  `false_of_selection_finalSlab_lateHI_prefix_P6HF` 的同样解耦。
常数是 closed term（不是 `∃`）：精度上限 `Classical.choose ancientWitness_decoupled_P6P`；坏点常数下界
直接用 GAPTOP6 的 `p6CoarseC_C11GT6 η₁`（`= ancientWitness_decoupled_P6P` 在 `ηout := η₁` 处的 choice，
`p6CoarseC_eq_C11GT6`），即 ceiling X 清单里的 `Cco η₁`。private 小引理照抄（后缀 `_P6R8H`）。
陈述由 build-logs/scratch/O-CH11-RERUN8/gen.py 从源文本生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6CoarseC_eq_C11GT6 one_le_p6CoarseC_C11GT6)

namespace ObservedHistory

/-- 标量按 stage 指标搬运（`m = m'`、度量 `g = stageMetric m v`、`HEq` 点）。 -/
private theorem scalar_congr_P6R8H (H : ObservedHistory.{u}) {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (v : ℝ) (g : (H.stage m).Metric) (hg : g = H.stageMetric m v)
    (p : (H.stage m).Carrier) (p' : (H.stage m').Carrier) (hp : HEq p p') :
    metricScalarAt g p = metricScalarAt (H.stageMetric m' v) p' := by
  subst hg
  subst hm
  obtain rfl := eq_of_heq hp
  rfl

/-- 基点标量：E（`K.eventPrefix j T`）层 = K 层（同实时刻、`HEq` 点）。 -/
private theorem scalar_eq_of_eventPrefix_P6R8H (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {T : ℝ} (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (τ : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
    (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier)
    (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p') :
    metricScalarAt ((K.eventPrefix j T hjT hTj).toHistory.stageMetric
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ) p =
      metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' := by
  have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ)
  have hmet := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ
  rw [hττ] at hmet
  rw [hττ]
  exact scalar_congr_P6R8H K.toHistory hidx τ' _ hmet p p' hp

/-- 基点标量：final 截断 history `E` 层 = K 层（同实时刻、`HEq` 点）。 -/
private theorem scalar_eq_final_P6R8H (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon), (τ : ℝ) = τ' →
    ∀ (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier), HEq p p' →
      metricScalarAt (E.stageMetric (E.activeStage τ) τ) p =
        metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' := by
  intro E τ τ' hττ p p' hp
  have hidx : @Eq (Fin (K.toHistory.eventCount + 1)) (E.activeStage τ)
      (K.toHistory.activeStage τ') := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  have hmet : E.stageMetric (E.activeStage τ) τ' =
      K.toHistory.stageMetric (E.activeStage τ) τ' := K.stageMetric_final_P6M hfin hT hTs _ _
  rw [hττ]
  exact scalar_congr_P6R8H K.toHistory hidx τ' _ hmet p p' hp

/-- **late prefix 层，event slab，精度解耦（`_P6R8`）**：见文件头。 -/
theorem false_of_selection_eventSlab_lateHI_prefix_dec_P6R8 {η₁ : ℝ}
    (hη : 0 < η₁ ∧ η₁ < 1 / 11) {ε : ℝ} (hε : 0 < ε)
    (hεW : ε ≤ Classical.choose ancientWitness_decoupled_P6P.{u})
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    {C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0} (hC1 : p6CoarseC_C11GT6.{u} η₁ ≤ C1₁)
    (hC2 : p6CoarseC_C11GT6.{u} η₁ ≤ C2₁) (hCt : (p6CoarseC_C11GT6.{u} η₁).toNNReal ≤ Ctime₁) :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
              (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {Phi : ℝ → ℝ} → (hPhi : Perelman.AdmissiblePinchingFunction Phi) →
      (hpinchK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))))) →
      {C1s C2s Cs Cq : ℝ} → {Ctr : ℝ≥0} → {qs qd : ℕ → ℝ} →
      (hqs : ∀ n, qs n ≤ Cs * R n) → (hqd : ∀ n, qd n ≤ Cq * R n) →
      (hwit : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hderivK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qd n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctr * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) →
      (hbcad : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ n) (y n)) →
      False := by
  obtain ⟨-, hB⟩ := Classical.choose_spec
    ((Classical.choose_spec ancientWitness_decoupled_P6P.{u}).2 η₁ hη.1 hη.2)
  have hB' := hB ε hε hεW
  rw [p6CoarseC_eq_C11GT6 hη] at hC1 hC2 hCt
  intro Ctime phi hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ hHI hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R hσ
    hyG hRn r₀
    w hr₀ hw hseed κ hκ ρnc hradii hkappa Phi hPhi hpinchK C1s C2s Cs Cq Ctr qs qd hqs hqd hwit
    hderivK hbcad hsel
  subst hKh
  -- E 层（`Hs n = (K n).eventPrefix (j n) (t n)`）的基点对象
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (j n).castSucc).extendAtTime ((K n).prefixAt_time_last _)
      ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hjt n) (htj n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun n => (hσ n).symm
  have hidx : ∀ n, Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (j n).castSucc.isLt))
      ((Hs n).activeStage (ts n)) = (K n).toHistory.activeStage (σ n) := fun n =>
    Fin.ext ((K n).eventPrefix_activeStage_val (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n))
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hidx n)).symm (y n)
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  have hHs' : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory :=
    fun _ => rfl
  -- 1. P6D2 G3 在 E 上给 htraced（E 层 trace-local 前提由 G3 桥从 K 层拉回）
  obtain ⟨ψ, hψ, hall⟩ := exists_subseq_htraced_extendAt_lateHI_P6LT
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) hphi recordsF hHI
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hδF hqcan hpar
    hscale hbirthA hθcap hpinch hslab hjt htj hderG hqR hnot hT₀ hRt hanchor0 Hs ts ys R rfl
    HEq.rfl hys
    hRn
    hr₀ hw (hseed_seq_of_eventPrefix_P6M hHs' hσ' hysK hseed) hκ ρnc hradii
    (hkappa_seq_of_eventPrefix_P6M hHs' hσ' hysK hkappa) hε hεX hεN hqs
    (hwit_seq_of_eventPrefix_P6M hHs' hσ' hysK hwit)
    (hbcad_seq_of_eventPrefix_P6M hHs' hσ' hysK hbcad)
  -- 2. htraced 回 K
  have hallK : ∀ T : ℝ, 0 < T → DepthExtendable (fun n => (K n).toHistory) σ y R ψ T :=
    fun T hT => depthExtendable_of_eventPrefix_P6M hHs' hσ' hysK (hall T hT)
  -- 3. P6D G2 直接在 K 上
  have hR : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  have hRlim : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    rw [hRn n]
    linarith [hqcan n, hqR n]
  have hscalE := scal_of_extendAt_P6D2 (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    Hs ts ys R rfl HEq.rfl hys hRn
  have hscal : ∀ n, metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) = R n := fun n =>
    (scalar_eq_of_eventPrefix_P6R8H (K n) (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n) (ys n) (y n)
      (hysK n)).symm.trans (hscalE n)
  obtain ⟨-, ψ', hψ', hev⟩ := hB' (fun m => (K (ψ m)).toHistory) (fun m => σ (ψ m))
    (fun m => y (ψ m)) (fun m => R (ψ m)) (fun m => hR (ψ m)) (fun m => hscal (ψ m))
    (hRlim.comp hψ.tendsto_atTop) (fun A T hA hT => hallK T hT A hA) hr₀ hw
    (hψ.tendsto_atTop.eventually hseed) hκ (fun m => ρnc (ψ m)) (hradii.comp hψ.tendsto_atTop)
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hkappa D T hD hT)) hPhi
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hpinchK D T hD hT)) (fun m => hqs (ψ m))
    (fun m => hqd (ψ m)) (fun D T hD hT => hψ.tendsto_atTop.eventually (hwit D T hD hT))
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hderivK D T hD hT))
  -- 4. AD-good
  exact false_of_not_good_of_eventually_good_decoupled_P6P le_rfl hη.2 hC1 hC2 hCt
    (fun m => (K (ψ m)).toHistory) (fun m => σ (ψ m)) (fun m => y (ψ m)) (fun m => hsel (ψ m))
    ⟨ψ', hψ', hev⟩

/-- **late prefix 层，final slab，精度解耦（`_P6R8`）**：见文件头。 -/
theorem false_of_selection_finalSlab_lateHI_prefix_dec_P6R8 {η₁ : ℝ}
    (hη : 0 < η₁ ∧ η₁ < 1 / 11) {ε : ℝ} (hε : 0 < ε)
    (hεW : ε ≤ Classical.choose ancientWitness_decoupled_P6P.{u})
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    {C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0} (hC1 : p6CoarseC_C11GT6.{u} η₁ ≤ C1₁)
    (hC2 : p6CoarseC_C11GT6.{u} η₁ ≤ C2₁) (hCt : (p6CoarseC_C11GT6.{u} η₁).toNNReal ≤ Ctime₁) :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K
        n).eventCount)).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
          n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
          →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
          (G n).flow.scalar (t n) z ≤
            Q * (G n).flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {Phi : ℝ → ℝ} → (hPhi : Perelman.AdmissiblePinchingFunction Phi) →
      (hpinchK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))))) →
      {C1s C2s Cs Cq : ℝ} → {Ctr : ℝ≥0} → {qs qd : ℕ → ℝ} →
      (hqs : ∀ n, qs n ≤ Cs * R n) → (hqd : ∀ n, qd n ≤ Cq * R n) →
      (hwit : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hderivK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qd n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctr * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) →
      (hbcad : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ n) (y n)) →
      False := by
  obtain ⟨-, hB⟩ := Classical.choose_spec
    ((Classical.choose_spec ancientWitness_decoupled_P6P.{u}).2 η₁ hη.1 hη.2)
  have hB' := hB ε hε hεW
  rw [p6CoarseC_eq_C11GT6 hη] at hC1 hC2 hCt
  intro Ctime phi hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀ hHI hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R hσ
    hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa Phi hPhi hpinchK C1s C2s Cs Cq Ctr qs qd hqs
    hqd hwit hderivK hbcad hsel
  subst hKh
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  -- E 层（`Hs n` = final 截断 history）的基点对象
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt ((K n).prefixAt_time_last _)
      (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl ((htl n).trans (htK n))
        le_rfl) ((K n).final_initial ((htl n).trans (htK n))) (htl n) (htK n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (Fin.last (K n).eventCount)).extendAtTime ((K n).prefixAt_time_last _)
      (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl ((htl n).trans (htK n))
        le_rfl) ((K n).final_initial ((htl n).trans (htK n))) (htl n) (htK n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun n => (hσ n).symm
  have hidx : ∀ n, @Eq (Fin ((K n).toHistory.eventCount + 1)) ((Hs n).activeStage (ts n))
      ((K n).toHistory.activeStage (σ n)) := fun n =>
    (K n).activeStage_final_P6M ((htl n).trans (htK n)) (htl n) (htK n) (ts n) (σ n) (hσ' n)
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hidx n)).symm (y n)
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  have hHs' : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory := fun _ => rfl
  -- 1. lateHI kernel 在 E 上给 htraced（E 层 trace-local 前提由 final 桥从 K 层拉回）
  obtain ⟨ψ, hψ, hall⟩ := exists_subseq_htraced_extendAt_lateHI_P6LT
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    (s := fun n => (K n).horizon) (y := yG) hphi recordsF hHI
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial ((htl n).trans (htK n)))
      hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab htl htK hderG hqR hnot hT₀ hRt hanchor0 Hs ts ys
    R rfl HEq.rfl hys hRn hr₀ hw (hseed_seq_final_P6M hHs' hσ' hysK hseed) hκ ρnc hradii
    (hkappa_seq_final_P6M hHs' hσ' hysK hkappa) hε hεX hεN hqs
    (hwit_seq_final_P6M hHs' hσ' hysK hwit)
    (hbcad_seq_final_P6M hHs' hσ' hysK hbcad)
  -- 2. htraced 回 K
  have hallK : ∀ T : ℝ, 0 < T → DepthExtendable (fun n => (K n).toHistory) σ y R ψ T :=
    fun T hT => depthExtendable_final_P6M hHs' hσ' hysK (hall T hT)
  -- 3. P6D G2 直接在 K 上
  have hR : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  have hRlim : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    rw [hRn n]
    linarith [hqcan n, hqR n]
  have hscalE := scal_of_extendAt_P6D2
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    (s := fun n => (K n).horizon) (y := yG) (fun n => (K n).prefixAt_time_last _)
    (fun n => (K n).final_initial ((htl n).trans (htK n))) htl htK Hs ts ys R rfl HEq.rfl hys hRn
  have hscal : ∀ n, metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) = R n := fun n =>
    (scalar_eq_final_P6R8H (K n) ((htl n).trans (htK n)) (htl n) (htK n) (ts n) (σ n) (hσ' n)
      (ys n) (y n) (hysK n)).symm.trans (hscalE n)
  obtain ⟨-, ψ', hψ', hev⟩ := hB' (fun m => (K (ψ m)).toHistory) (fun m => σ (ψ m))
    (fun m => y (ψ m)) (fun m => R (ψ m)) (fun m => hR (ψ m)) (fun m => hscal (ψ m))
    (hRlim.comp hψ.tendsto_atTop) (fun A T hA hT => hallK T hT A hA) hr₀ hw
    (hψ.tendsto_atTop.eventually hseed) hκ (fun m => ρnc (ψ m)) (hradii.comp hψ.tendsto_atTop)
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hkappa D T hD hT)) hPhi
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hpinchK D T hD hT)) (fun m => hqs (ψ m))
    (fun m => hqd (ψ m)) (fun D T hD hT => hψ.tendsto_atTop.eventually (hwit D T hD hT))
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hderivK D T hD hT))
  -- 4. AD-good
  exact false_of_not_good_of_eventually_good_decoupled_P6P le_rfl hη.2 hC1 hC2 hCt
    (fun m => (K (ψ m)).toHistory) (fun m => σ (ψ m)) (fun m => y (ψ m)) (fun m => hsel (ψ m))
    ⟨ψ', hψ', hev⟩

/-- consumer：坏点精度 `η₁ = 1/40` 比左侧精度 `ε := min epsW (1/20)` 细时，常数前提可满足
（`C1₁ = C2₁ := Cco η₁ ≥ 1`、`Ctime₁ := (Cco η₁).toNNReal`）。 -/
example : 0 < min (Classical.choose ancientWitness_decoupled_P6P.{0}) (1 / 20) ∧
    1 ≤ p6CoarseC_C11GT6.{0} (1 / 40) :=
  ⟨lt_min (Classical.choose_spec ancientWitness_decoupled_P6P.{0}).1 (by norm_num),
    one_le_p6CoarseC_C11GT6 _⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
