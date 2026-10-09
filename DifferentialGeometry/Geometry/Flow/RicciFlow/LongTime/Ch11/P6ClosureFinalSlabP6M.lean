import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedDepthP6D2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterGood_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeFinalP6M

/-!
# P6 收口（K-route，final-slab 情形；O-CH11-P6ANCH G3f，后缀 `_P6M`）

`false_of_selection_eventSlab_P6M`（`P6ClosureKRouteP6M`）的 final-slab 对应：selection 坏点 `σ n`
落在 final slab（`(K n).time (Fin.last _) < t n < (K n).horizon`）。P6D2 G3
`exists_subseq_htraced_extendAt_P6D2` 的数据前提取
`H n := (K n).prefixAt (Fin.last (K n).eventCount)`（`hend := prefixAt_time_last`）、
`G n := ((K n).finalSlab _).restrictIncoming le_rfl _ le_rfl`（`hGi := final_initial`）、
`s n := horizon`；`Hs n := ((H n).extendAt …).toHistory`（P6D2 G3 的 `hHs` 为 `rfl`）。路线与 event 情形相同：
1. P6D2 G3 在 `Hs` 上给 `htraced`（`Hs`-层 `hseed` / `hkappa` / `hwit` / `hbcad` 由 G3f 桥
   `*_seq_final_P6M` 从 **K 层**拉回）；
2. `depthExtendable_final_P6M` 把 `htraced` 送回 K 层 `(σ n, y n)`；
3. P6D G2 `exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D` 直接在 K 上用；
4. AD-good `false_of_not_good_of_eventually_good_P6L` 与 selection 的 `¬ Good_K` 矛盾。
`G` 以显式序列 + 形状等式 `hG` 给出（数据前提逐字写在 `G n` 上，与 P6D2 G3 同形）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- 标量按 stage 指标搬运（`m = m'`、度量 `g = stageMetric m v`、`HEq` 点）。 -/
private theorem scalar_congr_final_P6M (H : ObservedHistory.{u}) {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (v : ℝ) (g : (H.stage m).Metric) (hg : g = H.stageMetric m v)
    (p : (H.stage m).Carrier) (p' : (H.stage m').Carrier) (hp : HEq p p') :
    metricScalarAt g p = metricScalarAt (H.stageMetric m' v) p' := by
  subst hg
  subst hm
  obtain rfl := eq_of_heq hp
  rfl

/-- 基点标量：final 截断 history `E` 层 = K 层（同实时刻、`HEq` 点）。 -/
private theorem scalar_eq_final_P6M (K : RetainedCoreHistory.{u})
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
  exact scalar_congr_final_P6M K.toHistory hidx τ' _ hmet p p' hp

/-- **P6 收口（K-route，final-slab 情形）**：常数 `epsW, C` 在序列前取（P6D G2）；预选 `C ≤ C1'`、
`C ≤ C2'`、`C.toNNReal ≤ Ctime'`（D-9.2）。selection 坏点 `(σ n, y n)` 落在 final slab 内部
（`time (Fin.last _) < t n < horizon`）。数据前提（prefix `(K n).prefixAt (Fin.last _)` + final slab 的
incoming 形 `G n = ((K n).finalSlab _).restrictIncoming le_rfl _ le_rfl`）与 P6D2 G3 逐字；trace-local
前提全在 **K 层**。结论：selection 的 `¬ Good_K` 序列不存在。 -/
theorem false_of_selection_finalSlab_P6M :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan : ℕ → ℝ} → {p₀ p : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      {records : ∀ n i, GeometricCutoffRecord
        ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀
        ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory)) →
      (hrec : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).IsCanonicalCutoffRecordFamily
        (p₀ n) (δb n) (ρb n) (records n)) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime
        (qcan n) (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ((K n).prefixAt (Fin.last (K n).eventCount)).CapWindowPoint (records n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) (yG n) (t n) (D n)
        (θcap n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) * t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
          (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (yG n)) →
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
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ :=
    exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW
  refine ⟨C, hC, fun hC1 hC2 hCt => ?_⟩
  intro P₀ g₀ Ctime phi hphi K t htl htK G hG D θcap qcan p₀ p δb ρb records yG hinit hrec hqcan
    hpar hscale hθcap hpinch hslab hderG hqR hnot hRt hanchor0 Kh hKh σ y R hσ hyG hRn r₀ w hr₀ hw
    hseed κ hκ ρnc hradii hkappa Phi hPhi hpinchK C1s C2s Cs Cq Ctr qs qd hqs hqd hwit hderivK
    hbcad hsel
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
  -- 1. P6D2 G3 在 E 上给 htraced（E 层 trace-local 前提由 G3f 桥从 K 层拉回）
  obtain ⟨ψ, hψ, hall⟩ := exists_subseq_htraced_extendAt_P6D2
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    (s := fun n => (K n).horizon) (y := yG) hphi hinit
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial ((htl n).trans (htK n)))
    hrec hqcan hpar hscale hθcap hpinch hslab htl htK hderG hqR hnot hRt hanchor0 Hs ts ys R rfl
    HEq.rfl hys hRn hr₀ hw (hseed_seq_final_P6M hHs' hσ' hysK hseed) hκ ρnc hradii
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
      ((htl n).trans (htK n)) le_rfl) (s := fun n => (K n).horizon)
    (y := yG) (fun n => (K n).prefixAt_time_last _)
    (fun n => (K n).final_initial ((htl n).trans (htK n))) htl htK
    Hs ts ys R rfl HEq.rfl hys hRn
  have hscal : ∀ n, metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) = R n := fun n =>
    (scalar_eq_final_P6M (K n) ((htl n).trans (htK n)) (htl n) (htK n) (ts n) (σ n) (hσ' n)
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
  exact false_of_not_good_of_eventually_good_P6L hC1 hC2 hCt (fun m => (K (ψ m)).toHistory)
    (fun m => σ (ψ m)) (fun m => y (ψ m)) (fun m => hsel (ψ m)) ⟨ψ', hψ', hev⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
