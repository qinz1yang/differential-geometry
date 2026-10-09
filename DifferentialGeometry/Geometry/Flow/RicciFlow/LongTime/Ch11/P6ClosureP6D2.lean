import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedDepthP6D2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterGood_P6L

/-!
# P6 收口（条件形）：selection 的 `¬Good` 序列与 L7 任意深度 + L8 恢复矛盾（O-CH11-P6D2 G4）

后缀 `_P6D2`。把 G3 consumer `exists_eventually_hasSpatialCanonicalTimeControl_extendAt_P6D2`（htraced
子列喂 P6D G2：坏点子列 eventually **完整** `HasSpatialCanonicalTimeControl ε C C C.toNNReal`）与 P6A3
的 AD-good `false_of_not_good_of_eventually_good_P6L` 接起来：常数预选 `C ≤ C1'`、`C ≤ C2'`、
`C.toNNReal ≤ Ctime'`（D-9.2），则 `RetainedCoreHistory` + `extendAt` 坏点序列不能处处
`¬ HasSpatialCanonicalTimeControl ε C1' C2' Ctime'`。

**这是 P6 反证的收口型检查**；仍是条件定理，条件 = 数据前提（records / pinching / slab 导数 /
`¬ CapWindowPoint` / `hRt`）+ 基点 anchor `hanchor0` + trace-local `hseed` / `hkappa` / `hwit` /
`hbcad`。
把 point selection（`ST/CanonicalTimeControlPointSelection:55`）的坏点喂进来还缺（精确陈述见
`build-logs/resume/state-O-CH11-P6D2.md` 的 L9–L11 段）：selection 的 Good 区 ⇒ `hwit`（需距离
confinement `hdist`，R-C11-2 D-5）、`hanchor0`（`SLT:249_P6L`）、`hbcad`（更早时刻的 BCAD），以及
slice ↔ `RetainedCoreHistory` 终端 incoming slab 的桥（P6A3 G5 注 (b)）。
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

/-- **P6 收口（条件形）**：预选常数下，`extendAt` 坏点序列处处 `¬Good(ε, C1', C2', Ctime')` 与
G3（L7 任意深度 htraced）+ P6D G2（L8 恢复）矛盾。 -/
theorem false_of_not_good_extendAt_P6D2 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {D θcap qcan s t : ℕ → ℝ} → {p₀ p : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      {H : ℕ → RetainedCoreHistory.{u}} →
      {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)} →
      {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
        ((H n).time (Fin.last (H n).eventCount)) (s n)} →
      {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier} →
      (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory)) →
      (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) →
      (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
        (H n).initialMetric (Fin.last (H n).eventCount)) →
      (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n)) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi) →
      (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount)) →
      (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) → (hts : ∀ n, t n < s n) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n)) →
      (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
        (D n) (θcap n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n)) →
      (Hs : ℕ → ObservedHistory.{u}) → (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon) →
      (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) → (R : ℕ → ℝ) →
      (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory) →
      (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))) →
      (hys : ∀ n, HEq (ys n) (y n)) → (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
          ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
              ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
                (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
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
                (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} →
      {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
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
              Wt.capTubeHasNeckChart ε) →
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
                (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n) →
      (∀ n, ¬ (Hs n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (ts n) (ys n)) → False := by
  obtain ⟨epsW, hepsW, hB⟩ := exists_eventually_hasSpatialCanonicalTimeControl_extendAt_P6D2.{u}
  refine ⟨epsW, hepsW, fun ε hε hs hεW hεX hεN => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hs hεW hεX hεN
  refine ⟨C, hC, fun hC1 hC2 hCt => ?_⟩
  intro P₀ g₀ Ctime phi hphi D θcap qcan s t p₀ p δb ρb H records G y hinit hend hGi hrec hqcan
    hpar hscale hθcap hpinch hslab hat hts hderG hqR hnot hRt hanchor0 Hs ts ys R hHs hts' hys hRn
    r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwit hbcad hsel
  obtain ⟨σ, hσ, ψ, hψ, hev⟩ := hB' hphi hinit hend hGi hrec hqcan hpar hscale hθcap hpinch hslab
    hat hts hderG hqR hnot hRt hanchor0 Hs ts ys R hHs hts' hys hRn hr₀ hw hseed hκ ρnc hradii
    hkappa hqs hwit hbcad
  exact false_of_not_good_of_eventually_good_P6L hC1 hC2 hCt Hs ts ys hsel
    ⟨σ ∘ ψ, hσ.comp hψ, hev⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
