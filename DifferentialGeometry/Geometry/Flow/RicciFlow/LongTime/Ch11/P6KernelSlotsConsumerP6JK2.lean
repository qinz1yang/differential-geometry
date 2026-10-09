import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelAssembleExpP6JK2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bSwitchCoarseP6HPB3

/-!
# J10KERNEL G3 consumer：HP6B3 v3 `hkerJx` 槽的接线见证（O-CH11-J10KERNEL，`_P6JK2`）

生成器 `build-logs/scratch/O-CH11-J10KERNEL/gen/gen3y.py`（槽文本从 G3b 陈述切出）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **G3 consumer（lead 裁定 (a) 的内联 ∀ 槽装配形；只是接线见证）**：若对**任意** kernel 数据都有
{anchor 槽 `hslabsLoc`（+ 顶层 `hWBloc`）、slice 槽 `hbcadC`、(B) 行}，则 HP6B3 v3 槽
`hkerJx : NotKKernelExpNoJ10_P6HPB3` 成立（经 G3c-4，`C = p6CoarseC ε`，常数缺口 0）。
**注意**：`hslots` 的 (B) seed 行（`hclock` / `hsmall` / `hhalf`：`aSeed = Tn − 1`、seed 小曲率）对任意
seed 数据为假——冻结 kernel 形不含 E 帧 (B) 族，kernel binder 对 seed 无约束。故本 example 不付 `hkerJx`，只证
"四 kernel 槽 + (B) 行 ⇒ 冻结 exp kernel" 的接线；真实修复 = (B) 行进 kernel 合同（随 hgapJ 元组下传）。 -/
example
    (hWBloc : ∀ (ε : ℝ), ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0)
      (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A →
      ∀ (Cq θ : ℝ), 0 < θ →
      ∃ Q Λ Dcap Rrad ζ₀ Rad Bw c : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧ 0 < c ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
          (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
        Λ ≤ G.flow.scalar t y * t →
        ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - Bw / G.flow.scalar t y →
        ∀ (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
          GeometricCutoffRecord H.toHistory i p),
        (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
        Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
        ∀ (U : Set (H.stage (Fin.last H.eventCount)).Carrier),
        (∀ w ∈ riemannianBallOf (G.flow.base.metric t) y (Rad / Real.sqrt (G.flow.scalar t y)),
          w ∈ U) →
        (∀ x ∈ U, q < G.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        (∀ j : Fin H.eventCount,
          ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - Bw / G.flow.scalar t y ≤ v →
          (t - v) * max q (G.flow.scalar t z) ≤ c →
          q < (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * (H.toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential G.flow v x w| ≤
              Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
                Real.sqrt ((G.flow.base.metric v).inner x w w)) →
        (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
          (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - Bw / G.flow.scalar t y)) phi) →
        Perelman.PhiAlmostNonnegative G.flow
          (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - Bw / G.flow.scalar t y)) phi →
        (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
          t - Bw / G.flow.scalar t y ≤ T →
          let B := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
          let tm : Icc (0 : ℝ) B.horizon := ⟨T, H.horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) →
        Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
        (¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
          (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
          G.flow.scalar t z ≤ Q * G.flow.scalar t y)
    (hslots : ∀ (Ctime' : ℝ≥0) (K : ℕ → RetainedCoreHistory.{u}) (T₀ : ℕ → ℝ)
      (p : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n))
      (a₀ : ℕ → ℝ) (Kh : ℕ → ObservedHistory.{u}) (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R : ℕ → ℝ)
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
      (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) (Cg : ℝ)
      (L : ℕ → ℝ) (κ Aκ : ℝ) (r ρV : ℕ → ℝ),
        (∀ (j : ∀ n, Fin (K n).eventCount)
        (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier),
        (∀ n, (K n).time (j n).castSucc < (σ n : ℝ)) →
        (∀ n, (σ n : ℝ) < (K n).time (j n).succ) → (∀ n, HEq (y n) (yG n)) →
        ∀ Rad B c : ℝ, ∀ᶠ n in atTop,
        ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (σ n : ℝ))
            (yG n)
            (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (σ n : ℝ) (yG n))),
        ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
        ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
          (((K n).prefixAt (j n).castSucc).time i.succ),
        (σ n : ℝ) - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n : ℝ) (yG n) ≤ v →
        ((σ n : ℝ) - v) * max (Cg * R n)
            (((K n).toHistory.event (j n)).incoming.flow.scalar (σ n : ℝ) z) ≤ c →
        Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w =>
            (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
              (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
            (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2) ∧
        (0 < κ →
        (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
        (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
        (∀ᶠ n in atTop,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n)) →
        (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal (Aκ * r n)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) →
        (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∀ᶠ n in atTop,
        ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
            (Kh n).time j'.castSucc < τ →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
        ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
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
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) ∧
        (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2) ∧
        (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) 1) ∧
        (∀ n, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n) ∧
        (∀ n, 0 < a₀ n) ∧
        (∀ n, StandardCap.transitionEnd + 10 < (p n).modelRadius) ∧
        (∀ n, T₀ n ≤ aSeed n) ∧
        (∀ n, 1 ≤ (aSeed n : ℝ)) ∧
        (∀ M : ℝ, ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount)
        (hi : T₀ n ≤ (K n).time i.succ) b, (aSeed n : ℝ) < (K n).time i.succ →
          M * R n < ((recordsK n i hi).static b).neck.scale) ∧
        (∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)) :
    NotKKernelExpNoJ10_P6HPB3.{u} := by
  intro ε hε h11 hεW hεX hεN hεcone
  have h := @notKBody_noJ10_coarse_P6JK2.{u} hWBloc ε hε h11 hεW hεX hεN hεcone
  unfold NotKBodyNoJ10_P6HPB3
  intro C1' C2' Ctime' hC1 hC2 hCt Ctime phi hphi K Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF
    hacc hrad hord hscaleK hbirthA hpinchK0 hslabK Kh hKh σ y hpos R hRdef hRpos hRlt hnotKs κd hκd
    hvolK aP haP hpinL Tn aSeed haT hsT has hT₀ pT seedTrace L hL Cg hCg hgood hwin hdistC hdistW κ
    Aκ hκ r ρV hρV hroom hdistσ hκR hclosG hsel
  obtain ⟨hsl, hbc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hslots Ctime' K T₀ p recordsK a₀
    Kh σ y R Tn aSeed haT hsT has pT seedTrace Cg L κ Aκ r ρV
  exact h hC1 hC2 hCt hphi recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK Kh
    hKh σ y hpos R hRdef hRpos hRlt hnotKs hκd hvolK haP hpinL Tn aSeed haT hsT has hT₀ pT seedTrace
    L hL Cg hCg hgood hwin hdistC hdistW hκ r ρV hρV hroom hdistσ hκR hclosG hsl hbc h1 h2 h3 h4
    h5 h6 h7 h8 h9 hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
