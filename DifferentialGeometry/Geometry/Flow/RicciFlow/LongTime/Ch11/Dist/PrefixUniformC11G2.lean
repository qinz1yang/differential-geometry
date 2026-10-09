import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixHdistC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixHgeomC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointUniformC11G2

/-!
# uniform `ε₀`：eventPrefix 层 `hgeom` / `hrate` / K 层相对 `hdist`（S-CH11-P6PFX G5，`_C11G2`）

`ε₀`（`exists_hprot_window_C11G` 给的端点保护精度）**与半径参数 `ℓ₀` 无关**：`ℓ₀` 只进 `hscal` 的球半径与
输出半径 `ℓ = ℓ₀/√K`（`K` 只依赖 `hscal` 的常数 `C_{D,T}`），不进任何阈值。所以 `∃ ε₀, ∀ ℓ₀ ∈ (0,1]` 的
重排成立：本文件把 `…_radius_C11G2` / `…_pointwise_…` / eventPrefix 层定理的量词序改成
`∃ ε₀ > 0, ∀ ℓ₀, 0 < ℓ₀ → ℓ₀ ≤ 1 → …`（证明同原，只是 `ℓ₀` 移到 `ε₀` 之后；消费端 (α) 路线里 `ℓ₀` 随
`(D, T, K)` 变，要的正是这个形）。（`hdist` / `hrate` 型定理的 `ε₀ := min ε₀' (1/2)` 同样与 `ℓ₀` 无关。）
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **uniform `ε₀`（eventPrefix 层 `hgeom`）**：`∃ ε₀, ∀ ℓ₀ ∈ (0,1], …`。 -/
theorem exists_hgeom_eventPrefix_uniform_C11G2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ℓ₀ : ℝ), 0 < ℓ₀ → ℓ₀ ≤ 1 →
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ),
    let Hs : ℕ → ObservedHistory.{u} :=
      fun n => ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
    ∀ (Te : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (pe : ∀ n, ((Hs n).stageAt (Te n)).Carrier)
      (Tk : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (pk : ∀ n, ((K n).toHistory.stageAt (Tk n)).Carrier)
      (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ Te n)
      (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
        ((Hs n).activeStage (Te n)) ((Hs n).activeStage_mono (haT n)) (pe n))
      (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ Te n) (has : ∀ n, aSeed n ≤ s n)
      (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r : ℕ → ℝ), (∀ᶠ n in atTop, 0 < R n) →
      (∀ n, (Te n : ℝ) = Tk n) → (∀ n, HEq (pe n) (pk n)) →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tk n) (pk n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Te n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n)) →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
        (x : ((K n).toHistory.stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
          (a₀ + τ') x) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
            τ < s n →
          ∀ z : ((Hs n).stageAt (s n)).Carrier,
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ C * R n) ∧
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
            (s n : ℝ) - T / R n ≤ v →
          ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
            ((Hs n).activeStage_mono hvs) x,
          ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
            (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
          ∀ z : ((Hs n).stage e.castSucc).Carrier,
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
                (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n)) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (s n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          (riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          Real.sqrt (normSq0S ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z 4
            (metricRm04At ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z)) ≤ K * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (Te n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)), (v : ℝ) < (Hs n).time e.succ →
        ∀ (he : T₀ n ≤ (Hs n).time e.succ) b,
          (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
              ((recordsK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e) he).static
                b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
            tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
              ((recordsK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e) he).static
                b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (Te n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
          (riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          ricciTensor ((Hs n).stageMetric e.castSucc t') z ξ ξ ≤
            (3 / (ℓ / Real.sqrt (R n)) ^ 2) *
              ((Hs n).stageMetric e.castSucc t').inner z ξ ξ) := by
  obtain ⟨ε₀, hε₀, hA⟩ := exists_hgeom_of_K0_pinching_radius_uniform_C11G2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro ℓ₀ hℓ₀1 hℓ₀2 K j t hjt htj Hs Te pe Tk pk aSeed haT seedTrace s hst has y R r hR hTe hpe
    hsmallK hclock
    hX hwin hlate a₀ ha₀ hpinK hscal q T₀ recordsK hcanK hacc0 hm hDm hsepWK
  exact hA ℓ₀ hℓ₀1 hℓ₀2 Hs Te pe aSeed haT seedTrace s hst has y R r hR
    (fun n => (K n).hasSmallParabolicCurvature_eventPrefix_C11G2 (j n) (hjt n) (htj n) (Te n) (Tk n)
      (hTe n) (pe n) (pk n) (hpe n) (hsmallK n))
    hclock hX hwin hlate ha₀
    (fun n => (K n).inFixedHI_eventPrefix_C11G2 (j n) (hjt n) (htj n) (hpinK n)) hscal q T₀
    (fun n => (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n))
    (fun n => (K n).eventPrefixRecords_hcan_C11G2 (j n) (hjt n) (htj n) (recordsK n) (hcanK n))
    hacc0 hm hDm
    (fun C hC T hT => (hsepWK C hC T hT).mono fun n hn e he b hwe =>
      hn (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e) e.isLt he b hwe)

/-- **uniform `ε₀`（eventPrefix 层 `hrate`）**。 -/
theorem hrate_eventPrefix_uniform_C11G2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ℓ₀ : ℝ), 0 < ℓ₀ → ℓ₀ ≤ 1 →
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ),
    let Hs : ℕ → ObservedHistory.{u} :=
      fun n => ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
    ∀ (Te : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (pe : ∀ n, ((Hs n).stageAt (Te n)).Carrier)
      (Tk : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (pk : ∀ n, ((K n).toHistory.stageAt (Tk n)).Carrier)
      (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ Te n)
      (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
        ((Hs n).activeStage (Te n)) ((Hs n).activeStage_mono (haT n)) (pe n))
      (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ Te n) (has : ∀ n, aSeed n ≤ s n)
      (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r : ℕ → ℝ), (∀ᶠ n in atTop, 0 < R n) →
      (∀ n, (Te n : ℝ) = Tk n) → (∀ n, HEq (pe n) (pk n)) →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tk n) (pk n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Te n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n)) →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
        (x : ((K n).toHistory.stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
          (a₀ + τ') x) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
            τ < s n →
          ∀ z : ((Hs n).stageAt (s n)).Carrier,
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ C * R n) ∧
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
            (s n : ℝ) - T / R n ≤ v →
          ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
            ((Hs n).activeStage_mono hvs) x,
          ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
            (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
          ∀ z : ((Hs n).stage e.castSucc).Carrier,
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
                (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n)) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (s n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (s n : ℝ) - T / R n) →
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n ≤ τ → (Hs n).time ((Hs n).activeStage (s n)) ≤ τ →
          τ ≤ s n →
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
            ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
              ((Hs n).activeStage_mono (hst n))) x ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) x +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((s n : ℝ) - τ))) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (Te n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (τ : ℝ),
          (v : ℝ) ≤ τ → (Hs n).time e.castSucc ≤ τ → τ < (Hs n).time e.succ →
        riemannianEDistOf ((Hs n).stageMetric e.castSucc τ)
            ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
          riemannianEDistOf ((Hs n).stageMetric e.succ ((Hs n).time e.succ))
              ((seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
              (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((Hs n).time e.succ - τ))) := by
  obtain ⟨ε₀, hε₀, hA⟩ := exists_hgeom_eventPrefix_uniform_C11G2.{u}
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), ?_⟩
  intro ℓ₀ hℓ₀1 hℓ₀2 K j t hjt htj Hs Te pe Tk pk aSeed haT seedTrace s hst has y R r hR hTe hpe
    hsmallK hclock
    hX hwin hlate a₀ ha₀ hpinK hscal q T₀ recordsK hcanK hacc0 hm hDm hsepWK hT₀
  have hgeom := hA ℓ₀ hℓ₀1 hℓ₀2 K j t hjt htj Te pe Tk pk aSeed haT seedTrace s hst has y R r hR
    hTe hpe
    hsmallK hclock hX hwin hlate ha₀ hpinK hscal q T₀ recordsK hcanK
    (fun n => (hacc0 n).trans (min_le_left _ _)) hm hDm hsepWK
  exact hrate_of_endpoint_bounds_C11D Hs Te pe aSeed haT seedTrace s hst has y R hR q T₀
    (fun n => (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n))
    (fun n e he =>
      ((K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n) e he).old_eq_retained)
    (fun n => (K n).eventPrefixRecords_hcan_C11G2 (j n) (hjt n) (htj n) (recordsK n) (hcanK n))
    (fun n => (hacc0 n).trans (min_le_right _ _)) hDm hT₀ hgeom

/-- **uniform `ε₀`（K 层相对 `hdist`，逐点 `(D,T)`）**。 -/
theorem hdist_Kdata_pointwise_eventPrefix_uniform_C11G2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ℓ₀ : ℝ), 0 < ℓ₀ → ℓ₀ ≤ 1 →
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ),
    let Hs : ℕ → ObservedHistory.{u} :=
      fun n => ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (Te aE sE : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haTe : ∀ n, aE n ≤ Te n)
      (_hsTe : ∀ n, sE n ≤ Te n) (_hasE : ∀ n, aE n ≤ sE n)
      (pe : ∀ n, ((Hs n).stageAt (Te n)).Carrier) (yE : ∀ n, ((Hs n).stageAt (sE n)).Carrier)
      (seedE : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aE n))
        ((Hs n).activeStage (Te n)) ((Hs n).activeStage_mono (haTe n)) (pe n)),
      (∀ n, (sE n : ℝ) = σ n) → (∀ n, (aE n : ℝ) = aSeed n) → (∀ n, (Te n : ℝ) = Tn n) →
      (∀ n, HEq (yE n) (y n)) → (∀ n, HEq (pe n) (pT n)) →
      (∀ n (m : Fin ((Hs n).eventCount + 1)) (h1 : (Hs n).activeStage (aE n) ≤ m)
        (h2 : m ≤ (Hs n).activeStage (Te n))
        (h1' : (Kh n).activeStage (aSeed n) ≤ (K n).eIdx_C11G2 (j n) (hjt n) (htj n) m)
        (h2' : (K n).eIdx_C11G2 (j n) (hjt n) (htj n) m ≤ (Kh n).activeStage (Tn n)),
        (seedE n).point m h1 h2 =
          (seedTrace n).point ((K n).eIdx_C11G2 (j n) (hjt n) (htj n) m) h1' h2') →
      (∀ᶠ n in atTop, 0 < R n) → Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
    ∀ D T : ℝ, 0 < D → 0 < T →
      (∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (σ n : ℝ) - T / R n) →
      (∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n)) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (sE n)) (sE n)) (yE n)
            (D / Real.sqrt (R n)),
          ∀ τ : ℝ, (sE n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (sE n)) < τ →
            τ < sE n →
          ∀ z : ((Hs n).stageAt (sE n)).Carrier,
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (sE n)) τ) x z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (sE n)) τ) z ≤ C * R n) ∧
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (sE n)) (sE n)) (yE n)
            (D / Real.sqrt (R n)),
          ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aE n ≤ v) (hvs : v ≤ sE n),
            (sE n : ℝ) - T / R n ≤ v →
          ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (sE n))
            ((Hs n).activeStage_mono hvs) x,
          ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ (Hs n).activeStage (sE n)) (t' : ℝ),
            (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
          ∀ z : ((Hs n).stage e.castSucc).Carrier,
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
                (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n)) →
      (∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvs) x,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n))
                  ((Kh n).activeStage_mono (has n)) ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨ε₀, hε₀, hC⟩ := hdist_rel_pointwise_radius_uniform_C11G2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro ℓ₀ hℓ₀1 hℓ₀2 K j t hjt htj Hs Kh σ y R r L Tn aSeed haT hsT has pT seedTrace Te aE sE haTe
    hsTe hasE
    pe yE seedE hsE haE hTe hyE hpE hseed hR hL hsmallK hclockK hX a₀ ha₀ hpinK q T₀ recordsK hcanK
    hacc0 hm hDm D T hD hT hwin hlate hscal hsepWK hT₀
  have hdistE := hC ℓ₀ hℓ₀1 hℓ₀2 Hs Te pe aE haTe seedE sE hsTe hasE yE R r L hR hL
    (fun n => (K n).hasSmallParabolicCurvature_eventPrefix_C11G2 (j n) (hjt n) (htj n) (Te n)
      (Tn n) (hTe n) (pe n) (pT n) (hpE n) (hsmallK n))
    (fun n => by rw [haE n, hTe n]; exact hclockK n) hX ha₀
    (fun n => (K n).inFixedHI_eventPrefix_C11G2 (j n) (hjt n) (htj n) (hpinK n)) q T₀
    (fun n => (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n))
    (fun n => (K n).eventPrefixRecords_hcan_C11G2 (j n) (hjt n) (htj n) (recordsK n) (hcanK n))
    hacc0 hm hDm D T hD hT
    (hwin.mono fun n h => by rw [haE n, hsE n]; exact h)
    (hlate.mono fun n h => by rw [hsE n]; exact h) hscal
    (fun C hC' => (hsepWK C hC').mono fun n hn e he b hwe =>
      hn (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e) e.isLt he b
        (by rw [← hsE n]; exact hwe))
    (hT₀.mono fun n h => by rw [hsE n]; exact h)
  filter_upwards [hdistE] with n hn
  exact (K n).hdist_of_eventPrefix_C11G2 (j n) (hjt n) (htj n) (haT n) (hsT n) (has n)
    (seedTrace n) (haTe n) (hsTe n) (hasE n) (seedE n) (hsE n) (haE n) (hyE n) (hseed n) hn

/-- **uniform `ε₀`（K 层相对 `hdist`，全 `(D,T)`，P6M l.91 逐字形）**。 -/
theorem hdist_Kdata_eventPrefix_uniform_C11G2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ℓ₀ : ℝ), 0 < ℓ₀ → ℓ₀ ≤ 1 →
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ),
    let Hs : ℕ → ObservedHistory.{u} :=
      fun n => ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (Te aE sE : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haTe : ∀ n, aE n ≤ Te n)
      (_hsTe : ∀ n, sE n ≤ Te n) (_hasE : ∀ n, aE n ≤ sE n)
      (pe : ∀ n, ((Hs n).stageAt (Te n)).Carrier) (yE : ∀ n, ((Hs n).stageAt (sE n)).Carrier)
      (seedE : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aE n))
        ((Hs n).activeStage (Te n)) ((Hs n).activeStage_mono (haTe n)) (pe n)),
      (∀ n, (sE n : ℝ) = σ n) → (∀ n, (aE n : ℝ) = aSeed n) → (∀ n, (Te n : ℝ) = Tn n) →
      (∀ n, HEq (yE n) (y n)) → (∀ n, HEq (pe n) (pT n)) →
      (∀ n (m : Fin ((Hs n).eventCount + 1)) (h1 : (Hs n).activeStage (aE n) ≤ m)
        (h2 : m ≤ (Hs n).activeStage (Te n))
        (h1' : (Kh n).activeStage (aSeed n) ≤ (K n).eIdx_C11G2 (j n) (hjt n) (htj n) m)
        (h2' : (K n).eIdx_C11G2 (j n) (hjt n) (htj n) m ≤ (Kh n).activeStage (Tn n)),
        (seedE n).point m h1 h2 =
          (seedTrace n).point ((K n).eIdx_C11G2 (j n) (hjt n) (htj n) m) h1' h2') →
      (∀ᶠ n in atTop, 0 < R n) → Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (σ n : ℝ) - T / R n) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n)) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (sE n)) (sE n)) (yE n)
            (D / Real.sqrt (R n)),
          ∀ τ : ℝ, (sE n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (sE n)) < τ →
            τ < sE n →
          ∀ z : ((Hs n).stageAt (sE n)).Carrier,
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (sE n)) τ) x z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (sE n)) τ) z ≤ C * R n) ∧
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (sE n)) (sE n)) (yE n)
            (D / Real.sqrt (R n)),
          ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aE n ≤ v) (hvs : v ≤ sE n),
            (sE n : ℝ) - T / R n ≤ v →
          ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (sE n))
            ((Hs n).activeStage_mono hvs) x,
          ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ (Hs n).activeStage (sE n)) (t' : ℝ),
            (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
          ∀ z : ((Hs n).stage e.castSucc).Carrier,
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
                (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n)) →
      (∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
    ∀ D T : ℝ, 0 < D → 0 < T →
      ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvs) x,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n))
                  ((Kh n).activeStage_mono (has n)) ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨ε₀, hε₀, hB⟩ := hdist_Kdata_pointwise_eventPrefix_uniform_C11G2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro ℓ₀ hℓ₀1 hℓ₀2 K j t hjt htj Hs Kh σ y R r L Tn aSeed haT hsT has pT seedTrace Te aE sE haTe
    hsTe hasE
    pe yE seedE hsE haE hTe hyE hpE hseed hR hL hsmallK hclockK hX a₀ ha₀ hpinK q T₀ recordsK hcanK
    hacc0 hm hDm hwin hlate hscal hsepWK hT₀ D T hD hT
  exact hB ℓ₀ hℓ₀1 hℓ₀2 K j t hjt htj σ y R r L Tn aSeed haT hsT has pT seedTrace Te aE sE haTe
    hsTe hasE pe yE
    seedE hsE haE hTe hyE hpE hseed hR hL hsmallK hclockK hX ha₀ hpinK q T₀ recordsK hcanK hacc0 hm
    hDm D T hD hT (hwin T hT) (hlate T hT) (hscal D T hD hT) (fun C hC => hsepWK C hC T hT)
    (hT₀ T hT)

/-- **consumer**：uniform ⇒ 原（`ℓ₀` 在 `∃ ε₀` 之前）形，`type_of%` 对齐。 -/
example (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    type_of% (exists_hgeom_eventPrefix_C11G2.{u} ℓ₀ hℓ₀) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_hgeom_eventPrefix_uniform_C11G2.{u}
  exact ⟨ε₀, hε₀, h ℓ₀ hℓ₀.1 hℓ₀.2⟩

/-- **consumer**：uniform ⇒ 原（`ℓ₀` 在 `∃ ε₀` 之前）形，`type_of%` 对齐。 -/
example (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    type_of% (hrate_eventPrefix_C11G2.{u} ℓ₀ hℓ₀) := by
  obtain ⟨ε₀, hε₀, h⟩ := hrate_eventPrefix_uniform_C11G2.{u}
  exact ⟨ε₀, hε₀, h ℓ₀ hℓ₀.1 hℓ₀.2⟩

/-- **consumer**：uniform ⇒ 原（`ℓ₀` 在 `∃ ε₀` 之前）形，`type_of%` 对齐。 -/
example (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    type_of% (hdist_Kdata_pointwise_eventPrefix_C11G2.{u} ℓ₀ hℓ₀) := by
  obtain ⟨ε₀, hε₀, h⟩ := hdist_Kdata_pointwise_eventPrefix_uniform_C11G2.{u}
  exact ⟨ε₀, hε₀, h ℓ₀ hℓ₀.1 hℓ₀.2⟩

/-- **consumer**：uniform ⇒ 原（`ℓ₀` 在 `∃ ε₀` 之前）形，`type_of%` 对齐。 -/
example (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    type_of% (hdist_Kdata_eventPrefix_C11G2.{u} ℓ₀ hℓ₀) := by
  obtain ⟨ε₀, hε₀, h⟩ := hdist_Kdata_eventPrefix_uniform_C11G2.{u}
  exact ⟨ε₀, hε₀, h ℓ₀ hℓ₀.1 hℓ₀.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
