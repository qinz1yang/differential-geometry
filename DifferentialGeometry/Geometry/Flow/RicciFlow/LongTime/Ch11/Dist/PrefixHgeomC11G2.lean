import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixTransportC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointRadiusC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.DistanceAssemblyC11D

/-!
# P6 prefix transport G3：eventPrefix 层 `hgeom`（S-CH11-P6PFX，后缀 `_C11G2`）

`exists_hgeom_eventPrefix_C11G2 ℓ₀ hℓ₀`：P6GEO `exists_hgeom_of_K0_pinching_C11G` 的半径参数化变体
（G4）在 `Hs n := ((K n).eventPrefix (j n) (t n) _ _).toHistory` 上，前提里 K0 / pinching / late
records / scale 分离取 K 层（`PrefixTransportC11G2` 的 G1 / G2 搬运），其余（`hscal` 等）逐字。
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

/-- **G3：`hgeom` 在 `K.eventPrefix` 上（`_C11G2`）**：`exists_hgeom_of_K0_pinching_radius_C11G2` 在
`Hs n := ((K n).eventPrefix (j n) (t n) _ _).toHistory`（`let`）上实例化；K0 / pinching / late records
取 **K 层**（G1/G2 搬运），`records` 的 `static` 与 K 层 `recordsK` 逐点 `rfl`（结论 (ii) 直接写
`recordsK n (castLE e)`）；scale 分离只对 `i.val < j n` 的事件（E 的事件）要求；`hscal`（E 层
trace，半径 `ℓ₀/√R`）、`hwin` / `hlate` 逐字不变。`Tk n`、`pk n` 是 K0 的 K 层种子（`(Te n : ℝ) = Tk n`、
`HEq`）。 -/
theorem exists_hgeom_eventPrefix_C11G2 (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
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
  obtain ⟨ε₀, hε₀, hA⟩ := exists_hgeom_of_K0_pinching_radius_C11G2.{u} ℓ₀ hℓ₀
  refine ⟨ε₀, hε₀, ?_⟩
  intro K j t hjt htj Hs Te pe Tk pk aSeed haT seedTrace s hst has y R r hR hTe hpe hsmallK hclock
    hX hwin hlate a₀ ha₀ hpinK hscal q T₀ recordsK hcanK hacc0 hm hDm hsepWK
  exact hA Hs Te pe aSeed haT seedTrace s hst has y R r hR
    (fun n => (K n).hasSmallParabolicCurvature_eventPrefix_C11G2 (j n) (hjt n) (htj n) (Te n) (Tk n)
      (hTe n) (pe n) (pk n) (hpe n) (hsmallK n))
    hclock hX hwin hlate ha₀
    (fun n => (K n).inFixedHI_eventPrefix_C11G2 (j n) (hjt n) (htj n) (hpinK n)) hscal q T₀
    (fun n => (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n))
    (fun n => (K n).eventPrefixRecords_hcan_C11G2 (j n) (hjt n) (htj n) (recordsK n) (hcanK n))
    hacc0 hm hDm
    (fun C hC T hT => (hsepWK C hC T hT).mono fun n hn e he b hwe =>
      hn (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e) e.isLt he b hwe)

/-- **G3 consumer：`hrate` 在 `K.eventPrefix` 上（`_C11G2`）**：`exists_hgeom_eventPrefix_C11G2` ⇒ DIST
`hrate_of_endpoint_bounds_C11D`（`Hs n := ((K n).eventPrefix …).toHistory`，records 取 K 层的搬运；
`hOld` 用 record 字段 `old_eq_retained`，`hacc : ≤ 1/2` 由 `ε₀ := min ε₀' (1/2)`）。 -/
theorem hrate_eventPrefix_C11G2 (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
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
  obtain ⟨ε₀, hε₀, hA⟩ := exists_hgeom_eventPrefix_C11G2.{u} ℓ₀ hℓ₀
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), ?_⟩
  intro K j t hjt htj Hs Te pe Tk pk aSeed haT seedTrace s hst has y R r hR hTe hpe hsmallK hclock
    hX hwin hlate a₀ ha₀ hpinK hscal q T₀ recordsK hcanK hacc0 hm hDm hsepWK hT₀
  have hgeom := hA K j t hjt htj Te pe Tk pk aSeed haT seedTrace s hst has y R r hR hTe hpe
    hsmallK hclock hX hwin hlate ha₀ hpinK hscal q T₀ recordsK hcanK
    (fun n => (hacc0 n).trans (min_le_left _ _)) hm hDm hsepWK
  exact hrate_of_endpoint_bounds_C11D Hs Te pe aSeed haT seedTrace s hst has y R hR q T₀
    (fun n => (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n))
    (fun n e he =>
      ((K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n) e he).old_eq_retained)
    (fun n => (K n).eventPrefixRecords_hcan_C11G2 (j n) (hjt n) (htj n) (recordsK n) (hcanK n))
    (fun n => (hacc0 n).trans (min_le_right _ _)) hDm hT₀ hgeom

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
