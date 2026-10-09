import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosureFinalSlabEndP6M

/-!
# P6 收口主形（final-slab 情形）：数据前提改为 **K 层**（S-CH11-P6BND G1，后缀 `_P6S`）

`false_of_selection_finalSlab_main_P6M`（O-CH11-P6ANCH G3g）的数据前提在 prefix
`(K n).prefixAt (Fin.last _)` 上；本文件照 G4c `false_of_selection_eventSlab_Kdata_P6M`
（`P6ClosureKDataP6M`）把它们换成 K 层（tower history 自身）的同名前提，经树内
`RetainedCoreHistoryPrefixTransport`（`k := Fin.last _`）：
* `records n := (K n).prefixRecords (Fin.last _) (recordsK n)`，`hrec` ⇐
  `isCanonicalCutoffRecordFamily_prefixAt`，`hscale` 逐点（prefix record 的 `static` 定义等）；
* `hpinch` ⇐ `eventSlabsPinched_prefixAt`（事件 slab）+ 单列的 final slab pinching `hpinchF`；
* `hslab` ⇐ `eventSlabsDerivative_prefixAt`（`k = Fin.last _`，事件 slab）；final slab 的导数界
  `hderG` 在 K 层没有对应前提（`EventSlabsDerivative` 只管 event slab）⇒ **保持原形**；
* `hnot` ⇐ 本文件新引理 `capWindowPoint_of_prefixAt_P6S`（树内 `capWindowPoint_of_prefixAt` 只给
  `j.castSucc` 位，这里对任意 `k : Fin (eventCount + 1)`，同证明）。
`hinit`（prefix 的 initial identification）、`hderG` / `hqR` / `hRt`（final slab 的 incoming 形）保持原形。
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

namespace RetainedCoreHistory

/-- `capWindowPoint_of_prefixAt` 的任意 prefix 位版本（`k : Fin (eventCount + 1)`，final-slab 用
`k = Fin.last _`）：prefix `H.prefixAt k` 的末 stage 上的 `CapWindowPoint` ⇒ `H` 在 stage `k` 上的
`CapWindowPoint`（trace 由 `backwardPointTraceOfPrefix` 搬回，事件指标 `Fin.castLE`）。 -/
theorem capWindowPoint_of_prefixAt_P6S (H : RetainedCoreHistory.{u}) (k : Fin (H.eventCount + 1))
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    {y : (H.stage k).Carrier} {t D θ : ℝ}
    (h : (H.prefixAt k).CapWindowPoint (H.prefixRecords k records) (Fin.last _) y t D θ) :
    H.CapWindowPoint records k y t D θ := by
  obtain ⟨i, hl, A, b, x, h1, h2, h3⟩ := h
  exact ⟨Fin.castLE (Nat.le_of_lt_succ k.isLt) i, Fin.le_def.mpr (Fin.le_def.mp hl),
    H.backwardPointTraceOfPrefix k A, b, x, h1, h2, h3⟩

end RetainedCoreHistory

namespace ObservedHistory

/-- **P6 收口主形（final-slab 情形），K 层数据前提**（records / canonical family / scale /
event-slab pinching / event-slab 导数 / `¬ CapWindowPoint` 都在 tower history `K n` 上；
final slab 的 `hpinchF` / `hderG` / `hqR` / `hRt` 保持 final-slab incoming 形）。 -/
theorem false_of_selection_finalSlab_Kdata_P6S :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
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
      {recordsK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀
        ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory)) →
      (hrecK : ∀ n, (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (recordsK n)) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscaleK : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((recordsK n i).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi) →
      (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon) phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnotK : ∀ n, ¬ (K n).CapWindowPoint (recordsK n) (Fin.last (K n).eventCount) (yG n) (t n)
        (D n) (θcap n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) * t n) atTop atTop) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ : ℝ} → (hr₀ : 0 < r₀) → (hRpos : ∀ n, 0 < R n) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) →
      (hctrl : ∀ᶠ n in atTop,
        (Kh n).isParabolicallyRmControlledBall (σ n) (y n) (r₀ / Real.sqrt (R n))) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hslice : ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
        Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁,
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          ∃ CWP : ((Kh n).stage ((Kh n).activeStage v)).Carrier → Prop,
            (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
                (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
                ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
              R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w → ∀ x,
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v) w x <
                ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                  Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) x ≤
                QB * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w) ∧
            (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
                (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
                ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
              ∃ (Ξ : standardCapWindow D₂ → ((Kh n).stage ((Kh n).activeStage v)).Carrier)
                (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
                Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
                ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                  τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                  ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                    metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                        ((Kh n).stageMetric ((Kh n).activeStage v) v)) Ξ hΞ)
                      ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                      (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW, hB⟩ :=
    false_of_selection_finalSlab_main_P6M.{u}
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW,
    fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro P₀ g₀ Ctime phi hphi K t htl htK G hG D θcap qcan p₀ p δb ρb recordsK yG hinit hrecK hqcan
    hpar hscaleK hθcap hpinchK0 hpinchF hslabK hderG hqR hnotK hRt Kh hKh σ y R hσ hyG hRn r₀ hr₀
    hRpos d hctrl Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hdist hslice hsel
  exact hB' hC1 hC2 hCt hphi htl htK hG
    (records := fun n => (K n).prefixRecords (Fin.last (K n).eventCount) (recordsK n)) hinit
    (fun n => (K n).isCanonicalCutoffRecordFamily_prefixAt _ (hrecK n)) hqcan hpar
    (fun n i b => hscaleK n _ b) hθcap
    (fun n => ⟨(K n).eventSlabsPinched_prefixAt _ (hpinchK0 n), hpinchF n⟩)
    (fun n => (K n).eventSlabsDerivative_prefixAt _ (hslabK n)) hderG hqR
    (fun n h => hnotK n ((K n).capWindowPoint_of_prefixAt_P6S _ (recordsK n) h)) hRt Kh hKh σ y R
    hσ hyG hRn hr₀ hRpos d hctrl Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hdist hslice hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
