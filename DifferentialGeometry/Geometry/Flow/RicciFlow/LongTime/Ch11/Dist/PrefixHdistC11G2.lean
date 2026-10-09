import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixTransportC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointPointwiseC11G2

/-!
# P6 prefix transport G3：eventPrefix 层 `hgeom` / 相对 `hdist` ⇒ K 层 `hdist`（`_C11G2`）

`PrefixTransportC11G2`（G1/G2）把 K0 / pinching / late records 从 K 搬到 `E := K.eventPrefix j T`；
`EndpointRadiusC11G2` / `EndpointPointwiseC11G2`（G4/G4b）在任意 `Hs` 上给 `hgeom` / 相对 `hdist`。
本文件：

* **E → K 的距离 / 球 / 点搬运**（`edist_eventPrefix_C11G2`、`mem_ball_eventPrefix_C11G2`）：stage 指标
  `m' = eIdx mE` 下 `riemannianEDistOf (E.stageMetric mE v) a b
  = riemannianEDistOf (K.stageMetric m' v) a' b'`
  （`HEq` 点）。
* **逐 `n` 核心** `hdist_of_eventPrefix_C11G2`：E 层相对 `hdist`（`(D,T)`，`L`）⇒ K 层同形（P6M
  `false_of_selection_eventSlab_Kdata_P6M` l.91 `hdist` 的逐 `n` 内层；K 的 trace 经
  `exists_eventPrefixTrace_C11G2` 限制成 E 的 trace，种子 trace 由 `point` 逐点相等的关系 `hseed` 对齐）。
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

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- **E → K 的距离搬运（`_C11G2`）**：E 的 stage `mE`、K 的 stage `m'`（`m' = eIdx mE`），`HEq` 点。 -/
theorem edist_eventPrefix_C11G2 (j : Fin K.eventCount) {T : ℝ} (hjT : K.time j.castSucc < T)
    (hTj : T < K.time j.succ)
    {mE : Fin ((K.eventPrefix j T hjT hTj).toHistory.eventCount + 1)}
    {m' : Fin (K.eventCount + 1)} (hm : m' = K.eIdx_C11G2 j hjT hTj mE) (v : ℝ)
    {a b : ((K.eventPrefix j T hjT hTj).toHistory.stage mE).Carrier}
    {a' b' : (K.toHistory.stage m').Carrier} (ha : HEq a a') (hb : HEq b b') :
    riemannianEDistOf ((K.eventPrefix j T hjT hTj).toHistory.stageMetric mE v) a b =
      riemannianEDistOf (K.toHistory.stageMetric m' v) a' b' := by
  subst hm
  rw [eq_of_heq ha, eq_of_heq hb, K.eventPrefix_stageMetric j hjT hTj]
  rfl

/-- **K → E 的球成员搬运（`_C11G2`）**：K 的球成员（stage `m'`）⇒ E 的球成员（stage `mE`）。 -/
theorem mem_ball_eventPrefix_C11G2 (j : Fin K.eventCount) {T : ℝ} (hjT : K.time j.castSucc < T)
    (hTj : T < K.time j.succ)
    {mE : Fin ((K.eventPrefix j T hjT hTj).toHistory.eventCount + 1)}
    {m' : Fin (K.eventCount + 1)} (hm : m' = K.eIdx_C11G2 j hjT hTj mE) (v : ℝ)
    {y x : ((K.eventPrefix j T hjT hTj).toHistory.stage mE).Carrier}
    {y' x' : (K.toHistory.stage m').Carrier} (hy : HEq y y') (hx : HEq x x') {b : ℝ}
    (h : x' ∈ riemannianBallOf (K.toHistory.stageMetric m' v) y' b) :
    x ∈ riemannianBallOf ((K.eventPrefix j T hjT hTj).toHistory.stageMetric mE v) y b := by
  have h' : riemannianEDistOf (K.toHistory.stageMetric m' v) y' x' < ENNReal.ofReal b := h
  change riemannianEDistOf ((K.eventPrefix j T hjT hTj).toHistory.stageMetric mE v) y x <
    ENNReal.ofReal b
  rwa [K.edist_eventPrefix_C11G2 j hjT hTj hm v hy hx]

/-- trace 点在 stage 指标相等时 `HEq`。 -/
private theorem point_heq_idx_C11G2 {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {x : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle x)
    {m m' : Fin (H.eventCount + 1)} (hm : m = m') (h1 : first ≤ m) (h2 : m ≤ last)
    (h1' : first ≤ m') (h2' : m' ≤ last) : HEq (A.point m h1 h2) (A.point m' h1' h2') := by
  subst hm
  exact HEq.rfl

/-- **逐 `n` 核心（`_C11G2`）**：E 层相对 `hdist`（`(Dd, Tw)`，`Lq`，`Rr`）⇒ K 层同形（P6M
`false_of_selection_eventSlab_Kdata_P6M` l.91 `hdist` 的逐 `n` 内层；`Kh n = K.toHistory`，`σ`、`y`、
`aSeed`、`Tn`、`seedTrace` 为 K 层数据）。E 层数据（`sE aE Te pe yE seedE`）与 K 层数据的关系：实时刻相等
（`hs`、`ha`）、中心 `HEq`（`hy`）、种子 trace 逐点相等（`hseed`，stage 指标 `eIdx`）。K 的 trace 经
`exists_eventPrefixTrace_C11G2` 限制成 E 的 trace。 -/
theorem hdist_of_eventPrefix_C11G2 (j : Fin K.eventCount) {T : ℝ} (hjT : K.time j.castSucc < T)
    (hTj : T < K.time j.succ) :
    let E : ObservedHistory.{u} := (K.eventPrefix j T hjT hTj).toHistory
    ∀ {σ aSeed Tn : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
      (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
      (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
        (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
      {y : (K.toHistory.stageAt σ).Carrier}
      {sE aE Te : Icc (0 : ℝ) E.horizon} (haTe : aE ≤ Te) (hsTe : sE ≤ Te) (hasE : aE ≤ sE)
      {pe : (E.stageAt Te).Carrier}
      (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage Te)
        (E.activeStage_mono haTe) pe)
      {yE : (E.stageAt sE).Carrier},
      (sE : ℝ) = σ → (aE : ℝ) = aSeed → HEq yE y →
      (∀ (m : Fin (E.eventCount + 1)) (h1 : E.activeStage aE ≤ m) (h2 : m ≤ E.activeStage Te)
        (h1' : K.toHistory.activeStage aSeed ≤ K.eIdx_C11G2 j hjT hTj m)
        (h2' : K.eIdx_C11G2 j hjT hTj m ≤ K.toHistory.activeStage Tn),
        seedE.point m h1 h2 = seedTrace.point (K.eIdx_C11G2 j hjT hTj m) h1' h2') →
      ∀ {Dd Rr Tw Lq : ℝ},
      (∀ x ∈ riemannianBallOf (E.stageMetric (E.activeStage sE) sE) yE (Dd / Real.sqrt Rr),
        ∀ (v : Icc (0 : ℝ) E.horizon) (hav : aE ≤ v) (hvs : v ≤ sE), (sE : ℝ) - Tw / Rr ≤ v →
        ∀ tr : BackwardPointTrace E (E.activeStage v) (E.activeStage sE)
            (E.activeStage_mono hvs) x,
          riemannianEDistOf (E.stageMetric (E.activeStage v) v)
              (seedE.point (E.activeStage v) (E.activeStage_mono hav)
                (E.activeStage_mono (hvs.trans hsTe)))
              (tr.point (E.activeStage v) le_rfl (E.activeStage_mono hvs)) ≤
            riemannianEDistOf (E.stageMetric (E.activeStage sE) sE)
                (seedE.point (E.activeStage sE) (E.activeStage_mono hasE)
                  (E.activeStage_mono hsTe)) yE +
              ENNReal.ofReal (Lq / Real.sqrt Rr)) →
      ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
          (Dd / Real.sqrt Rr),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
        (σ : ℝ) - Tw / Rr ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (Lq / Real.sqrt Rr) := by
  intro E σ aSeed Tn haT hsT has pT seedTrace y sE aE Te haTe hsTe hasE pe seedE yE hs ha hy hseed
    Dd Rr Tw Lq hE x hx v hav hvs hwin tr
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  have hvT : (v : ℝ) ≤ T := by
    have h1 : (v : ℝ) ≤ σ := hvs
    have h2 : (sE : ℝ) ≤ T := sE.2.2
    rw [hs] at h2
    exact h1.trans h2
  let vE : Icc (0 : ℝ) E.horizon := ⟨v, v.2.1, hvT⟩
  have hAv := K.eventPrefix_activeStage_val j hjT hTj vE v rfl
  have hAs := K.eventPrefix_activeStage_val j hjT hTj sE σ hs
  have hvK : K.toHistory.activeStage v =
      K.eIdx_C11G2 j hjT hTj (E.activeStage vE) := Fin.ext hAv.symm
  have hsK : K.toHistory.activeStage σ =
      K.eIdx_C11G2 j hjT hTj (E.activeStage sE) := Fin.ext hAs.symm
  let xE : (E.stageAt sE).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hsK) x
  have hxx : HEq xE x := cast_heq _ _
  have hxE : xE ∈ riemannianBallOf (E.stageMetric (E.activeStage sE) sE) yE
      (Dd / Real.sqrt Rr) := by
    refine K.mem_ball_eventPrefix_C11G2 j hjT hTj hsK (sE : ℝ) hy hxx ?_
    rw [hs]
    exact hx
  have havE : aE ≤ vE := show (aE : ℝ) ≤ v by rw [ha]; exact hav
  have hvsE : vE ≤ sE := show (v : ℝ) ≤ sE by rw [hs]; exact hvs
  have hwinE : (sE : ℝ) - Tw / Rr ≤ vE := by
    rw [hs]
    exact hwin
  obtain ⟨trE, htrE⟩ := K.exists_eventPrefixTrace_C11G2 j hjT hTj hvK hsK
    (hle := E.activeStage_mono hvsE) (hle' := K.toHistory.activeStage_mono hvs) hxx tr
  have hEin := hE xE hxE vE havE hvsE hwinE trE
  have hM1 : K.toHistory.activeStage aSeed ≤ K.eIdx_C11G2 j hjT hTj (E.activeStage vE) :=
    (K.toHistory.activeStage_mono hav).trans hvK.le
  have hM2 : K.eIdx_C11G2 j hjT hTj (E.activeStage vE) ≤ K.toHistory.activeStage Tn :=
    hvK.symm.le.trans (K.toHistory.activeStage_mono (hvs.trans hsT))
  have hseed1 := hseed (E.activeStage vE) (E.activeStage_mono havE)
    (E.activeStage_mono (hvsE.trans hsTe)) hM1 hM2
  have htr1 := htrE (E.activeStage vE) le_rfl (E.activeStage_mono hvsE) hvK.le
    (hvK.symm.le.trans (K.toHistory.activeStage_mono hvs))
  have hseedP : HEq (seedE.point (E.activeStage vE) (E.activeStage_mono havE)
      (E.activeStage_mono (hvsE.trans hsTe)))
      (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
        (K.toHistory.activeStage_mono (hvs.trans hsT))) :=
    (heq_of_eq hseed1).trans (point_heq_idx_C11G2 seedTrace hvK.symm _ _ _ _)
  have htrP : HEq (trE.point (E.activeStage vE) le_rfl (E.activeStage_mono hvsE))
      (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) :=
    (heq_of_eq htr1).trans (point_heq_idx_C11G2 tr hvK.symm _ _ _ _)
  have hL1 := K.edist_eventPrefix_C11G2 j hjT hTj hvK (v : ℝ) hseedP htrP
  have hN1 : K.toHistory.activeStage aSeed ≤ K.eIdx_C11G2 j hjT hTj (E.activeStage sE) :=
    (K.toHistory.activeStage_mono has).trans hsK.le
  have hN2 : K.eIdx_C11G2 j hjT hTj (E.activeStage sE) ≤ K.toHistory.activeStage Tn :=
    hsK.symm.le.trans (K.toHistory.activeStage_mono hsT)
  have hseed2 := hseed (E.activeStage sE) (E.activeStage_mono hasE) (E.activeStage_mono hsTe)
    hN1 hN2
  have hseedS : HEq (seedE.point (E.activeStage sE) (E.activeStage_mono hasE)
      (E.activeStage_mono hsTe))
      (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
        (K.toHistory.activeStage_mono hsT)) :=
    (heq_of_eq hseed2).trans (point_heq_idx_C11G2 seedTrace hsK.symm _ _ _ _)
  have hR1 := K.edist_eventPrefix_C11G2 j hjT hTj hsK (sE : ℝ) hseedS hy
  rw [hs] at hR1 hEin
  calc _ = _ := hL1.symm
    _ ≤ _ := hEin
    _ = _ := by rw [hR1]

end RetainedCoreHistory

/-- **G3：K 层相对 `hdist`（逐点 `(D,T)`，`_C11G2`）**：`hdist_rel_pointwise_radius_C11G2` 在
`Hs := K.eventPrefix` 上（K0 / pinching / late records / scale 分离取 K 层）⇒ P6M
`false_of_selection_eventSlab_Kdata_P6M` l.91 `hdist` 的**逐字内层**（`Kh n = (K n).toHistory`，K 层
`σ y R L aSeed Tn seedTrace`；`(D,T)` 给定）。E 层数据（`Te aE sE pe yE seedE`）是自由变量，经实时刻相等 /
`HEq` / 种子 trace 逐点相等（`hseed`，stage 指标 `eIdx`）与 K 层数据对应；`hscal`（E 层 trace，半径 `ℓ₀/√R`）
逐字。**需要 `Tn n ≤ t n`（隐含在 `Te n : Icc 0 (Hs n).horizon`、`(Te n : ℝ) = Tn n`）**，即 K0 种子时刻
在 prefix 的 horizon `t n` 之内（K-route：`Tn = σ = t`）。 -/
theorem hdist_Kdata_pointwise_eventPrefix_C11G2 (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
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
  obtain ⟨ε₀, hε₀, hC⟩ := hdist_rel_pointwise_radius_C11G2.{u} ℓ₀ hℓ₀
  refine ⟨ε₀, hε₀, ?_⟩
  intro K j t hjt htj Hs Kh σ y R r L Tn aSeed haT hsT has pT seedTrace Te aE sE haTe hsTe hasE
    pe yE seedE hsE haE hTe hyE hpE hseed hR hL hsmallK hclockK hX a₀ ha₀ hpinK q T₀ recordsK hcanK
    hacc0 hm hDm D T hD hT hwin hlate hscal hsepWK hT₀
  have hdistE := hC Hs Te pe aE haTe seedE sE hsTe hasE yE R r L hR hL
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

/-- **G3：K 层相对 `hdist`（全 `(D,T)` 形，`_C11G2`）**：`hdist_Kdata_pointwise_eventPrefix_C11G2` 逐 `(D,T)`
展开；结论 `∀ D T, 0<D → 0<T → ∀ᶠ n, …` 是 P6M `false_of_selection_eventSlab_Kdata_P6M` l.91 `hdist`
的逐字形（`Kh n = (K n).toHistory`，`let`）。 -/
theorem hdist_Kdata_eventPrefix_C11G2 (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
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
  obtain ⟨ε₀, hε₀, hB⟩ := hdist_Kdata_pointwise_eventPrefix_C11G2.{u} ℓ₀ hℓ₀
  refine ⟨ε₀, hε₀, ?_⟩
  intro K j t hjt htj Hs Kh σ y R r L Tn aSeed haT hsT has pT seedTrace Te aE sE haTe hsTe hasE
    pe yE seedE hsE haE hTe hyE hpE hseed hR hL hsmallK hclockK hX a₀ ha₀ hpinK q T₀ recordsK hcanK
    hacc0 hm hDm hwin hlate hscal hsepWK hT₀ D T hD hT
  exact hB K j t hjt htj σ y R r L Tn aSeed haT hsT has pT seedTrace Te aE sE haTe hsTe hasE pe yE
    seedE hsE haE hTe hyE hpE hseed hR hL hsmallK hclockK hX ha₀ hpinK q T₀ recordsK hcanK hacc0 hm
    hDm D T hD hT (hwin T hT) (hlate T hT) (hscal D T hD hT) (fun C hC => hsepWK C hC T hT)
    (hT₀ T hT)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
