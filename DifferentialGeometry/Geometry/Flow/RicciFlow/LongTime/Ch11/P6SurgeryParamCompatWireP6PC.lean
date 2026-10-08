import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurgeryParamCompatP6PC

/-!
# 参数相容性的接线（O-CH11-PARAMCOMPAT，后缀 `_P6PC`）

由 build-logs/scratch/O-CH11-PARAMCOMPAT/gen.py 从源文本生成（断言只换指定槽）。

* G1 consumer `exists_crossSlab_ceiling_paramCompat_P6PC`：
  `exists_crossSlab_ceiling_windowNeck_P6HS` 的陈述，
  只把合同 `WindowNeckScaleBudget_P6HS` 槽换成 `SurgeryParamCompat_P6PC q θ` + `0 ≤ θ` + `Tn ≤ θ·a` + Tn 行
  `R ≤ ρ(Tn)⁻²`，窗口 δ 小由 `8·Q_b·δ⁴ ≤ 1` 改成 `8·Q_b·δ² ≤ 1`；结论逐字。证明直接喂
  `exists_crossSlab_ceiling_CXJD` 的 `hscale` 槽（`hscale_of_paramCompat_P6PC`，
  同一 `records`、同一 `ε₀`）。
* G3 consumer `exists_crossSlab_ceiling_noStep_P6PC`：零步形（antitone + 窗内 `ρ` 常值 + Tn 行）经
  `windowNeckScaleBudget_of_noStep_P6PC` 产出 HSCALE 合同逐字，
  喂 `exists_crossSlab_ceiling_windowNeck_P6HS`。
* G2 `hOpen8B_of_paramCompat_P6PC`：hOpen8 合同形 `hOpen8B`（J7BIRTH）中 `CapBirthBudget_P6J7` 合取换成
  `CapBirthParamCompat_P6PC`（同一 `∀ p recordsK`）⇒ `hOpen8B` 逐字；G2 consumer
  `hgapJ8_of_paramCompat_P6PC` 喂 `hgapJ8_of_capBirthBudget_P6J7`（前提 = 其前提逐字，只换 hOpen8 位；
  结论逐字）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6)

namespace ObservedHistory

/-- **G1 consumer（PROVISIONAL[`SurgeryParamCompat_P6PC`]）**：
`exists_crossSlab_ceiling_windowNeck_P6HS` 的陈述，HSCALE 合同槽换成参数相容性 + Tn 行 + 窗口比
（δ-弱化预算路线，绕过 HSCALE 逐字形，不改 CXJD 槽形）；`hscale` 由 `hscale_of_paramCompat_P6PC`
以同一 `records` 产出，喂 `exists_crossSlab_ceiling_CXJD`（同一 `ε₀`）。 -/
theorem exists_crossSlab_ceiling_paramCompat_P6PC :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T K ℓ D : ℝ} (_ : 0 ≤ C2')
    (H : ObservedHistory.{u}) {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (_ : 0 < R)
    (_ : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb) (_ : 2 * Ctime' * Qb * T ≤ 1) (_ : aSeed ≤ a)
    (haσ : a ≤ σ) (_ : H.activeStage σ < Fin.last H.eventCount)
    (_ : (σ : ℝ) - L ^ 2 / R ≤ a) (_ : (σ : ℝ) - a ≤ T / R) (_ : 1 ≤ R * a)
    {z : (H.stageAt σ).Carrier}
    (_ : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (_ : 0 < ℓ) (_ : K * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ θ : ℝ} (_ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (_ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    (_ : SurgeryParamCompat_P6PC q θ) (_ : 0 ≤ θ) (_ : (Tn : ℝ) ≤ θ * (a : ℝ))
    (_ : R ≤ (q.neckRadius (Tn : ℝ) ^ 2)⁻¹)
    (_ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → (a : ℝ) < H.time e.succ →
      q.recenterConstant * q.delta (H.time e.succ) ≤ 1 / 2 ∧
        8 * Qb * q.delta (H.time e.succ) ^ 2 ≤ 1)
    (_ : 3 / r ^ 2 ≤ 2 * (Qb * R))
    (_ : z ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R))
    (_ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hσT)) y ≠ ⊤)
    (_ : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
        metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          2 * (Qb * R) := by
  obtain ⟨ε₀, hε₀, hB⟩ := exists_crossSlab_ceiling_CXJD.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ D hC2 H Tn aSeed a σ haT pT r hsmall hclock seedTrace
    a₀ ha₀ hpin hσT has y R L hR hgood hQb hstep haS haσ hσlast haL hdepth hRa z hz A hℓ hKℓ hℓr hKr
    hKC hℓρ hρL q T₀ θ hT₀ records hOld hcan hDm hacc hm hpc hθ hwin hTn hδw h3r hzy hdσ hnum
  exact hB hC2 H haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR hgood hQb hstep haS haσ hσlast
    haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records hOld hcan hDm hacc hm
    (hscale_of_paramCompat_P6PC records hpc hθ Tn.2.1 hwin hTn hδw h3r
      ((zero_le_one.trans (le_max_right _ _)).trans hQb)) hzy hdσ hnum

/-- **G3 consumer（零步特例，PROVED 于零步前提）**：`exists_crossSlab_ceiling_windowNeck_P6HS` 的陈述，HSCALE
合同槽换成零步形（`ρ` antitone + 窗口 `(a, Tn]` 内 `ρ` 常值 + Tn 行）；合同由
`windowNeckScaleBudget_of_noStep_P6PC` 逐字产出后喂 `exists_crossSlab_ceiling_windowNeck_P6HS`
（同一 `ε₀`）。 -/
theorem exists_crossSlab_ceiling_noStep_P6PC :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T K ℓ D : ℝ} (_ : 0 ≤ C2')
    (H : ObservedHistory.{u}) {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (_ : 0 < R)
    (_ : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb) (_ : 2 * Ctime' * Qb * T ≤ 1) (_ : aSeed ≤ a)
    (haσ : a ≤ σ) (_ : H.activeStage σ < Fin.last H.eventCount)
    (_ : (σ : ℝ) - L ^ 2 / R ≤ a) (_ : (σ : ℝ) - a ≤ T / R) (_ : 1 ≤ R * a)
    {z : (H.stageAt σ).Carrier}
    (_ : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (_ : 0 < ℓ) (_ : K * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (_ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (_ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    (_ : AntitoneOn q.neckRadius (Ici 0))
    (_ : ∀ τ : ℝ, (a : ℝ) < τ → τ ≤ (Tn : ℝ) → q.neckRadius τ = q.neckRadius (Tn : ℝ))
    (_ : R ≤ (q.neckRadius (Tn : ℝ) ^ 2)⁻¹)
    (_ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → (a : ℝ) < H.time e.succ →
      q.recenterConstant * q.delta (H.time e.succ) ≤ 1 / 2 ∧
        8 * Qb * q.delta (H.time e.succ) ^ 4 ≤ 1)
    (_ : 3 / r ^ 2 ≤ 2 * (Qb * R))
    (_ : z ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R))
    (_ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hσT)) y ≠ ⊤)
    (_ : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
        metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          2 * (Qb * R) := by
  obtain ⟨ε₀, hε₀, hB⟩ := exists_crossSlab_ceiling_windowNeck_P6HS.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ D hC2 H Tn aSeed a σ haT pT r hsmall hclock seedTrace
    a₀ ha₀ hpin hσT has y R L hR hgood hQb hstep haS haσ hσlast haL hdepth hRa z hz A hℓ hKℓ hℓr hKr
    hKC hℓρ hρL q T₀ hT₀ records hOld hcan hDm hacc hm hanti hflat hTn hδw h3r hzy hdσ hnum
  exact hB hC2 H haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR hgood hQb hstep haS haσ hσlast
    haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records hOld hcan hDm hacc hm
    (windowNeckScaleBudget_of_noStep_P6PC hanti Tn.2.1 hflat hTn) hδw h3r hzy hdσ hnum

/-- **G2 适配（PROVISIONAL[`CapBirthParamCompat_P6PC`]）**：J7BIRTH 合同形 `hOpen8B` 中 `CapBirthBudget_P6J7`
合取换成 J7 参数合同 `CapBirthParamCompat_P6PC`（同一 `∀ p recordsK`）⇒ `hOpen8B` **逐字**（gen.py 从
`P6CapBirthP6J7.lean` 源文本生成并断言）。合同 = `capBirthBudget_of_paramCompat_J7b_P6PC`
（J7b 给 `0 ≤ Cb·scale`）。 -/
theorem hOpen8B_of_paramCompat_P6PC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ)
    {pBase : CutoffParameters} {Cc : GC.GeneralFlow.ClosedBirthConstants}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase Cc P g) {Ctime₀ : ℝ≥0} {a₀ : ℝ}
    {T₀ Qt : ℕ → ℝ}
    (hOpen8C : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon
        (∀ n, c n * Qs n < R n) ∧
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ → q.delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) →
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) →
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) →
          (∀ n i hi b, max (0 : ℝ) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          CapBirthParamCompat_P6PC p (fun n => max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)))
            Qs (fun n => Cb Ctime₀ n)) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w)) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon
        (∀ n, c n * Qs n < R n) ∧
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ → q.delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) →
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) →
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) →
          (∀ n i hi b, max (0 : ℝ) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          CapBirthBudget_P6J7 Ho (fun n => max (T₀ n) (c n * ((σ n : ℝ) - L n / R n))) p
            recordsK Qs (fun n => Cb Ctime₀ n)) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w) := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt Qs
  obtain ⟨hJ10, hK, hJ14, hJ16⟩ := hOpen8C A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT
    hclock h1 hsm hlate seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt
    hradii hRρ hroom hball hdistσ hev hlt
  refine ⟨hJ10, fun p recordsK hcan hδ hacc hrad hord hJ7b hJ8 => ?_, hJ14, hJ16⟩
  obtain ⟨hJ6, hpc⟩ := hK p recordsK hcan hδ hacc hrad hord hJ7b hJ8
  exact ⟨hJ6, capBirthBudget_of_paramCompat_J7b_P6PC hpc hJ7b⟩

/-- **G2 consumer（PROVISIONAL[`CapBirthParamCompat_P6PC`]）**：喂 `hgapJ8_of_capBirthBudget_P6J7`。
前提 = 其前提逐字，只把 `hOpen8B` 换成参数形 `hOpen8C`；结论逐字。WR2 证明体只在 KNOM `choose_spec` 的那一个 records
witness 上用 hOpen8 第二合取，所以 J6 / J7b / 参数合同落在同一 witness 上。 -/
theorem hgapJ8_of_paramCompat_P6PC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ)
    (hCb : ∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n ∧ Cb C n ≤ 1 / ((n : ℝ) + 1) ^ 2)
    (hζ : ∀ (C : ℝ≥0) (n : ℕ), 0 < ζ C n) (hδ₀ : ∀ (C : ℝ≥0) (n : ℕ), 0 < δ₀ C n)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ rs : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((rs i hi).static b)) ∧
      ∀ i hi, (rs i hi).nominalRadius = (records k i).nominalRadius ∧
        (rs i hi).delta = (records k i).delta ∧
        (rs i hi).order = (records k i).order ∧
        (∀ α, HEq ((rs i hi).neck α) ((records k i).neck α)) ∧
        (∀ b, ((rs i hi).static b).neck.scale = ((records k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((rs i hi).static b).inclusion (((rs i hi).static b).witness.cap z) =
            ((records k i).static b).inclusion (((records k i).static b).witness.cap z))
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    {pBase : CutoffParameters} {Cc : GC.GeneralFlow.ClosedBirthConstants}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase Cc P g) (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, GC.GeneralFlow.PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (hTower : F.tower = S.tower) {Ctime₀ : ℝ≥0} (hC₀ : Ctime₀ = Cc.Ctime)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    {T₀ Qt : ℕ → ℝ}
    (hT₀ : ∀ n, lateThrJ8_P6WR2 (fun n => Cb Ctime₀ n) (fun n => Rn Ctime₀ n)
      (fun n => ζ Ctime₀ n) (fun n => δ₀ Ctime₀ n) (fun n => m₀ Ctime₀ n) a₀ records hP5L hδq
      hanti n ≤ T₀ n)
    (hJ11 : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ → q.delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) →
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) →
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) →
          (∀ n i hi b, max (0 : ℝ) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) →
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) →
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
            ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
        ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
          (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
          (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
            B / (R n / c n) ≤ v →
        ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).toHistory.activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Ho n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt))
            (ϱ / Real.sqrt (R n / c n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
              ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
              (tr.point ((Ho n).toHistory.activeStage v) le_rfl
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ)))
    (hJ15 : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ → q.delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) →
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) →
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) →
          (∀ n i hi b, max (0 : ℝ) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) →
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) →
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)))))
    (hOpen8C : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon
        (∀ n, c n * Qs n < R n) ∧
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ → q.delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) →
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) →
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) →
          (∀ n i hi b, max (0 : ℝ) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          CapBirthParamCompat_P6PC p (fun n => max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)))
            Qs (fun n => Cb Ctime₀ n)) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w)) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (p pF : ℕ → CutoffParameters) (Qs : ℕ → ℝ)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n))
          (a₀ : ℝ),
          Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
          0 < a₀ ∧
          (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) a₀ x ∧
            -3 / a₀ ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ →
            (pF n).delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) ∧
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) ∧
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) ∧
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b, max (Qs n) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qs n) (Fin.last (Ho n).eventCount)) ∧
          (∀ n, c n * Qs n < R n) ∧
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
            ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
        ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
          (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
          (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
            B / (R n / c n) ≤ v →
        ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).toHistory.activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Ho n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt))
            (ϱ / Real.sqrt (R n / c n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
              ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
              (tr.point ((Ho n).toHistory.activeStage v) le_rfl
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ) ∧
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) ∧
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w) :=
  hgapJ8_of_capBirthBudget_P6J7 Cb Rn ζ δ₀ m₀ hCb hζ hδ₀ hanti hδq records hP5L hrcs S εcut Dcut
    mcut W hshift hoffset hTower hC₀ ha₀ hHI hT₀ hJ11 hJ15
    (hOpen8B_of_paramCompat_P6PC Cb Rn ζ δ₀ m₀ S hOpen8C)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
