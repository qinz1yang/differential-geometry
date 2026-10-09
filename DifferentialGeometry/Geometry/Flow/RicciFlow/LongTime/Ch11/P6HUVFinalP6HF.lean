import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HUVGlobalCgP6S3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SliceDichotomyFinalP6HF

/-!
# final slab 的 U 侧（witness / 梯度 / 区域 κ）⇐ selection 数据（O-CH11-HCLOSEF G3a，后缀 `_P6HF`）

`Local/HUVSlabGoodCg_P6LS3`、`Local/HUVKappaClosure_P6L3`、`P6HUVGlobalCgP6S3` 的 final slab 孪生。
final 情形 `σ` 在 final slab 内，切片 `v ∈ (time last, σ]` 的 U 侧数据需要 final slab 上的 seed closure 与区域 κ：
**`hclosGF`**（`hclosG` 的 final 实例，DF-1 同性质）与 **`hκRF`**（`hκR` 的 final 实例，KAPPA3 D-8 同性质）——
二者不能由 HREST `hcloseF` 的其余 binder 推出（`hκR` / `hclosG` 只量化 event slab），是 `hcloseF⁺` 新增的两条 binder。
witness / 梯度仍由 `hgood` 给（`activeStage τ = last` ⇐ `time last < τ`）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- seed 三角不等式（任意度量版，`seed_triangle_P6L3` 的度量泛化）。 -/
theorem seed_triangle_metric_P6HF {P : OrientedThreeStage.{u}} (g : P.Metric)
    (O w x : P.Carrier) (dσ : ℝ≥0∞) {L Rad R Rw : ℝ} (hR : 0 < R)
    (hRw : R ≤ Rw) (hL0 : 0 ≤ L) (hRad : 2 * max Rad 0 ≤ L)
    (hw : riemannianEDistOf g O w ≤ dσ + ENNReal.ofReal (L / 2 / Real.sqrt R))
    (hx : riemannianEDistOf g w x < ENNReal.ofReal (Rad / Real.sqrt Rw)) :
    riemannianEDistOf g O x ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hsRw : Real.sqrt R ≤ Real.sqrt Rw := Real.sqrt_le_sqrt hRw
  have hM : 0 ≤ max Rad 0 := le_max_right _ _
  have h1 : Rad / Real.sqrt Rw ≤ max Rad 0 / Real.sqrt R :=
    (div_le_div_of_nonneg_right (le_max_left _ _) (hsR.le.trans hsRw)).trans
      (div_le_div_of_nonneg_left hM hsR hsRw)
  have h2 : L / 2 / Real.sqrt R + max Rad 0 / Real.sqrt R ≤ L / Real.sqrt R := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  calc riemannianEDistOf g O x
      ≤ riemannianEDistOf g O w + riemannianEDistOf g w x := riemannianEDistOf_triangle _ _ _ _
    _ ≤ (dσ + ENNReal.ofReal (L / 2 / Real.sqrt R)) + ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
        add_le_add hw (hx.le.trans (ENNReal.ofReal_le_ofReal h1))
    _ = dσ + ENNReal.ofReal (L / 2 / Real.sqrt R + max Rad 0 / Real.sqrt R) := by
        rw [add_assoc, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal h2)

namespace RetainedCoreHistory

/-- final stage 指标对齐：`m = last`、`HEq` 点 ⇒ stage 度量标量 = 限制 final slab 标量。 -/
theorem scalar_stage_eq_last_P6HF (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon) {m : Fin (K.eventCount + 1)}
    (hm : m = Fin.last K.eventCount) (τ : ℝ) (pm : (K.stage m).Carrier)
    (pS : (K.stage (Fin.last K.eventCount)).Carrier) (hp : HEq pm pS) :
    metricScalarAt (K.toHistory.stageMetric m τ) pm = ((K.finalSlab hfin).restrictIncoming le_rfl
      hfin le_rfl).flow.scalar τ pS := by
  subst hm
  obtain rfl := eq_of_heq hp
  rw [K.stageMetric_last_restrict_P6HF hfin]
  rfl

/-- final stage 指标对齐：距离版。 -/
theorem edist_stage_eq_last_P6HF (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon) {m : Fin (K.eventCount + 1)}
    (hm : m = Fin.last K.eventCount) (τ : ℝ) (pm qm : (K.stage m).Carrier)
    (pS qS : (K.stage (Fin.last K.eventCount)).Carrier) (hp : HEq pm pS) (hq : HEq qm qS) :
    riemannianEDistOf (K.toHistory.stageMetric m τ) pm qm =
      riemannianEDistOf (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric
        τ) pS qS := by
  subst hm
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  rw [K.stageMetric_last_restrict_P6HF hfin]

/-- witness `stageMetric m` → 限制 final slab 度量（`m = last`）。 -/
theorem witness_of_stage_last_P6HF (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon) {m : Fin (K.eventCount + 1)}
    (hm : m = Fin.last K.eventCount) (τ : ℝ) {eps C1 C2 : ℝ} (xm : (K.stage m).Carrier)
    (x : (K.stage (Fin.last K.eventCount)).Carrier) (hx : HEq xm x)
    (h : ∃ W : SpatialCanonicalWitness (K.toHistory.stageMetric m τ) eps C1 C2 xm,
      W.capTubeHasNeckChart eps) :
    ∃ W : SpatialCanonicalWitness (((K.finalSlab hfin).restrictIncoming le_rfl hfin
      le_rfl).flow.base.metric τ) eps C1 C2 x,
      W.capTubeHasNeckChart eps := by
  subst hm
  obtain rfl := eq_of_heq hx
  rw [K.stageMetric_last_restrict_P6HF hfin] at h
  exact h

/-- **selection `hgood` ⇒ final slab 内 witness（`_P6HF`，阈值 `Cg·R`）**：
`witness_of_hgood_slab_Cg_P6LS3` 的 final 孪生（`activeStage τ = last` ⇐ `time last < τ`）。 -/
theorem witness_of_hgood_final_P6HF {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (K : RetainedCoreHistory.{u}) (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier) (R L : ℝ)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (τ : ℝ) (hτ1 : K.time (Fin.last K.eventCount) < τ)
    (haτ : (aSeed : ℝ) ≤ τ) (hτσ : τ ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ)
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    (x : (K.stage (Fin.last K.eventCount)).Carrier)
    (hd : riemannianEDistOf (((K.finalSlab hfin).restrictIncoming le_rfl hfin
      le_rfl).flow.base.metric τ) (seedTrace.point (Fin.last K.eventCount) h1 h2) x ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R))
    (hR : Cg * R ≤ ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar τ x) :
    ∃ W : SpatialCanonicalWitness (((K.finalSlab hfin).restrictIncoming le_rfl hfin
      le_rfl).flow.base.metric τ) eps C1' C2' x,
      W.capTubeHasNeckChart eps := by
  have h0 : (0 : ℝ) ≤ τ := (K.toHistory.time_nonneg _).trans hτ1.le
  let τI : Icc (0 : ℝ) K.toHistory.horizon := ⟨τ, h0, hτσ.trans σ.2.2⟩
  have hact : K.toHistory.activeStage τI = Fin.last K.eventCount :=
    K.toHistory.activeStage_eq_last_of_time_last_le τI hτ1.le
  have hav : aSeed ≤ τI := haτ
  have hvs : τI ≤ σ := hτσ
  let xm : (K.stage (K.toHistory.activeStage τI)).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hact.symm) x
  have hxm : HEq xm x := cast_heq _ _
  have hs := point_heq_of_eq_P6M2 seedTrace hact (K.toHistory.activeStage_mono hav)
    (K.toHistory.activeStage_mono (hvs.trans hsT)) h1 h2
  have hdm : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τI) τI)
      (seedTrace.point (K.toHistory.activeStage τI) (K.toHistory.activeStage_mono hav)
        (K.toHistory.activeStage_mono (hvs.trans hsT))) xm ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) :=
    (K.edist_stage_eq_last_P6HF hfin hact τ _ xm _ x hs hxm).trans_le hd
  have hRm : Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage τI) τI) xm :=
    hR.trans_eq (K.scalar_stage_eq_last_P6HF hfin hact τ xm x hxm).symm
  exact K.witness_of_stage_last_P6HF hfin hact τ xm x hxm (hgood τI hav hvs hLτ xm hdm hRm).1

/-- **selection `hgood` ⇒ final slab 内梯度界（`_P6HF`）**：witness 的 `gradient` 字段。 -/
theorem gradient_of_hgood_final_P6HF {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ} (hC2 : 0 ≤ C2')
    (K : RetainedCoreHistory.{u}) (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier) (R L : ℝ)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (τ : ℝ) (hτ1 : K.time (Fin.last K.eventCount) < τ)
    (haτ : (aSeed : ℝ) ≤ τ) (hτσ : τ ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ)
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    (x : (K.stage (Fin.last K.eventCount)).Carrier)
    (hd : riemannianEDistOf (((K.finalSlab hfin).restrictIncoming le_rfl hfin
      le_rfl).flow.base.metric τ) (seedTrace.point (Fin.last K.eventCount) h1 h2) x ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R))
    (hR : Cg * R ≤ ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar τ x) (ξ :
      TangentSpace ThreeModel x) :
    |scalarDifferential ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow τ x ξ| ≤
      (C2'.toNNReal : ℝ) * ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar τ x
        * Real.sqrt (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar τ x) *
        Real.sqrt ((((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric
          τ).inner x ξ ξ) := by
  obtain ⟨W, -⟩ := K.witness_of_hgood_final_P6HF (Ctime' := Ctime') hfin haT hsT has seedTrace y R L
    hgood τ hτ1 haτ hτσ hLτ h1 h2 x hd hR
  rw [Real.coe_toNNReal _ hC2]
  exact W.gradient ξ

/-- **区域 κ ⇐ seed closure（final slab，`_P6HF`）**：`regionalKappa_of_closure_P6L3` 的 final 孪生；
区域 κ 前提 `hκRF` = KAPPA3 D-8 形 `hκR` 在 final slab（`time last < τ < horizon`）上的实例。 -/
theorem regionalKappa_of_closure_final_P6HF (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier) {R L r ρ κ Aκ : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hκRF : ∀ (c : (K.toHistory.stage (Fin.last K.toHistory.eventCount)).Carrier)
      (U : Set (K.toHistory.stage (Fin.last K.toHistory.eventCount)).Carrier) (a t ρU : ℝ),
      (Tn : ℝ) - r ^ 2 / 2 ≤ a → t ≤ (Tn : ℝ) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        K.toHistory.time (Fin.last K.toHistory.eventCount) < τ → (τ : ℝ) < K.toHistory.horizon →
        ∀ z ∈ U, ∀ zz cc : (K.toHistory.stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        K.toHistory.time (Fin.last K.toHistory.eventCount) < τ → (τ : ℝ) < K.toHistory.horizon →
        ∀ (hav : aSeed ≤ τ) (hvt : τ ≤ Tn), ∀ cc : (K.toHistory.stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (seedTrace.point (K.toHistory.activeStage τ) (K.toHistory.activeStage_mono hav)
                (K.toHistory.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r)) →
      ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        K.toHistory.time (Fin.last K.toHistory.eventCount) < τ → (τ : ℝ) < K.toHistory.horizon →
        ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))
    (hdσ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal ((L + 1) / Real.sqrt R) ≤ ENNReal.ofReal (Aκ * r))
    (U : Set (K.stage (Fin.last K.eventCount)).Carrier) (a t : ℝ)
    (ha : (Tn : ℝ) - r ^ 2 / 2 ≤ a) (ht : t ≤ (Tn : ℝ))
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    (hcl : ∀ τ : ℝ, a ≤ τ → τ ≤ t → K.time (Fin.last K.eventCount) < τ → τ < K.horizon → ∀ x ∈ U,
      riemannianEDistOf (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric
        τ) (seedTrace.point (Fin.last K.eventCount) h1 h2) x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (L / Real.sqrt R)) :
    ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
      ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b) := by
  set dσ := riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
    (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
      (K.toHistory.activeStage_mono hsT)) y with hdσdef
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hL1 : 0 ≤ (L + 1) / Real.sqrt R := div_nonneg (by linarith) hsR.le
  have hfinσ : dσ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hdσ)
  have hρU : ENNReal.ofReal (dσ.toReal + (L + 1) / Real.sqrt R) =
      dσ + ENNReal.ofReal ((L + 1) / Real.sqrt R) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hL1, ENNReal.ofReal_toReal hfinσ]
  have hlt : dσ + ENNReal.ofReal (L / Real.sqrt R) <
      ENNReal.ofReal (dσ.toReal + (L + 1) / Real.sqrt R) := by
    rw [hρU]
    refine ENNReal.add_lt_add_left hfinσ ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    exact div_lt_div_of_pos_right (by linarith) hsR
  refine hκRF (seedTrace.point (Fin.last K.eventCount) h1 h2) U a t
    (dσ.toReal + (L + 1) / Real.sqrt R) ha ht ?_ ?_
  · intro τ haτ hτt hτ1 hτ2 z hz zz cc hzz hcc
    have hact : K.toHistory.activeStage τ = Fin.last K.eventCount :=
      K.toHistory.activeStage_eq_last_of_time_last_le τ hτ1.le
    rw [K.edist_stage_eq_last_P6HF hfin hact τ cc zz _ z hcc hzz]
    exact (hcl τ haτ hτt hτ1 hτ2 z hz).trans_lt hlt
  · intro τ haτ hτt hτ1 hτ2 hav hvt cc hcc
    have hact : K.toHistory.activeStage τ = Fin.last K.eventCount :=
      K.toHistory.activeStage_eq_last_of_time_last_le τ hτ1.le
    have hO := eq_of_heq ((point_heq_of_eq_P6M2 seedTrace hact (K.toHistory.activeStage_mono hav)
      (K.toHistory.activeStage_mono hvt) h1 h2).trans hcc.symm)
    rw [hO, riemannianEDistOf_self, zero_add, hρU]
    exact hdσ

end RetainedCoreHistory

/-- **final slab 的 near-trace U 侧块 `hUVGF` ⇐ `hgood` + final slab closure `hclosGF` + 区域 κ `hκRF`**
（`hUVG_of_selection_Cg_P6S3` 的 final 孪生，`_P6HF`）：`hκRF` / `hclosGF` = `hκR` / `hclosG` 的 final slab
实例（stage 度量形 `stageMetric (Fin.last _)`、时间 `time last < · < horizon`）。结论 = G2
`hsliceR_lateHI_of_slice_data_final_P6HF` 的 `hUVGF` 前提逐字。 -/
theorem ObservedHistory.hUVGF_of_selection_Cg_P6HF {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2')
    {κ Aκ : ℝ} {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) (R L r ρV : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono
              hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z
          →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono
            (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκRF : ∀ᶠ n in atTop, ∀ (c : ((K n).toHistory.stage (Fin.last (K
      n).toHistory.eventCount)).Carrier)
      (U : Set ((K n).toHistory.stage (Fin.last (K n).toHistory.eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ → (τ : ℝ) < (K
          n).toHistory.horizon →
        ∀ z ∈ U, ∀ zz cc : ((K n).toHistory.stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ → (τ : ℝ) < (K
          n).toHistory.horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((K n).toHistory.stageAt τ).Carrier, HEq cc c
          →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              ((seedTrace n).point ((K n).toHistory.activeStage τ) ((K n).toHistory.activeStage_mono
                hav)
                ((K n).toHistory.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ → (τ : ℝ) < (K
          n).toHistory.horizon →
        ∀ z ∈ U, ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) zz
                b))
    (hclosGF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (v : ℝ), (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < v →
        v < (K n).toHistory.horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (K n).toHistory.eventCount) ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory (Fin.last (K n).toHistory.eventCount) ((K
          n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (Fin.last (K n).toHistory.eventCount))
        (h2 : (Fin.last (K n).toHistory.eventCount) ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K
          n).toHistory.stage (Fin.last (K n).toHistory.eventCount)).Carrier),
        riemannianEDistOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
            ((seedTrace n).point (Fin.last (K n).toHistory.eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
            (tr.point (Fin.last (K n).toHistory.eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd /
              Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v) w
          →
        ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
          w
            (Rad / Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric (Fin.last (K
              n).toHistory.eventCount) v) w)),
        ∀ τ : ℝ, v - B / metricScalarAt ((K n).toHistory.stageMetric (Fin.last (K
          n).toHistory.eventCount) v) w ≤ τ → τ ≤ v →
          (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ →
          riemannianEDistOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) τ)
              ((seedTrace n).point (Fin.last (K n).toHistory.eventCount) h1 h2) x ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
              n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                  n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (v : ℝ), (K n).time (Fin.last (K n).eventCount) < v →
        v < (K n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory (Fin.last (K n).eventCount) ((K
          n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (Fin.last (K n).eventCount))
        (h2 : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K
          n).toHistory.stage (Fin.last (K n).eventCount)).Carrier),
        riemannianEDistOf ((G n).flow.base.metric v)
            ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((G n).flow.base.metric v)
            (tr.point (Fin.last (K n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R
              n)) →
        R n ≤ (G n).flow.scalar v w →
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            Cg * R n < (G n).flow.scalar v x →
            ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric v)
              eps C1' C2' x, W.capTubeHasNeckChart eps) ∧
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n).flow.scalar v w ≤ v' →
            Cg * R n < (G n).flow.scalar v' x →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential (G n).flow v' x ξ| ≤
                (C2'.toNNReal : ℝ) * (G n).flow.scalar v' x *
                  Real.sqrt ((G n).flow.scalar v' x) *
                  Real.sqrt (((G n).flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - B / (G n).flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).time (Fin.last (K n).eventCount) < τ → (τ : ℝ) < (K n).horizon →
            ∀ z ∈ riemannianBallOf ((G n).flow.base.metric v) w
                  (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) := by
  intro Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  have hX1 : (1 : ℝ) ≤ max B 0 - σ₁ + 1 := by
    have := le_max_right B 0
    linarith
  filter_upwards [hclosGF Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd,
    hL.eventually_ge_atTop (max (2 * max Rad 0) (max B 0 - σ₁ + 1)),
    hwin (max B 0 - σ₁ + 1) (by linarith), hκRF, hdistσ]
    with n hcl hLn hwn hκn hdσ
  intro v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  rw [hG n] at hwseed hwnear hRw ⊢
  have hcl' := hcl v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w
    (by rw [(K n).stageMetric_last_restrict_P6HF (hfin n)]; exact hwseed)
    (by rw [(K n).stageMetric_last_restrict_P6HF (hfin n)]; exact hwnear)
    (by rw [(K n).stageMetric_last_restrict_P6HF (hfin n)]; exact hRw)
  simp only [(K n).stageMetric_last_restrict_P6HF (hfin n)] at hcl'
  have hRn := hR n
  have hLX : max B 0 - σ₁ + 1 ≤ L n := (le_max_right _ _).trans hLn
  have hL0 : 0 ≤ L n := by linarith
  have hRad : 2 * max Rad 0 ≤ L n := (le_max_left _ _).trans hLn
  have hvσ : v ≤ (σ n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  have hwinB : ∀ τ : ℝ, v - B / (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
    le_rfl).flow.scalar v w ≤ τ →
      (aSeed n : ℝ) ≤ τ ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ τ := fun τ hτ => by
    obtain ⟨e1, e2⟩ := window_P6L3 hRn hRw hvσ1 hτ le_rfl hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  have hwin0 : (aSeed n : ℝ) ≤ v ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ v := by
    have hX0 : max 0 0 - σ₁ + 1 ≤ max B 0 - σ₁ + 1 := by
      rw [max_self]
      linarith [le_max_right B 0]
    obtain ⟨e1, e2⟩ := window_P6L3 (B := 0) (τ := v) hRn hRw hvσ1 (by simp) hX0 hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hRx
    exact (K n).witness_of_hgood_final_P6HF (hfin n) (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) v hv1 hwin0.1 hvσ hwin0.2 h1 h2 x
      (seed_triangle_metric_P6HF _ _ w x _ hRn hRw hL0 hRad hwseed hx) hRx.le
  · intro x hx v' hv' hBv' hRx ξ
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (K n).gradient_of_hgood_final_P6HF hC2 (hfin n) (haT n) (hsT n) (has n) (seedTrace n)
      (y n) (R n) (L n) (hgood n) v' hv'.1 ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hBv' hv'.2.le hv'.1) hRx.le ξ
  · have ha : (Tn n : ℝ) - r n ^ 2 / 2 ≤ v - B / (((K n).finalSlab (hfin n)).restrictIncoming le_rfl
      (hfin n) le_rfl).flow.scalar v w :=
      (hroom n).trans (hwinB _ le_rfl).2
    exact (K n).regionalKappa_of_closure_final_P6HF (hfin n) (haT n) (hsT n) (has n) (seedTrace n)
      (y n) hRn hL0 hκn hdσ _ _ v ha (hvσ.trans (hsT n)) h1 h2
      (fun τ haτ hτv hτ1 _ x hx => hcl' x hx τ haτ hτv hτ1)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
