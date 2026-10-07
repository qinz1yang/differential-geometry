import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVSlabGood_P6L3

/-!
# U 侧单点生产的阈值系数参数化（`4R` → `Cg·R`；S-CH11-P6CG G1，后缀 `_P6LS3`）

`Local/HUVSlabGood_P6L3` 的 `witness_of_hgood_slab_P6L3` / `gradient_of_hgood_slab_P6L3` 逐字副本，只把
`hgood` 与 `hR` 里的阈值 `4 * R` 换成任意系数 `Cg * R`（证明体逐字：阈值只是透传）；与 O-CH11-P6ANCH3 G5 的
`_Cg_P6L3` / `_Cg_P6M3` 对齐。`activeStage_eq_of_slab_P6L3` / `witness_of_stage_P6L3` 阈值无关，直接复用。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

universe u

namespace ObservedHistory

/-- **selection `hgood` ⇒ slab 内 witness（`_Cg_P6LS3`，阈值 `Cg·R`）**：slab `j` 内时刻 `τ`（`aSeed ≤ τ ≤ σ`、
`σ − L²/R ≤ τ`）、`d_τ(O_j, x) ≤ d_σ(O_σ, y) + L/√R`、`Cg·R ≤ R(τ, x)` ⇒ incoming 形 witness。 -/
theorem witness_of_hgood_slab_Cg_P6LS3 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (y : (H.stageAt σ).Carrier) (R L : ℝ)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (j : Fin H.eventCount) (τ : ℝ) (hτ1 : H.time j.castSucc < τ) (hτ2 : τ < H.time j.succ)
    (haτ : (aSeed : ℝ) ≤ τ) (hτσ : τ ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ)
    (h1 : H.activeStage aSeed ≤ j.castSucc) (h2 : j.castSucc ≤ H.activeStage Tn)
    (x : (H.stage j.castSucc).Carrier)
    (hd : riemannianEDistOf ((H.event j).incoming.flow.base.metric τ)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R))
    (hR : Cg * R ≤ (H.event j).incoming.flow.scalar τ x) :
    ∃ W : SpatialCanonicalWitness ((H.event j).incoming.flow.base.metric τ) eps C1' C2' x,
      W.capTubeHasNeckChart eps := by
  have h0 : (0 : ℝ) ≤ τ := (H.time_nonneg _).trans hτ1.le
  let τI : Icc (0 : ℝ) H.horizon := ⟨τ, h0, hτσ.trans σ.2.2⟩
  have hact : H.activeStage τI = j.castSucc := H.activeStage_eq_of_slab_P6L3 j τI hτ1.le hτ2
  have hav : aSeed ≤ τI := haτ
  have hvs : τI ≤ σ := hτσ
  let xm : (H.stage (H.activeStage τI)).Carrier :=
    cast (congrArg (fun m => (H.stage m).Carrier) hact.symm) x
  have hxm : HEq xm x := cast_heq _ _
  have hs := point_heq_of_eq_P6M2 seedTrace hact (H.activeStage_mono hav)
    (H.activeStage_mono (hvs.trans hsT)) h1 h2
  have hdm : riemannianEDistOf (H.stageMetric (H.activeStage τI) τI)
      (seedTrace.point (H.activeStage τI) (H.activeStage_mono hav)
        (H.activeStage_mono (hvs.trans hsT))) xm ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) :=
    (edist_stage_eq_P6L2 j hact τ _ xm _ x hs hxm).trans_le hd
  have hRm : Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage τI) τI) xm :=
    hR.trans_eq (scalar_stage_eq_P6L2 j hact τ xm x hxm).symm
  exact H.witness_of_stage_P6L3 j hact τ xm x hxm (hgood τI hav hvs hLτ xm hdm hRm).1

/-- **selection `hgood` ⇒ slab 内梯度界（`_Cg_P6LS3`，阈值 `Cg·R`）**：`witness_of_hgood_slab_Cg_P6LS3` +
witness `gradient` 字段（`Cgrad := C2'.toNNReal`，`0 ≤ C2'`）。 -/
theorem gradient_of_hgood_slab_Cg_P6LS3 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ} (hC2 : 0 ≤ C2')
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (y : (H.stageAt σ).Carrier) (R L : ℝ)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (j : Fin H.eventCount) (τ : ℝ) (hτ1 : H.time j.castSucc < τ) (hτ2 : τ < H.time j.succ)
    (haτ : (aSeed : ℝ) ≤ τ) (hτσ : τ ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ)
    (h1 : H.activeStage aSeed ≤ j.castSucc) (h2 : j.castSucc ≤ H.activeStage Tn)
    (x : (H.stage j.castSucc).Carrier)
    (hd : riemannianEDistOf ((H.event j).incoming.flow.base.metric τ)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R))
    (hR : Cg * R ≤ (H.event j).incoming.flow.scalar τ x) (ξ : TangentSpace ThreeModel x) :
    |scalarDifferential (H.event j).incoming.flow τ x ξ| ≤
      (C2'.toNNReal : ℝ) * (H.event j).incoming.flow.scalar τ x *
        Real.sqrt ((H.event j).incoming.flow.scalar τ x) *
        Real.sqrt (((H.event j).incoming.flow.base.metric τ).inner x ξ ξ) := by
  obtain ⟨W, -⟩ := H.witness_of_hgood_slab_Cg_P6LS3 (Ctime' := Ctime') haT hsT has seedTrace y R L
    hgood j τ hτ1 hτ2 haτ hτσ hLτ h1 h2 x hd hR
  rw [Real.coe_toNNReal _ hC2]
  exact W.gradient ξ

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
