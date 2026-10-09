import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceAnchorOpen_P6L2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection

/-!
# U 侧（hUV）的单点生产：selection `hgood` ⇒ slab 内 witness / 梯度（O-CH11-P6ANCH3 G2，后缀 `_P6L3`）

条件形 `hUVC`（`P6SliceDichotomyCondP6M3`）的 witness / 梯度两项都在 incoming slab 形
（`(H.event j).incoming.flow.base.metric τ`、stage `j.castSucc` 的点）上陈述；selection 的 `hgood` 在
history 形（`H.stageMetric (H.activeStage v) v`、`stageAt v` 的点）上。本文件做单点对齐：
* `activeStage_eq_of_slab_P6L3`：开 slab 时刻的 `activeStage`；
* `witness_of_stage_P6L3`：witness 从 `stageMetric m` 搬到 incoming（`m = j.castSucc`，`HEq`）；
* **`witness_of_hgood_slab_P6L3`**：slab `j` 内时刻 `τ`、seed 点 `O_j` 的距离 `≤ d_σ + L/√R`、`4R ≤ R(τ, x)`
  ⇒ incoming 形 witness（`hgood` 在 `τ` 的 Icc 提升上取值）；
* **`gradient_of_hgood_slab_P6L3`**：同前提 ⇒ `|dR(τ, x)| ≤ C2' R^{3/2}|ξ|`（witness `gradient` 字段，
  `Cgrad := C2'.toNNReal`）。
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

/-- 开 slab 时刻的 `activeStage`（`_P6L3`）。 -/
theorem activeStage_eq_of_slab_P6L3 (H : ObservedHistory.{u}) (j : Fin H.eventCount)
    (τ : Icc (0 : ℝ) H.horizon) (h1 : H.time j.castSucc ≤ τ) (h2 : (τ : ℝ) < H.time j.succ) :
    H.activeStage τ = j.castSucc :=
  (H.mem_stageDomain_iff τ j.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (τ : ℝ) ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨h1, h2⟩))

/-- witness `stageMetric m` → incoming（`m = j.castSucc`，`_P6L3`）。 -/
theorem witness_of_stage_P6L3 (H : ObservedHistory.{u}) (j : Fin H.eventCount)
    {m : Fin (H.eventCount + 1)} (hm : m = j.castSucc) (τ : ℝ) {eps C1 C2 : ℝ}
    (xm : (H.stage m).Carrier) (x : (H.stage j.castSucc).Carrier) (hx : HEq xm x)
    (h : ∃ W : SpatialCanonicalWitness (H.stageMetric m τ) eps C1 C2 xm,
      W.capTubeHasNeckChart eps) :
    ∃ W : SpatialCanonicalWitness ((H.event j).incoming.flow.base.metric τ) eps C1 C2 x,
      W.capTubeHasNeckChart eps := by
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

/-- **selection `hgood` ⇒ slab 内 witness（`_P6L3`）**：slab `j` 内时刻 `τ`（`aSeed ≤ τ ≤ σ`、
`σ − L²/R ≤ τ`）、`d_τ(O_j, x) ≤ d_σ(O_σ, y) + L/√R`、`4R ≤ R(τ, x)` ⇒ incoming 形 witness。 -/
theorem witness_of_hgood_slab_P6L3 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
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
        4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
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
    (hR : 4 * R ≤ (H.event j).incoming.flow.scalar τ x) :
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
  have hRm : 4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage τI) τI) xm :=
    hR.trans_eq (scalar_stage_eq_P6L2 j hact τ xm x hxm).symm
  exact H.witness_of_stage_P6L3 j hact τ xm x hxm (hgood τI hav hvs hLτ xm hdm hRm).1

/-- **selection `hgood` ⇒ slab 内梯度界（`_P6L3`）**：`witness_of_hgood_slab_P6L3` + witness `gradient`
字段（`Cgrad := C2'.toNNReal`，`0 ≤ C2'`）。 -/
theorem gradient_of_hgood_slab_P6L3 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} (hC2 : 0 ≤ C2')
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
        4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
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
    (hR : 4 * R ≤ (H.event j).incoming.flow.scalar τ x) (ξ : TangentSpace ThreeModel x) :
    |scalarDifferential (H.event j).incoming.flow τ x ξ| ≤
      (C2'.toNNReal : ℝ) * (H.event j).incoming.flow.scalar τ x *
        Real.sqrt ((H.event j).incoming.flow.scalar τ x) *
        Real.sqrt (((H.event j).incoming.flow.base.metric τ).inner x ξ ξ) := by
  obtain ⟨W, -⟩ := H.witness_of_hgood_slab_P6L3 (Ctime' := Ctime') haT hsT has seedTrace y R L
    hgood j τ hτ1 hτ2 haτ hτσ hLτ h1 h2 x hd hR
  rw [Real.coe_toNNReal _ hC2]
  exact W.gradient ξ

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
