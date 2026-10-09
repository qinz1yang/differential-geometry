import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10DepthHstopCXJP

/-!
# hextend 深度步 G2：`hscalC` 的生产（CX-J10DEPTH，后缀 `_CXJP`）

hextend 单步的 trace 点标量源（条件形，供 G1 `hstop_scalC_CXJP`）：trace `A`（窗口底 `a` → `σ`），
* `[a₁, σ]`（`a₁` = 上一步 traced region 的底）：traced region 数据 `A₁.isRmBoundedBy (K₁·R)` ⇒
  `R ≤ 9·K₁·R`（`point_unique` 把 `A` 与 `A₁` 对齐）；
* `[v, a₁)`：anchor `R(a₁, A(a₁)) ≤ M·R` + `[v, σ]` 上 trace 在 Ω′ 内（Good 前提）⇒ CXJT0
  `scalar_le_two_mul_stopped_ceiling_CXJT0`（hgood 时间分量，阈值 `Cg·R`，`C_ball := M`）⇒
  `R ≤ 2·max{M, Cg, 1}·R`。**每步独立 anchor**：只用本步 anchor 值作初值，不读上一步 ODE 输出。
无 `qcan` / `qcap`；traced region 只用上一步已证数据。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- **traced region 段的标量界（`_CXJP`）**：`a₁ ≤ v`，`A` 与 traced-region 的 `A₁` 在 `v` 处同点
（`point_unique`），`|R| ≤ 3²·|Rm| ≤ 9·K₁·R ≤ 2·Q_b·R`。 -/
theorem scalar_le_of_isRmBounded_CXJP {K₁ Qb : ℝ} (H : ObservedHistory.{u})
    {a a₁ σ : Icc (0 : ℝ) H.horizon} (haσ : a ≤ σ) (ha₁σ : a₁ ≤ σ) {R : ℝ} (hR : 0 < R)
    (hK₁ : 9 * K₁ ≤ 2 * Qb) (hK₁0 : 0 ≤ K₁) {z : (H.stageAt σ).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (A₁ : BackwardPointTrace H (H.activeStage a₁) (H.activeStage σ) (H.activeStage_mono ha₁σ) z)
    (hA₁ : A₁.isRmBoundedBy (hat := ha₁σ) (K₁ * R))
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hva : a₁ ≤ v) (hvσ : v ≤ σ) :
    metricScalarAt (H.stageMetric (H.activeStage v) v)
      (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) ≤
      2 * (Qb * R) := by
  have hpt := BackwardPointTrace.point_unique
    (A.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvσ))
    (A₁.restrictFirst (H.activeStage_mono hva) (H.activeStage_mono hvσ))
    (H.activeStage v) le_rfl (H.activeStage_mono hvσ)
  have hnorm := hA₁.1 v hva hvσ
  have hsc := scalar_abs_le_rm (H.stageMetric (H.activeStage v) v)
    (A₁.point (H.activeStage v) (H.activeStage_mono hva) (H.activeStage_mono hvσ))
  have hfin : (Module.finrank ℝ (TangentSpace ThreeModel
      (A₁.point (H.activeStage v) (H.activeStage_mono hva) (H.activeStage_mono hvσ))) : ℝ) =
      3 := by
    change ((Module.finrank ℝ ThreeSpace : ℕ) : ℝ) = 3
    simp [ThreeSpace]
  have hsq : Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v)
      (A₁.point (H.activeStage v) (H.activeStage_mono hva) (H.activeStage_mono hvσ)) 4
      (metricRm04At (H.stageMetric (H.activeStage v) v)
        (A₁.point (H.activeStage v) (H.activeStage_mono hva) (H.activeStage_mono hvσ)))) ≤
      K₁ * R :=
    (Real.sqrt_le_sqrt hnorm).trans (Real.sqrt_sq (by positivity)).le
  rw [hfin] at hsc
  refine (le_of_eq (congrArg _ hpt)).trans ((le_abs_self _).trans (hsc.trans ?_))
  have h3 := mul_le_mul_of_nonneg_right hK₁ hR.le
  have e1 : 9 * K₁ * R = (3 : ℝ) ^ 2 * (K₁ * R) := by ring
  have e2 : 2 * Qb * R = 2 * (Qb * R) := by ring
  have e3 := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 3 ^ 2)
  linarith

/-- **`hscalC` 的生产（`_CXJP`）**：traced region（`[a₁, σ]`）+ anchor ceiling ODE（`[·, a₁)`）。 -/
theorem hscalC_of_traced_anchor_CXJP {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg M K₁ Qb Tx : ℝ}
    (H : ObservedHistory.{u}) {Tn aSeed a a₁ σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hL0 : 0 ≤ L)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
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
    (hstep : 2 * Ctime' * max (max M Cg) 1 * Tx ≤ 1)
    (hQb : max (max M Cg) 1 ≤ Qb) (hK₁ : 9 * K₁ ≤ 2 * Qb) (hK₁0 : 0 ≤ K₁)
    (haS : aSeed ≤ a) (haa₁ : a ≤ a₁) (ha₁σ : a₁ ≤ σ)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (a₁ : ℝ) - a ≤ Tx / R)
    {z : (H.stageAt σ).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ)
      (H.activeStage_mono (haa₁.trans ha₁σ)) z)
    (A₁ : BackwardPointTrace H (H.activeStage a₁) (H.activeStage σ) (H.activeStage_mono ha₁σ) z)
    (hA₁ : A₁.isRmBoundedBy (hat := ha₁σ) (K₁ * R))
    (hanc : metricScalarAt (H.stageMetric (H.activeStage a₁) a₁)
      (A.point (H.activeStage a₁) (H.activeStage_mono haa₁) (H.activeStage_mono ha₁σ)) ≤ M * R) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ),
      (∀ (v' : Icc (0 : ℝ) H.horizon) (hav' : a ≤ v') (hv'σ : v' ≤ σ), (v : ℝ) ≤ v' →
        riemannianEDistOf (H.stageMetric (H.activeStage v') v')
            (seedTrace.point (H.activeStage v')
              (H.activeStage_mono (haS.trans hav'))
              (H.activeStage_mono (hv'σ.trans hσT)))
            (A.point (H.activeStage v') (H.activeStage_mono hav')
              (H.activeStage_mono hv'σ)) <
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / 2 / Real.sqrt R)) →
      metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvσ)) ≤ 2 * (Qb * R) := by
  intro v hav hvσ hgoodV
  have hQ1 : 1 ≤ max (max M Cg) 1 := le_max_right _ _
  by_cases hva : a₁ ≤ v
  · exact scalar_le_of_isRmBounded_CXJP H (haa₁.trans ha₁σ) ha₁σ hR hK₁ hK₁0 A A₁ hA₁ v hav hva hvσ
  · -- anchor 出发的 ceiling ODE 段
    have hva' : v ≤ a₁ := (lt_of_not_ge hva).le
    have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
    let A'' := (A.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvσ)).restrictLast
      (H.activeStage_mono hva') (H.activeStage_mono ha₁σ)
    have hceil := scalar_le_two_mul_stopped_ceiling_CXJT0 (Cball := M) H haT hσT has seedTrace y L
      hR hgood (le_refl _) hstep hva' ha₁σ (haS.trans hav) (haL.trans hav) (by
        have : (a : ℝ) ≤ v := hav
        linarith) hanc A'' ?_ v le_rfl hva'
    · exact hceil.trans (by nlinarith [mul_le_mul_of_nonneg_right hQb hR.le])
    · intro u hvu hua
      have hg := hgoodV u (hav.trans hvu) (hua.trans ha₁σ) hvu
      refine hg.le.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
      exact div_le_div_of_nonneg_right (by linarith) hsR.le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
