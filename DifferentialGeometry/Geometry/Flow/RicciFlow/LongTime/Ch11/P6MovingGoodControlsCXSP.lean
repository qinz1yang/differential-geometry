import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVSlabGood_P6L3

set_option autoImplicit false

/-!
# CX-SPINE G7：移动种子球的完整 Good 给实际 incoming 微分控制

使用现有 stage 指标、HEq、scalar 与距离转换；时间导数来自 Good 的真实第二分量，
空间梯度来自同一 witness 的 gradient 字段。这里不从 spatial (b) 恢复时间分量。
时间窗口严格处于同一个 slab；所有测试点都由同一移动种子球供给。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem incoming_control_of_good_CXSP (H : ObservedHistory.{u})
    (j : Fin H.eventCount) (τ : Icc (0 : ℝ) H.horizon)
    (hact : H.activeStage τ = j.castSucc) (hleft : H.time j.castSucc < τ)
    (htop : (τ : ℝ) < H.horizon) {ε C1 C2 : ℝ} {Ct : ℝ≥0}
    (x : (H.stageAt τ).Carrier) (y : (H.stage j.castSucc).Carrier) (hxy : HEq x y)
    (hgood : H.HasSpatialCanonicalTimeControl ε C1 C2 Ct τ x) :
    |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic (τ : ℝ)) τ| ≤
        Ct * (H.event j).incoming.flow.scalar τ y ^ 2 ∧
      ∀ ξ : TangentSpace ThreeModel y,
        |scalarDifferential (H.event j).incoming.flow τ y ξ| ≤
          C2 * (H.event j).incoming.flow.scalar τ y *
            Real.sqrt ((H.event j).incoming.flow.scalar τ y) *
            Real.sqrt (((H.event j).incoming.flow.base.metric τ).inner y ξ ξ) := by
  have hbound := hgood.2 (by simpa only [hact] using hleft) htop
  have hfun : (fun v => metricScalarAt (H.stageMetric (H.activeStage τ) v) x) =
      fun v => (H.event j).incoming.flow.scalar v y :=
    funext (fun v => scalar_stage_eq_P6L2 j hact v x y hxy)
  rw [hfun, scalar_stage_eq_P6L2 j hact τ x y hxy] at hbound
  obtain ⟨W, -⟩ := H.witness_of_stage_P6L3 j hact τ x y hxy hgood.1
  exact ⟨hbound, fun ξ => W.gradient ξ⟩

/-- 移动球中的完整 Good 供给给同一实际 slab 上的局部时间与空间微分控制。 -/
theorem ObservedHistory.incoming_controls_of_moving_good_CXSP (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a t q ρ ε C1 C2 : ℝ} {Ct : ℝ≥0}
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ Tn),
      a ≤ (v : ℝ) → (v : ℝ) ≤ t →
      ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvT)) ρ,
      q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) y →
        H.HasSpatialCanonicalTimeControl ε C1 C2 Ct v y)
    (j : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ H.activeStage Tn)
    (hja : H.time j.castSucc < a) (htj : t < H.time j.succ)
    (hseedA : (aSeed : ℝ) ≤ a) (htT : t ≤ Tn) :
    ∀ w ∈ Ioo a t,
      ∀ y ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric w)
        (seedTrace.point j.castSucc h1 h2) ρ,
      q < (H.event j).incoming.flow.scalar w y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic w) w| ≤
          Ct * (H.event j).incoming.flow.scalar w y ^ 2 ∧
        ∀ ξ : TangentSpace ThreeModel y,
          |scalarDifferential (H.event j).incoming.flow w y ξ| ≤
            C2 * (H.event j).incoming.flow.scalar w y *
              Real.sqrt ((H.event j).incoming.flow.scalar w y) *
              Real.sqrt (((H.event j).incoming.flow.base.metric w).inner y ξ ξ) := by
  intro w hw y hy hR
  have hw0 : 0 ≤ w := (H.time_nonneg _).trans (hja.trans hw.1).le
  have hwT : w ≤ Tn := hw.2.le.trans htT
  let τ : Icc (0 : ℝ) H.horizon := ⟨w, hw0, hwT.trans Tn.2.2⟩
  have hact : H.activeStage τ = j.castSucc :=
    H.activeStage_eq_of_slab_P6L3 j τ (hja.trans hw.1).le (hw.2.trans htj)
  let x : (H.stageAt τ).Carrier :=
    cast (congrArg (fun m => (H.stage m).Carrier) hact.symm) y
  have hxy : HEq x y := cast_heq _ _
  have hav : aSeed ≤ τ := hseedA.trans hw.1.le
  have hvT : τ ≤ Tn := hwT
  have hseed := point_heq_of_eq_P6M2 seedTrace hact (H.activeStage_mono hav)
    (H.activeStage_mono hvT) h1 h2
  have hball : x ∈ riemannianBallOf (H.stageMetric (H.activeStage τ) τ)
      (seedTrace.point (H.activeStage τ) (H.activeStage_mono hav)
        (H.activeStage_mono hvT)) ρ := by
    change riemannianEDistOf _ _ _ < _
    rw [edist_stage_eq_P6L2 j hact w _ x _ y hseed hxy]
    exact hy
  have hR' : q ≤ metricScalarAt (H.stageMetric (H.activeStage τ) τ) x :=
    hR.le.trans_eq (scalar_stage_eq_P6L2 j hact w x y hxy).symm
  have hG := hgood τ hav hvT hw.1.le hw.2.le x hball hR'
  exact incoming_control_of_good_CXSP H j τ hact (hja.trans hw.1)
    (hw.2.trans_le (htT.trans Tn.2.2)) x y hxy hG

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
