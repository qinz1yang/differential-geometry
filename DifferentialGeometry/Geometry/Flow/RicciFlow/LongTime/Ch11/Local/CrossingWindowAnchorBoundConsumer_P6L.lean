import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingWindowAnchorBound_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionLocalLimitDepthSchedule_P6L

/-!
# G1 consumer：depth-schedule 局部流极限 `_P6L` 的 survivor block ⇒ `:227_P6L` 的 block 导数界
（O-CH11-P6D2 G1）

把 `exists_local_pointed_flow_limits_of_depth_schedule_P6L` 输出的 block（`W k n` = 归一化球、
完整 survivor data）直接喂 `eventually_abs_derivWithin_scalar_le_of_survivor_blocks_P6L`
（trace-local `hstage`，P6D G2 `hderiv` 形），`E n` = event 时刻集合。这正是 G2（window anchor
`:555_P6L`）里 `hderiv` 的接法。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace ObservedHistory

universe u

/-- consumer：局部前提 ⇒ depth-schedule 极限的 block 上 `|∂ₜ⁻ R| ≤ Ct R²`（非 event 时刻）。 -/
example (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) (τ : ℕ → ℝ) (hτ : ∀ k, 0 < τ k)
    (htraced : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k / R n)
        (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (H n).isParabolicallyRmControlledBall v
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))))
    {Ct qD : ℝ} (hCt : 0 ≤ Ct) {qst : ℕ → ℝ} (hqD : ∀ n, qst n ≤ R n * qD)
    (hstage : ∀ Dw Tw : ℝ, 0 < Dw → 0 < Tw → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - Tw / R n ≤ v →
      (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        qst n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v')
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ct * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ^ 2) :
    ∃ (W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens ((H n).stageAt (t n)).Carrier)
      (h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)),
      ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-τ k) 0,
        (∀ i, (t n : ℝ) + s / R n ≠ (H n).time i) →
        ∀ z : W k n, qD < metricScalarAt (h k n s) z →
          |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
            Ct * metricScalarAt (h k n s) z ^ 2 := by
  obtain ⟨W, h, hblock, -⟩ := exists_local_pointed_flow_limits_of_depth_schedule_P6L H t y R hR
    hRlim τ hτ htraced hr₀ hw hseed hκ ρnc hkappa hPhi hpinch
  refine ⟨W, h, fun k => ?_⟩
  have key := eventually_abs_derivWithin_scalar_le_of_survivor_blocks_P6L (Hs := H) (ts := t)
    (ys := y) (hR := hR) (W := W) (h := h) hτ (fun k => (hblock k).mono fun _ hn => hn.1)
    (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1)
    (E := fun n => {s | ∃ i, (t n : ℝ) + s / R n = (H n).time i}) hCt hqD hstage
    (fun n s _ hsE i hi => hsE ⟨i, hi⟩) k
  filter_upwards [key] with n hn s hs hne z hz
  exact hn s hs (fun ⟨i, hi⟩ => hne i hi) z hz

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
