import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LocalKappaP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LimitNoncollapseP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitSurvivorCanonicalWitnessC11X

/-!
# P6：M5 → M8 的接线（window κ ⇒ trace-local κ）与 M7 收口（O-CH11-P6B G2）

后缀 `_P6B`。

* `tracedKappa_of_window_P6B`：L5 的 window 形（`nr := fun _ => 0`，即 KL 84.1(a) 字面的全尺度形）
  + **L7 survival 的距离结论**（坏点 `(s n, y n)` 的 traced 球 `B(y, D/√R)` 的 backward trace 在
  `v ∈ [s − T/R, s]` 上留在种子 trace 点 `O_v` 的 `A r` 邻域里——astra `FiniteEventFirstContact:639`
  结论的形）+ 窗口条件 `t − r²/2 ≤ s − T/R` ⇒ M8 装配所需的 **trace-local κ**（尺度 `≤ r/200`）。
* consumer：bridge + M8 装配 ⇒ 坏点序列的局部古代极限 `κ/250`-noncollapsed（只要 `r √R → ∞`）。
* M7：astra `:43` 的 `eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit`
  已由 S-CH11-EXT2 逐字落地于 `AncientLimitSurvivorCanonicalWitnessC11X`（LANDED-EXT2）；这里只验证
  可 import 并取出常数 `C ≥ 1`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

attribute [local instance] CheegerGromovCompactness.PointedRiemannianManifold.topology
  CheegerGromovCompactness.PointedRiemannianManifold.charted
  CheegerGromovCompactness.PointedRiemannianManifold.smooth
  CheegerGromovCompactness.PointedRiemannianManifold.t2
  CheegerGromovCompactness.PointedRiemannianManifold.sigmaCompact

/-- **M5 → M8 bridge**：window κ（全尺度形）+ survival 的距离结论 + 窗口条件 ⇒ 坏点序列的
trace-local κ（尺度 `≤ r n / 200`），即 `exists_local_ancient_limit_kappa_noncollapsed_P6B` 的
`hkappa`（`ρnc := fun n => r n / 200`）。 -/
theorem tracedKappa_of_window_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A κ : ℝ}
    (hW : LocalKappaWindowAt_P6B F (fun _ => 0) A κ) (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal (A * r n)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvt : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ r n / 200 →
        (F.tower.history (ind n)).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) r'' := by
  obtain ⟨T₀, -, hK⟩ := hW
  intro D T hD hT
  filter_upwards [hdist D T hD hT, hwin T hT, hlate.eventually_ge_atTop T₀] with n hd hw hl
  intro x hx v hvs hv tr r'' hr'' hρ hpc
  have hr0 : 0 < r n := (hsmall n).1
  have hvwin : (t n : ℝ) - r n ^ 2 / 2 ≤ v := hw.trans hv
  have hav : aSeed n ≤ v := by
    change (aSeed n : ℝ) ≤ v
    rw [hclock n]
    nlinarith [sq_nonneg (r n)]
  have hvt : v ≤ t n := hvs.trans (hst n)
  have hxball := hd x hx v hvs hv tr hav
  refine hK (ind n) (t n) (p n) (r n) hl (htime n) (hsmall n) (hvol n) (aSeed n) (haT n)
    (hclock n) (seedTrace n) v hav hvt hvwin _ hxball r'' ?_ (by linarith) hpc
  change (0 : ℝ) / 100 ≤ r''
  rw [zero_div]
  exact hr''.le

/-- consumer（端到端接线）：window κ + survival 距离结论 + 坏点处 traced regions、种子体积、
trace-local pinching ⇒ 坏点序列的局部古代极限对每个 `ρ` 是 `κ/250`-noncollapsed
（`ρnc n = r n / 200`，只要 `(r n / 200) √R n → ∞`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A κ : ℝ} (hκ : 0 < κ)
    (hW : LocalKappaWindowAt_P6B F (fun _ => 0) A κ) (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal (A * r n))
    (htraced : ∀ A' T : ℝ, 0 < A' → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (F.tower.history (ind n)).toHistory.isTracedRegion (s n) (y n)
        (A' / Real.sqrt (R n)) (T / R n) (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel
          ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier
          ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n))
          (riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (r₀ / Real.sqrt (R n))))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvt : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)))
          (Phi (metricScalarAt ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt))))) :
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P' : CheegerGromovCompactness.PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (_ : CheegerGromovCompactness.PointedRiemannianConvergenceMaps
          ({ obj := fun n =>
            { M := ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier
              basepoint := y n
              metric := scaleMetric (R n) (hR n)
                ((F.tower.history (ind n)).toHistory.stageMetric
                  ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) } } :
            CheegerGromovCompactness.PointedRiemannianSeq.{u, 0, 0} ThreeModel) P' f),
        CheegerGromovCompactness.MetricComplete P' ∧ ConnectedSpace P'.M ∧
        ∃ (G : ℝ → SmoothRiemannianMetric ThreeModel P'.M)
          (_ : IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P'.M)
            Perelman.CanonicalNeighborhood.ancientTimeInterval)),
          G 0 = P'.metric ∧
          ∀ ρ : ℝ, 0 < ρ → Perelman.ParabolicallyKappaNoncollapsedBelowScale
            ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P'.M)
              Perelman.CanonicalNeighborhood.ancientTimeInterval) (κ / 250) ρ :=
  ObservedHistory.exists_local_ancient_limit_kappa_noncollapsed_P6B
    (fun n => (F.tower.history (ind n)).toHistory) s y R hR hRlim htraced hr₀ hw hseed hκ
    (fun n => r n / 200) hradii
    (tracedKappa_of_window_P6B hW ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace
      s hst y R hwin hdist) hPhi hpinch

open Perelman.CanonicalNeighborhood.FiniteHorn in
/-- M7 收口：EXT2 落地的 astra `:43`（`normalized_local_flow_limit`）可直接 import，取出其常数
`C ≥ 1`（L8 装配将以它把局部古代 κ-solution 极限转成近似流上的 canonical witness）。 -/
example {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 11) : ∃ C : ℝ, 1 ≤ C :=
  (eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit.{0} hε
    hsmall).imp fun _ hC => hC.1

end GC.LongTime.Ch11
