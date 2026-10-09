import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointAssemblyC11G
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceAnchorWindow_P6L

/-!
# consumer（G2w ⇒ P6GEO）：DIST `hgeom` 的 BCAD 输入换成窗口切片二分（O-CH11-P6ANCH，后缀 `_P6M`）

P6GEO `exists_hgeom_of_K0_pinching_C11G` 的 BCAD 形 `hscal` 由本车道 G2w
`ObservedHistory.hscal_of_window_dichotomy_P6L` 从窗口切片二分前提 `hW`（中心曲率 `≤ A·R_n` + 切片 SLT
有界曲率 + cap-window 嵌入）给出；标准解比较常数 `η₃ Cup Lc` 提到最前，其余前提逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **consumer（G2w ⇒ P6GEO `hgeom`）**：`hscal` 换成窗口切片二分 `hW`。 -/
theorem exists_hgeom_of_window_dichotomy_P6M :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (Hs : ℕ → ObservedHistory.{u})
      (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
      (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
      (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
        ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
      (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
      (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r : ℕ → ℝ), (∀ᶠ n in atTop, 0 < R n) →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (t n) (p n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n)) →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
        InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∃ A QB Dcap D₂ : ℝ, 1 ≤ A ∧ 0 ≤ QB ∧
        Dcap + 1 + (2 * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧ ∀ᶠ n in atTop,
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
            τ < s n →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x ≤ A * R n ∧
          ∃ CWP : ((Hs n).stageAt (s n)).Carrier → Prop,
            (∀ w, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
                (x) w <
                ENNReal.ofReal (1 / Real.sqrt (R n)) →
              ¬ CWP w → R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) w →
              ∀ x',
              riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) w x' <
                ENNReal.ofReal ((2 * Real.sqrt A + 1) /
                  Real.sqrt (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) w)) →
              metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x' ≤
                QB * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) w) ∧
            (∀ w, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
                (x) w <
                ENNReal.ofReal (1 / Real.sqrt (R n)) → CWP w →
              ∃ (Ξ : standardCapWindow D₂ → ((Hs n).stageAt (s n)).Carrier)
                (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
                Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
                ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                  τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                  ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                    metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                        ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)) Ξ hΞ)
                      ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                      (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) ∧
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
            (s n : ℝ) - T / R n ≤ v →
          ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
            ((Hs n).activeStage_mono hvs) x,
          ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
            (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
          metricScalarAt ((Hs n).stageMetric e.castSucc t')
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤ A * R n ∧
          ∃ CWP : ((Hs n).stage e.castSucc).Carrier → Prop,
            (∀ w, riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
                (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) w <
                ENNReal.ofReal (1 / Real.sqrt (R n)) →
              ¬ CWP w → R n ≤ metricScalarAt ((Hs n).stageMetric e.castSucc t') w →
              ∀ x',
              riemannianEDistOf ((Hs n).stageMetric e.castSucc t') w x' <
                ENNReal.ofReal ((2 * Real.sqrt A + 1) /
                  Real.sqrt (metricScalarAt ((Hs n).stageMetric e.castSucc t') w)) →
              metricScalarAt ((Hs n).stageMetric e.castSucc t') x' ≤
                QB * metricScalarAt ((Hs n).stageMetric e.castSucc t') w) ∧
            (∀ w, riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
                (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) w <
                ENNReal.ofReal (1 / Real.sqrt (R n)) → CWP w →
              ∃ (Ξ : standardCapWindow D₂ → ((Hs n).stage e.castSucc).Carrier)
                (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
                Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
                ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                  τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                  ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                    metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                        ((Hs n).stageMetric e.castSucc t')) Ξ hΞ)
                      ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                      (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃))) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
        GeometricCutoffRecord (Hs n) e (q n)),
      (∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
        ((records n e he).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
          (s n : ℝ) - T / R n < (Hs n).time e.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((records n e he).static b).neck.scale) →
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          (riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          Real.sqrt (normSq0S ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z 4
            (metricRm04At ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z)) ≤ K * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)), (v : ℝ) < (Hs n).time e.succ →
        ∀ (he : T₀ n ≤ (Hs n).time e.succ) b,
          (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
            tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
          (riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          ricciTensor ((Hs n).stageMetric e.castSucc t') z ξ ξ ≤
            (3 / (ℓ / Real.sqrt (R n)) ^ 2) *
              ((Hs n).stageMetric e.castSucc t').inner z ξ ξ) := by
  obtain ⟨η₃, Cup, Lc, h1, h2, h3, hscalW⟩ := ObservedHistory.hscal_of_window_dichotomy_P6L.{u}
  obtain ⟨ε₀, hε₀, hG⟩ := exists_hgeom_of_K0_pinching_C11G.{u}
  refine ⟨η₃, Cup, Lc, h1, h2, h3, ε₀, hε₀, ?_⟩
  intro Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX hwin hlate a₀ ha₀ hpin hW
  exact hG Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX hwin hlate ha₀ hpin
    (hscalW Hs s y aSeed R hR hW)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
