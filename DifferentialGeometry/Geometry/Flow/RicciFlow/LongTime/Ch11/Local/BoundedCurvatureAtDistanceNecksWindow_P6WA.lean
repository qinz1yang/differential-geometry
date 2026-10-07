import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistorySurvivorIncomingPinchingWindow_P6WA

/-!
# L6-A 窗口版：`BoundedCurvatureAtDistanceNecks:413`（`_P6WA`）

原 `metricRm04StandardAt_nonneg_of_normalized_terminal_pinching`（`Necks:413`，TP:97 的 `hsec`）的
`hpinch` 只经 `TPin:19` 在 `t → s⁻` 处求值。P6WIN 窗口版：加窗口起点 `(c : ℕ → ℝ)`、
`hc : ∀ i, c i < s i`（`(A …)` 之后；坑 F6：全 `i` 的严格性），`hpinch` 取 `Ico (a i) (s i) ∩ Ici (c i)`，
调 `TPin:19` 窗口版。结论逐字。consumer：原形由窗口版推回（取 `c i = a i`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal Topology NNReal

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open OrientedThreeStage.IncomingSlab

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **`_window_P6WA`**：`Necks:413` 的时间窗版（`hpinch` 取 `Ico ∩ Ici (c i)`，加 `c`、`hc`）。 -/
theorem metricRm04StandardAt_nonneg_of_normalized_terminal_pinching_window_P6WA
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ) (A : ∀ i, (P i).ClosedSlab (a i) (s i))
    (c : ℕ → ℝ) (hc : ∀ i, c i < s i)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (s i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow (Ico (a i) (s i) ∩ Ici (c i)) Phi)
    {f : ℕ → ℕ} (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (s i) (x i).val)
              (zero_lt_one.trans_le (hQ i)) ((A i).endpointTerminalLimitMetric (P i)).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hQlim : Tendsto (fun n => (A (f n)).flow.scalar (s (f n)) (x (f n)).val) atTop atTop) :
    ∀ (z : Pl.M) (v w : TangentSpace ThreeModel z),
      0 ≤ metricRm04StandardAt Pl.metric z v w w v := by
  have hQpos : ∀ i, 0 < (A i).flow.scalar (s i) (x i).val := fun i => zero_lt_one.trans_le (hQ i)
  apply sectional_nonnegative_of_pointed_admissible_pinching
    M hcanonical hPhi (fun i => (A i).flow.scalar (s i) (x i).val) hQpos hQlim
  intro i y
  have hp :=
    (TerminalLimitMetric.curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative_window_P6WA
      ((A i).endpointTerminalLimitMetric (P i)))
      hPhi.contDiff.continuous (hc i) (hpinch i) y
  change curvatureOperatorLowerBoundAt (scaleMetric ((A i).flow.scalar (s i) (x i).val) (hQpos i)
    ((A i).endpointTerminalLimitMetric (P i)).metric) y
    (metricAlgebraicCurvatureTensorAt (scaleMetric ((A i).flow.scalar (s i) (x i).val) (hQpos i)
      ((A i).endpointTerminalLimitMetric (P i)).metric) y)
    (Perelman.rescalePinchingFunction ((A i).flow.scalar (s i) (x i).val) Phi
      (metricScalarAt (scaleMetric ((A i).flow.scalar (s i) (x i).val) (hQpos i)
        ((A i).endpointTerminalLimitMetric (P i)).metric) y))
  rw [curvatureOperatorLowerBoundAt_scaleMetric_iff, metricScalarAt_scaleMetric,
    Perelman.rescalePinchingFunction]
  simpa only [← mul_assoc, mul_inv_cancel₀ (hQpos i).ne', one_mul] using hp

/-- consumer：原 `Necks:413` 由窗口版推回（`c i = a i`，丢 guard）。 -/
example : type_of%
    @metricRm04StandardAt_nonneg_of_normalized_terminal_pinching.{u} := by
  intro P a s A x hQ Phi hPhi hpinch f Pl F M hcanonical hQlim
  exact metricRm04StandardAt_nonneg_of_normalized_terminal_pinching_window_P6WA P a s A a
    (fun i => (A i).lt) x hQ hPhi (fun i t ht x => hpinch i t ht.1 x) Pl F M hcanonical hQlim

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
