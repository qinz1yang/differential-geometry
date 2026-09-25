import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowScalarBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower

noncomputable section
open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩
private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      (standardCapWindow D).isOpen)

theorem exists_presented_cap_scalar_lower_bound_of_canonical_window
    (D : ℝ) (hD : StandardCap.transitionEnd < D) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {m : ℕ} {ε : ℝ}, ε ≤ ε₀ → 2 ≤ m →
        ∀ {b : E.RetainedBoundaryIndex}
          (S : E.PresentedStaticCap fixed D m ε b), S.hasCanonicalWindow →
          ∀ z : ThreeBall,
            S.neck.scale / 2 ≤ metricScalarAt S.witness.metric (S.witness.cap z) := by
  obtain ⟨ε₀, C, hε₀, _, hbound⟩ :=
    StandardCap.exists_uniform_window_scalar_bounds_of_metric_close D StandardCap.transitionEnd
      (hD.trans (lt_add_one D))
  refine ⟨ε₀, hε₀, ?_⟩
  intro P Q a s E fixed m ε hε hm b S hcanonical z
  obtain ⟨x₀, δ, k, d, w, _, hinner, hcap⟩ := hcanonical
  obtain ⟨x, hx, hpoint⟩ := hcap z
  have hsmall := w.properties.window_close
  change metricDerivENormSupOn
    {y : standardCapWindow D | (riemannianEDistOf StandardCap.metric 0 y.val).toReal < D} m
    w.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at hsmall
  simp only [StandardCap.distance_zero] at hsmall
  have hrestrict := metricDerivENormSupOn_mono
    (show {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd} ⊆
      {y : standardCapWindow D | ‖y.val‖ < D} from fun y hy => hy.trans_lt hD)
    hm w.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D))
  have hscalar := (hbound w.windowMetric
    (hrestrict.trans_lt (hsmall.trans_le (ENNReal.ofReal_le_ofReal hε))) x hx).1
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ S.window :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv S.window
      S.window_smooth.contMDiff
      (fun p => (S.window_smooth.isImmersion.isImmersionAt p).injective_mfderiv (by simp)) rfl
  have heq := (curvature_of_injective_local_isometry w.windowMetric
    (scaleMetric S.neck.scale S.neck.scale_pos E.outputMetric) S.window hlocal
    S.window_smooth.isEmbedding.injective (fun y v z => by
      rw [scaleMetric_inner]
      exact hinner y v z) x).1
  rw [metricScalarAt_scaleMetric] at heq
  have hnormalized : S.neck.scale * metricScalarAt w.windowMetric x =
      metricScalarAt E.outputMetric (S.window x) := by
    rw [heq, ← mul_assoc, mul_inv_cancel₀ S.neck.scale_pos.ne', one_mul]
  have hlower := mul_le_mul_of_nonneg_left hscalar.le S.neck.scale_pos.le
  rw [hnormalized, hpoint, ← S.scalar_eq E] at hlower
  simpa only [div_eq_mul_inv, one_mul] using hlower

theorem exists_uniform_presented_cap_scalar_abs_bound_of_canonical_window :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ},
        StandardCap.transitionEnd < D → ε ≤ 1 / 2 → 2 ≤ m →
        ∀ {b : E.RetainedBoundaryIndex}
          (S : E.PresentedStaticCap fixed D m ε b), S.hasCanonicalWindow →
          ∀ z : ThreeBall,
            |metricScalarAt S.witness.metric (S.witness.cap z)| ≤ C * S.neck.scale := by
  obtain ⟨C, hC, hbound⟩ := StandardCap.exists_uniform_window_image_scalar_bound_of_scaled_pullback
  refine ⟨C, hC, ?_⟩
  intro P Q a s E fixed D ε m hD hε hm b S hcanonical z
  obtain ⟨x₀, δ, k, d, w, _, hinner, hcap⟩ := hcanonical
  obtain ⟨x, hx, hpoint⟩ := hcap z
  have hscalar := hbound w hε hm E.outputMetric S.window S.window_smooth
    S.neck.scale S.neck.scale_pos hinner x (hx.trans_lt hD)
  rw [hpoint, ← S.scalar_eq E] at hscalar
  exact hscalar

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
