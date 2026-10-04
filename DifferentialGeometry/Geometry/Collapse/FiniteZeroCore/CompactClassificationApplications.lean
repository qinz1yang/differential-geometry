import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CompactClassification
import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeSectionalCarrier

/-!
# Consumers of LFR53

* Carrier form: on a compact connected oriented carrier with empty boundary, a `C^n` metric
  (`2 ≤ n`) with finite-order `sec ≥ 0` yields a spherical, `S² × ℝ` or Euclidean geometric
  structure on the same carrier (LFR50 carrier form + U1 carrier form). This replaces the
  `example` of `FiniteZeroCore/Applications.lean`, whose binder `hU1` is now the proved U1.
* Geometrization: a closed connected oriented `3`-manifold with such a finite metric geometrizes.
* The smooth case through the finite route: a smooth metric with `sec ≥ 0`, regarded as a `C^∞`
  finite metric, is classified by the row form.
* The row in the `C²` case.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **LFR53, carrier form.** A compact connected oriented carrier with empty boundary and a `C^n`
metric (`2 ≤ n`) of nonnegative finite-order sectional curvature carries a spherical, `S² × ℝ` or
Euclidean geometric structure. -/
theorem exists_geometricStructure_of_finite_metric_of_boundary_eq_empty
    (W : GC.Endpoint.CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (hclosed : W.model.boundary W.Carrier = ∅) {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (g : Bundle.ContMDiffRiemannianMetric W.model n E3 (TangentSpace W.model : W.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace W.model x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
      G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨h, hh⟩ :=
    W.exists_smooth_sectional_nonneg_of_finite_metric_of_boundary_eq_empty hclosed hn g hsec
  exact GC.Geometry.closed_nonnegative_sectional_classification_unconditional W h hclosed hh

private instance finrankThreeNeZero' : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Geometrization consumer.** A closed connected oriented `3`-manifold with a `C^n` metric
(`2 ≤ n`) of nonnegative finite-order sectional curvature geometrizes. -/
theorem geometrizes_of_finite_metric_sectional_nonneg (P : ConnectedClosedOrientedManifold.{u} 3)
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 3) n E3 (TangentSpace (𝓡 3) : P.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace (𝓡 3) x), 0 ≤ g.sectionalCurvature x v w) :
    GC.Endpoint.Geometrizes P := by
  obtain ⟨h, hh⟩ :=
    MetricSmoothing.exists_smooth_sectional_nonneg_of_finite_metric (by simp) hn g hsec
  exact GC.Geometry.geometrizes_of_sectional_nonneg_unconditional P h hh

/-- **The row in the `C²` case.** -/
theorem isCompactNonnegativeType_of_metric2 (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 3) (2 : ℕ∞ω) E3
      (TangentSpace (𝓡 3) : P.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace (𝓡 3) x), 0 ≤ g.sectionalCurvature x v w) :
    IsCompactNonnegativeType P :=
  isCompactNonnegativeType_of_finite_metric P le_rfl g hsec

/-- **Smooth case through the finite route.** A smooth metric with `sec ≥ 0`, regarded as a `C^∞`
metric, is classified by the row form. -/
theorem isCompactNonnegativeType_of_smooth_via_finite (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) P.Carrier) (hsec : Riemannian.SectionalBoundedBelow g 0) :
    IsCompactNonnegativeType P :=
  isCompactNonnegativeType_of_finite_metric P (by simp) g
    (MetricSmoothing.sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero g hsec)

end DifferentialGeometry.Geometry.Collapse
