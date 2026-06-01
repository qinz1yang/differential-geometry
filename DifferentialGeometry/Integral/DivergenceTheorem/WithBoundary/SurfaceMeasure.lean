import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InducedMetric
import DifferentialGeometry.Integral.Measure.Invariance
import DifferentialGeometry.Integral.Measure.Properties

/-!
# Surface measure on the boundary of a Riemannian manifold-with-boundary

Given a smooth manifold `M` modelled on `(E, H, I)` with `[hI : HasSmoothBoundary E H I]`,
and a smooth Riemannian metric `g` on the tangent bundle of `M`, this file constructs
the *surface measure* on the boundary submanifold `BoundaryManifold I M` as the
Riemannian volume measure of the induced (pull-back) metric `inducedMetric g`.

## Main definitions

* `surfaceMeasure g` — the Riemannian volume measure of `inducedMetric g`,
  as a `MeasureTheory.Measure (BoundaryManifold I M)`.

## Main results

* `surfaceMeasure_isOpenPosMeasure`,
  `surfaceMeasure_sigmaFinite`,
  `surfaceMeasure_isLocallyFiniteMeasure`,
  `surfaceMeasure_isFiniteMeasureOnCompacts` — direct propagation of the
  corresponding `riemannianVolumeMeasure_*` properties through `inducedMetric`.
* `surfaceMeasure_eq_zero_of_boundaryless` — when the ambient model `I` is itself
  boundaryless, `BoundaryManifold I M` is empty, so the surface measure vanishes.

## Implementation notes

The boundary submanifold inherits the typeclass instances needed by
`riemannianVolumeMeasure`:

* `T2Space (BoundaryManifold I M)` — `BoundaryManifold.instT2Space`.
* `SigmaCompactSpace (BoundaryManifold I M)` — `BoundaryManifold.instSigmaCompactSpace`
  (uses closedness of the boundary in a smooth manifold).
* `ChartedSpace hI.boundaryH (BoundaryManifold I M)` — `BoundaryManifold.chartedSpace`.
* `IsManifold hI.boundaryI ∞ (BoundaryManifold I M)` — `BoundaryManifold.isManifold`.

The boundary model space `hI.boundaryE` carries `[NormedAddCommGroup _]`,
`[NormedSpace ℝ _]`, `[FiniteDimensional ℝ _]` from the typeclass fields; the latter
is definitionally `Module.Finite ℝ _`.
-/

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace (BoundaryManifold I M) :=
  borel (BoundaryManifold I M)
private local instance : BorelSpace (BoundaryManifold I M) := ⟨rfl⟩

/-- Surface measure on the boundary of a Riemannian manifold-with-boundary.

Constructed as the Riemannian volume measure of the metric induced on the
boundary submanifold via the boundary inclusion. The boundary submanifold
inherits `T2Space`, `SigmaCompactSpace`, and `IsManifold` from the ambient
manifold; `riemannianVolumeMeasure` then applies directly to the induced
metric. -/
noncomputable def surfaceMeasure
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    MeasureTheory.Measure (BoundaryManifold I M) :=
  Measure.riemannianVolumeMeasure
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

/-- Unfolding lemma: the surface measure is the Riemannian volume measure of the
induced metric on the boundary submanifold. -/
lemma surfaceMeasure_def
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    surfaceMeasure (I := I) (M := M) g =
      Measure.riemannianVolumeMeasure
        (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g) := rfl

/-- The surface measure is positive on nonempty open subsets of the boundary. -/
theorem surfaceMeasure_isOpenPosMeasure
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    (surfaceMeasure (I := I) (M := M) g).IsOpenPosMeasure := by
  rw [surfaceMeasure_def]
  exact Measure.riemannianVolumeMeasure_isOpenPosMeasure
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

/-- The surface measure is σ-finite. -/
theorem surfaceMeasure_sigmaFinite
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    SigmaFinite (surfaceMeasure (I := I) (M := M) g) := by
  rw [surfaceMeasure_def]
  exact Measure.riemannianVolumeMeasure_sigmaFinite
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

/-- The surface measure is locally finite. -/
theorem surfaceMeasure_isLocallyFiniteMeasure
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    IsLocallyFiniteMeasure (surfaceMeasure (I := I) (M := M) g) := by
  rw [surfaceMeasure_def]
  exact Measure.riemannianVolumeMeasure_isLocallyFiniteMeasure
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

/-- The surface measure is finite on compact subsets of the boundary. -/
theorem surfaceMeasure_isFiniteMeasureOnCompacts
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    IsFiniteMeasureOnCompacts (surfaceMeasure (I := I) (M := M) g) := by
  rw [surfaceMeasure_def]
  exact Measure.riemannianVolumeMeasure_isFiniteMeasureOnCompacts
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

/-- When the ambient model `I` is boundaryless, the boundary submanifold
`BoundaryManifold I M` is empty and the surface measure vanishes. -/
theorem surfaceMeasure_eq_zero_of_boundaryless
    [I.Boundaryless] [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    surfaceMeasure (I := I) (M := M) g = 0 := by
  haveI : IsEmpty hI.boundaryH :=
    HasSmoothBoundary.boundaryH_isEmpty_of_boundaryless I
  haveI : IsEmpty (BoundaryManifold I M) :=
    BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
  exact MeasureTheory.Measure.eq_zero_of_isEmpty _

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
