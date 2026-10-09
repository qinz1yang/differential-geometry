import DifferentialGeometry.Geometry.Thurston.Models
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance

set_option autoImplicit false
noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def CoordinateModelAtlas (g : SmoothRiemannianMetric I M) (k : CoordinateModel) : Prop :=
  ∀ x : M, ∃ e : PartialDiffeomorph (𝓡 3) I ModelCoordinates M ∞,
    x ∈ e.target ∧ ∀ p ∈ e.source, ∀ v w : TangentSpace (𝓡 3) p,
      g.inner (e p) (mfderiv (𝓡 3) I e p v) (mfderiv (𝓡 3) I e p w) =
        coordinateInner k p v w

def HasThurstonAtlas (g : SmoothRiemannianMetric I M) : ThurstonModel → Prop
  | .spherical => ModelAtlas g sphericalModelMetric
  | .euclidean => ModelAtlas g euclideanModelMetric
  | .hyperbolic => CoordinateModelAtlas g .hyperbolic
  | .sphericalProduct => ModelAtlas g sphericalProductModelMetric
  | .hyperbolicProduct => CoordinateModelAtlas g .hyperbolicProduct
  | .universalSL2 => CoordinateModelAtlas g .universalSL2
  | .nil => CoordinateModelAtlas g .nil
  | .sol => CoordinateModelAtlas g .sol

def LocallyHomogeneousMetric (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ x y : M, ∃ e : PartialDiffeomorph I I M M ∞, x ∈ e.source ∧ e x = y ∧
    ∀ p ∈ e.source, ∀ v w : TangentSpace I p,
      g.inner (e p) (mfderiv I I e p v) (mfderiv I I e p w) = g.inner p v w

def HomogeneousMetric (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ x y : M, ∃ e : M ≃ₘ⟮I, I⟯ M, e x = y ∧
    ∀ p : M, ∀ v w : TangentSpace I p,
      g.inner (e p) (mfderiv I I e p v) (mfderiv I I e p w) = g.inner p v w

omit [FiniteDimensional ℝ E] in
theorem HomogeneousMetric.locallyHomogeneous {g : SmoothRiemannianMetric I M}
    (h : HomogeneousMetric g) : LocallyHomogeneousMetric g := by
  intro x y
  obtain ⟨e, he, hg⟩ := h x y
  exact ⟨e.toPartialDiffeomorph, Set.mem_univ x, he, fun p _ v w => hg p v w⟩

omit [FiniteDimensional ℝ E] in

theorem coordinateModelAtlas_iff_modelAtlas (g : SmoothRiemannianMetric I M)
    (k : CoordinateModel) (h : SmoothRiemannianMetric (𝓡 3) ModelCoordinates)
    (hh : ∀ p v w, h.inner p v w = coordinateInner k p v w) :
    CoordinateModelAtlas g k ↔ ModelAtlas g h := by
  simp only [CoordinateModelAtlas, ModelAtlas, hh]

structure GeometricStructure (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] where
  model : ThurstonModel
  metric : SmoothRiemannianMetric I M
  complete : RiemannianMetricComplete metric
  atlas : HasThurstonAtlas metric model
  hyperbolic_finite_volume : model = .hyperbolic →
    Integral.Measure.riemannianVolumeMeasure I M metric Set.univ < ⊤

end GC.Geometry
