import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section
open Bundle Manifold Set Filter MeasureTheory Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

theorem smooth_critical_values_null {m n : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin m))) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) :
    volume (F '' {x | x ∈ U ∧ ¬Function.Surjective (fderiv ℝ F x)}) = 0 := by
  sorry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def immersionSecondFundamental {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (x : U) (X Y : EuclideanSpace ℝ (Fin m)) : TangentSpace I (F x) := by
  have a : TangentSpace I (F x) := by
    simpa only [zero_smul, add_zero] using
      covDerivAlong g (fun t : ℝ => F ((x : EuclideanSpace ℝ (Fin m)) + t • X))
        (fun t => mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F
          ((x : EuclideanSpace ℝ (Fin m)) + t • X) Y) 0
  exact a - mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x
    ((metricCov h) (fun _ : U => Y) x X)

theorem local_immersion_gauss [I.Boundaryless] [T2Space M]
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (himm : ∀ x ∈ U, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x))
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (hinduced : ∀ (x : U) (X Y : EuclideanSpace ℝ (Fin m)),
      h.inner x X Y = g.inner (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x X)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Y))
    (x : U) (X Y Z W : EuclideanSpace ℝ (Fin m)) :
    metricRm04StandardAt h x X Y Z W =
      metricRm04StandardAt g (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x X)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Z)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x W) +
      g.inner (F x) (immersionSecondFundamental U F g h x X W)
        (immersionSecondFundamental U F g h x Y Z) -
      g.inner (F x) (immersionSecondFundamental U F g h x X Z)
        (immersionSecondFundamental U F g h x Y W) := by
  sorry

theorem smooth_manifold_critical_values_null_in_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SecondCountableTopology M]
    {n : ℕ} {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H'} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    (F : M → N) (S : Set M) (hS : IsOpen S) (hF : ContMDiffOn I J ∞ F S)
    (q : N) :
    volume ((extChartAt J q ∘ F) ''
      {x | x ∈ S ∧ F x ∈ (chartAt H' q).source ∧
        ¬Function.Surjective (mfderiv I J F x)}) = 0 := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
