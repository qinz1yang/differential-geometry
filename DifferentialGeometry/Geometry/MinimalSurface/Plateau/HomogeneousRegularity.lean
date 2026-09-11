import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import Mathlib.Analysis.InnerProductSpace.PiL2








noncomputable section

open Bundle Manifold DifferentialGeometry Set
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

abbrev plateauCoordinateSpace := EuclideanSpace ℝ (Fin 3)

def plateauOpenCube : Set plateauCoordinateSpace := {y | ∀ i, |y i| < 1}
def plateauClosedCube : Set plateauCoordinateSpace := {y | ∀ i, |y i| ≤ 1}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


def plateauChartCoefficient (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : OpenPartialHomeomorph plateauCoordinateSpace M) (i j : Fin 3)
    (y : plateauCoordinateSpace) : ℝ :=
  g.inner (ψ y)
    (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y (EuclideanSpace.single i (1 : ℝ)))
    (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y (EuclideanSpace.single j (1 : ℝ)))




def HomogeneouslyRegularMetric (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) : Prop :=
  ∃ m A : ℝ, 0 < m ∧ m ≤ A ∧
    ∃ ψ : M → OpenPartialHomeomorph plateauCoordinateSpace M,
      (∀ p, plateauClosedCube ⊆ (ψ p).source ∧ ψ p 0 = p ∧
        ContMDiffOn 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ∞ (ψ p) (ψ p).source ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, plateauCoordinateSpace) ∞ (ψ p).symm (ψ p).target ∧
        ∀ y ∈ plateauOpenCube, ∀ ξ : plateauCoordinateSpace,
          m * ‖ξ‖ ^ 2 ≤ g.inner (ψ p y)
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) y ξ)
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) y ξ) ∧
          g.inner (ψ p y)
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) y ξ)
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) y ξ) ≤ A * ‖ξ‖ ^ 2) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p i j y, y ∈ plateauOpenCube →
        ‖iteratedFDeriv ℝ k (plateauChartCoefficient g (ψ p) i j) y‖ ≤ C

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def RiemannianMetricComplete [T3Space M] (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) : Prop :=
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  CompleteSpace M

end DifferentialGeometry.Geometry
