import DifferentialGeometry.Geometry.Measure.Area.LeastAreaAnnulus
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaComponent
import DifferentialGeometry.Topology.LoopSpace.RegularDerivativeBounds
import DifferentialGeometry.Topology.LoopSpace.RegularContractible



noncomputable section

open Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]



def regularContractibleToLipschitz (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : regularContractibleLoop E M) : lipschitzContractibleLoop g :=
  ⟨regularContractibleLoopInclusion γ, regularLoop_riemannian_lipschitz g γ.val⟩



def regularLeastArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : regularContractibleLoop E M) : ℝ :=
  leastSpanningArea g (regularContractibleToLipschitz g γ)

theorem regularLeastArea_nonneg
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : regularContractibleLoop E M) :
    0 ≤ regularLeastArea g γ :=
  leastSpanningArea_nonneg_of_nullhomotopic g (regularContractibleToLipschitz g γ)

theorem regularLeastArea_constant [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    regularLeastArea g (regularContractibleLoopConst q) = 0 := by
  have heq : regularContractibleToLipschitz g (regularContractibleLoopConst q) =
      constantLipschitzContractibleLoop g q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [regularLeastArea, heq, leastSpanningArea_constant]

end DifferentialGeometry.Geometry
