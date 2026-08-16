import DifferentialGeometry.Analysis.Convex.PositiveSemidefiniteMatrixCone
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.SemilinearConvex

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Convex
open Set
open scoped Manifold ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {ι : Type*} [Fintype ι]

theorem positiveSemidefiniteMatrix_heat_reaction_mem
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (reaction : Real -> M -> MatrixData ι -> MatrixData ι)
    (u : Real -> M -> MatrixData ι)
    (hsol : IsInnerProductHeatReactionOn
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closed 0 T hT) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T -> ∀ x : M,
      LipschitzWith L (reaction t x))
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T -> ∀ x : M,
      ∀ p : MatrixData ι, p ∈ matPositiveSemidefiniteCone (ι := ι) ->
        ∀ ν : MatrixData ι,
          (∀ q : MatrixData ι, q ∈ matPositiveSemidefiniteCone (ι := ι) ->
            inner Real ν (q - p) ≤ 0) ->
          inner Real ν (reaction t x p) ≤ 0)
    (hinit : ∀ x : M, u 0 x ∈ matPositiveSemidefiniteCone (ι := ι)) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      u t x ∈ matPositiveSemidefiniteCone (ι := ι) := by
  let C : Set (MatrixData ι) := matPositiveSemidefiniteCone (ι := ι)
  exact closed_convex_heat_reaction_mem_of_supporting_normal
    (I := I) (F := MatrixData ι) G hT C
    (by simpa [C] using matPositiveSemidefiniteCone (ι := ι).nonempty)
    (by simpa [C] using matPositiveSemidefiniteCone (ι := ι).isClosed)
    (by simpa [C] using matPositiveSemidefiniteCone (ι := ι).convex)
    reaction u hsol L hL (by simpa [C] using hreaction) (by simpa [C] using hinit)

end DifferentialGeometry.Analysis.Parabolic
