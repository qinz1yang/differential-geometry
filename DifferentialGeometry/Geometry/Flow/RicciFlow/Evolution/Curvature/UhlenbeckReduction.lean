import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Variation
import DifferentialGeometry.Geometry.Curvature.QuadraticContraction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Frame

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators


section Solution

open Bundle DifferentialGeometry.Tensor0SBundle Set
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
theorem rm04Var_eq_uhl
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (Rm04 : FourComp M (CoordinateIdx (𝕜 := Real) E))
    (ricciOneUp : MatrixComp M (CoordinateIdx (𝕜 := Real) E))
    (nabla2Ric :
      Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
        CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (nabla2Rm :
      Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
        CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
        CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (hsym : Rm04Symm (Rm04 t x₀))
    (hgi : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      coordInv (I := I) S x₀ t x₀ a b = coordInv (I := I) S x₀ t x₀ b a)
    (hricsym : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ a b =
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ b a)
    (hcon : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ a p *
          coordInv (I := I) S x₀ t x₀ p b) = if a = b then 1 else 0)
    (hraise : ∀ a b c d : CoordinateIdx (𝕜 := Real) E,
      DifferentialGeometry.Geometry.Curvature.christoffelCurvCoeffAt
          (I := I) (S.family.connection t) x₀ a b c d =
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          coordInv (I := I) S x₀ t x₀ d q * Rm04 t x₀ a b c q)
    (hRup : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      ricciOneUp t x₀ a b =
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          coordInv (I := I) S x₀ t x₀ b q *
            ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ a q)
    (hcomm : RicCommAt
      (DifferentialGeometry.Geometry.Curvature.christoffelCurvCoeffAt
        (I := I) (S.family.connection t) x₀)
      (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
      (nabla2Ric t x₀))
    (hin : Rm04LapIn (coordInv (I := I) S x₀ t x₀) (Rm04 t x₀)
      (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
      (nabla2Ric t x₀) (nabla2Rm t x₀))
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    rm04VarRHS (I := I) S x₀ nabla2Ric t m
      = rmLap (coordInv (I := I) S x₀ t x₀) (nabla2Rm t x₀) (m 0) (m 1) (m 2) (m 3)
        - 2 * (uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀
                (m 0) (m 1) (m 2) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀
                (m 0) (m 1) (m 3) (m 2)
            + uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀
                (m 0) (m 2) (m 1) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀
                (m 0) (m 3) (m 1) (m 2))
        - riemann04RicciDriftInFrame ricciOneUp Rm04 t x₀ (m 0) (m 1) (m 2) (m 3) := by
  have hb : ∀ a b c d : CoordinateIdx (𝕜 := Real) E,
      uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀ a b c d
        = bComp (coordInv (I := I) S x₀ t x₀) (Rm04 t x₀) a b c d := fun _ _ _ _ => rfl
  have hd : riemann04RicciDriftInFrame ricciOneUp Rm04 t x₀ (m 0) (m 1) (m 2) (m 3)
      = rmDrift (ricciOneUp t x₀) (Rm04 t x₀) (m 0) (m 1) (m 2) (m 3) := rfl
  have hv : rm04VarRHS (I := I) S x₀ nabla2Ric t m
      = rmVar
          (metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
          (coordInv (I := I) S x₀ t x₀)
          (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
          (DifferentialGeometry.Geometry.Curvature.christoffelCurvCoeffAt
            (I := I) (S.family.connection t) x₀)
          (nabla2Ric t x₀) (m 0) (m 1) (m 2) (m 3) := rfl
  rw [hv, hd, hb, hb, hb, hb]
  exact rmVar_eq_uhl
    (metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
    (coordInv (I := I) S x₀ t x₀)
    (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
    (ricciOneUp t x₀)
    (DifferentialGeometry.Geometry.Curvature.christoffelCurvCoeffAt
      (I := I) (S.family.connection t) x₀)
    (Rm04 t x₀) (nabla2Ric t x₀) (nabla2Rm t x₀)
    hsym hgi hricsym hcon hraise hRup hcomm hin (m 0) (m 1) (m 2) (m 3)

end Solution

end DifferentialGeometry.PDE.RicciFlow
