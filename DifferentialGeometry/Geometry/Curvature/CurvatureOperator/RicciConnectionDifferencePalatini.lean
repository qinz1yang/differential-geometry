import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifferenceCurvature
import DifferentialGeometry.Geometry.Connection.ConnectionDifference
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifference_eq_difference (g₀ g₁ : SmoothRiemannianMetric I M) :
    connectionDifference (I := I) g₁ g₀ =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) := rfl
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
def covDerivConnectionDifference (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Y Z x
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] [T2Space M] in
theorem covDerivConnectionDifference_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    covDerivConnectionDifference (I := I) g₀ g₁ X Y Z x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Y Z x := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_sub_eq_connectionDifference_palatini (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnectionDifference (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x
              - covDerivConnectionDifference (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x w) x)
            + (connectionDifference (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - connectionDifference (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x v x))) i :=
  ricciTensor_sub_eq_basisSum_difference (I := I) g₀ g₁ x v w

end Curvature
end Geometry
end DifferentialGeometry
