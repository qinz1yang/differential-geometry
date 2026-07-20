import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionHeatProbeEnergy
import DifferentialGeometry.Analysis.Parabolic.OneFormHodgeHeat
import DifferentialGeometry.Geometry.Surface.CurvatureEnergyIdentity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow
namespace Evolution
namespace SolutionHodgeProbeEnergy

open MeasureTheory
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic
open Bundle Tensor0SBundle
open Tensor0SNabla
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Evolution.HeatProbeEnergy
open scoped Manifold ContDiff BigOperators Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem hodgeHeatOneForm_gradNormSq_integral_hasDerivAt_solution
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (hdim : Module.finrank Real E = 2)
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hProbe : IsHodgeHeatOneFormOn (I := I) S.family h nablaH nabla2H)
    (t₀ : RealTimeInterval.RegularTime D) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family s))
      (((-2 : Real) *
          (∫ x, normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
              (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                (nabla2H (t₀ : Real) x))
            ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
        + ∫ x,
            (ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x
                (metricRicci (I := I) (S.family.metric (t₀ : Real)) x) (nablaH (t₀ : Real) x)
              + (2 : Real) *
                  inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
                    (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
                      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
                        (S.family.connection (t₀ : Real))
                        (metricRicci (I := I) (S.family.metric (t₀ : Real))) x)
                      (h (t₀ : Real) x))
                    (nablaH (t₀ : Real) x)
              - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family
                    S.toRealizedCandidate.ricci (t₀ : Real) x
                  * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
        + (2 : Real) *
            (∫ x, gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
                inner0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
                  (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                    (nabla2H (t₀ : Real) x))
              ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real))))
      (t₀ : Real) := by
  sorry


theorem hodgeHeatOneForm_gradNormSq_integral_hasDerivAt_curvature_solution
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (hdim : Module.finrank Real E = 2)
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hProbe : IsHodgeHeatOneFormOn (I := I) S.family h nablaH nabla2H)
    (t₀ : RealTimeInterval.RegularTime D) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family s))
      (-((2 : Real) *
            (∫ x, normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
                (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                  (nabla2H (t₀ : Real) x))
              ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
          - (2 : Real) *
              (∫ x, gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
                  normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)
                ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
          + (4 : Real) *
              (∫ x, gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
                  normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2
                    (ahlforsOperator (I := I) (S.family.metric (t₀ : Real))
                      (nablaH (t₀ : Real) x))
                ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
          + (2 : Real) *
              (∫ x, gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x ^ 2 *
                  normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
                ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))))
      (t₀ : Real) := by
  sorry

end SolutionHodgeProbeEnergy
end Evolution
end DifferentialGeometry.PDE.RicciFlow
