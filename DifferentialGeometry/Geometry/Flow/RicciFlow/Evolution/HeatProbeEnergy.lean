import DifferentialGeometry.Analysis.Parabolic.OneFormHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Volume
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.CotangentRiemannian
import DifferentialGeometry.Geometry.Operator.RoughLaplacian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow
namespace Evolution
namespace HeatProbeEnergy

open MeasureTheory
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic
open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


def ricciSharpEndo (g : SmoothRiemannianMetric I M) (x : M)
    (ricX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    TangentSpace I x →L[Real] TangentSpace I x :=
  (LinearMap.toContinuousLinearMap (cotangentSharpLinear (I := I) g x)).comp
    ((tensor0S_curry (𝕜 := Real) (I := I) 1 x) ricX)


def endoSlotFirst {x : M}
    (A : TangentSpace I x →L[Real] TangentSpace I x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (tensor0S_curry (𝕜 := Real) (I := I) 1 x).symm
    (((tensor0S_curry (𝕜 := Real) (I := I) 1 x) T).comp A)


def endoSlotSecond {x : M}
    (A : TangentSpace I x →L[Real] TangentSpace I x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (endoSlotFirst (I := I) A (T.domDomCongr (Equiv.swap (0 : Fin 2) 1))).domDomCongr
    (Equiv.swap (0 : Fin 2) 1)


def ricciReactionInner (g : SmoothRiemannianMetric I M) (x : M)
    (ricX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) : Real :=
  2 * (inner0S (I := I) g x 2 (endoSlotFirst (I := I) (ricciSharpEndo (I := I) g x ricX) T) T
    + inner0S (I := I) g x 2 (endoSlotSecond (I := I) (ricciSharpEndo (I := I) g x ricX) T) T)


def ricciVariationOneFormReaction (g : SmoothRiemannianMetric I M) (x : M)
    (nablaRicX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (alphaX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  let Hs : TangentSpace I x := cotangentSharp (I := I) g x alphaX
  let term1 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    (tensor0S_curry (𝕜 := Real) (I := I) 2 x (nablaRicX.domDomCongr (finRotate 3))) Hs
  let term2 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    term1.domDomCongr (Equiv.swap (0 : Fin 2) 1)
  let term3 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    (tensor0S_curry (𝕜 := Real) (I := I) 2 x nablaRicX) Hs
  term1 + term2 - term3


abbrev scalarCurvatureFromRicciInVolumeFrameOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (Ric : RicciTensorField (I := I) (M := M) Real) : Real -> M -> Real :=
  fun t =>
    scalarCurvatureFromRicciTraceInFrame (I := I) (Ric t)
      (Volume.volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (Volume.volumeTraceFrame (I := I) (M := M))


theorem heatOneForm_normSq_integral_hasDerivAt_ricciFlow
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : IsRealizedRicciFlowSolutionOn (I := I) S)
    (ric : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hric : forall (t : Real) (x : M) (X Y : TangentSpace I x),
      ric t x (vec2 X Y) = S.ricci t x X Y)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hProbe : IsHeatOneFormOn (I := I) S.family h nablaH nabla2H)
    (t₀ : RealTimeInterval.RegularTime D) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I) (S.family.metric s) x 1 (h s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family s))
      ((-2 : Real) *
          (∫ x, normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)
            ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
        + ∫ x,
            ((2 : Real) *
                ric (t₀ : Real) x
                  (vec2
                    (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x))
                    (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x)))
              - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                    (t₀ : Real) x
                  * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x))
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
      (t₀ : Real) := sorry


theorem heatOneForm_gradNormSq_integral_hasDerivAt_ricciFlow
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : IsRealizedRicciFlowSolutionOn (I := I) S)
    (ricT : Real -> TwoTensorSection (I := I) (M := M))
    (hricT : forall (t : Real) (x : M) (X Y : TangentSpace I x),
      (ricT t) x (vec2 X Y) = S.ricci t x X Y)
    (nablaRic : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hNablaRic : forall t : RealTimeInterval.FlowTime D, forall x : M,
      forall (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
        (Y Z : TangentSpace I x),
        nablaRic (t : Real) x (vec3 (X x) Y Z) =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 (S.family.connection (t : Real)) X (ricT (t : Real)) x (vec2 Y Z))
    (hProbe : IsHeatOneFormOn (I := I) S.family h nablaH nabla2H)
    (t₀ : RealTimeInterval.RegularTime D) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family s))
      ((-2 : Real) *
          (∫ x, normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
              (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                (nabla2H (t₀ : Real) x))
            ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
        + ∫ x,
            (ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x
                ((ricT (t₀ : Real)) x) (nablaH (t₀ : Real) x)
              + (2 : Real) *
                  inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
                    (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
                      (nablaRic (t₀ : Real) x) (h (t₀ : Real) x))
                    (nablaH (t₀ : Real) x)
              - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                    (t₀ : Real) x
                  * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
      (t₀ : Real) := sorry

end HeatProbeEnergy
end Evolution
end DifferentialGeometry.PDE.RicciFlow
