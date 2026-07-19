import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.HeatProbeEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow
namespace Evolution
namespace SolutionHeatProbeEnergy

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


theorem heatOneForm_normSq_integral_hasDerivAt_solution
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
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
                metricRicciAt (I := I) (S.family.metric (t₀ : Real)) x
                  (vec2
                    (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x))
                    (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x)))
              - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family
                    S.toRealizedCandidate.ricci (t₀ : Real) x
                  * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x))
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
      (t₀ : Real) := by
  refine heatOneForm_normSq_integral_hasDerivAt_ricciFlow
    (S := S.toRealizedCandidate)
    (isRealizedRicciFlowSolutionOn_of_isSolutionOn (I := I) hS)
    (fun t x => metricRicciAt (I := I) (S.family.metric t) x)
    ?_ h nablaH nabla2H hProbe t₀
  intro t x X Y
  rfl


theorem heatOneForm_gradNormSq_integral_hasDerivAt_solution
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
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
      (t₀ : Real) := by
  refine heatOneForm_gradNormSq_integral_hasDerivAt_ricciFlow
    (S := S.toRealizedCandidate)
    (isRealizedRicciFlowSolutionOn_of_isSolutionOn (I := I) hS)
    (fun t => metricRicci (I := I) (S.family.metric t))
    ?_
    (fun t x => totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
      (S.family.connection t) (metricRicci (I := I) (S.family.metric t)) x)
    h nablaH nabla2H
    ?_
    hProbe t₀
  · intro t x X Y
    rw [metricRicci_apply]
    rfl
  · intro t x X Y Z
    have hcons : Fin.cons (X x) (vec2 Y Z) = vec3 (X x) Y Z := by
      funext a
      fin_cases a <;> rfl
    rw [← hcons]
    exact totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
      (S.family.connection (t : Real)) X
      (metricRicci (I := I) (S.family.metric (t : Real))) x (vec2 Y Z)


set_option linter.unusedVariables false in
theorem isSolutionOn_of_shortTimeExistence_output
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {T : Real} (hT : (0 : Real) < T)
    (g₀ : SmoothRiemannianMetric I M)
    (g_fam : Real -> SmoothRiemannianMetric I M)
    (hInit : g_fam 0 = g₀)
    (hGram : forall (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.Ico (0 : Real) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hDeriv : ∀ t ∈ Set.Ico (0 : Real) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g_fam s).inner x v w)
        ((-2 : Real) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam t) x v w)
        (Set.Ici 0) t) :
    IsSolutionOn (I := I) (M := M)
      (D := RealTimeInterval.closedOpen 0 T hT)
      (⟨⟨g_fam⟩⟩ : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) := by
  sorry


theorem heatOneForm_normSq_integral_hasDerivAt_shortTimeExistence
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {T : Real} (hT : (0 : Real) < T)
    (g₀ : SmoothRiemannianMetric I M)
    (g_fam : Real -> SmoothRiemannianMetric I M)
    (hInit : g_fam 0 = g₀)
    (hGram : forall (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.Ico (0 : Real) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hDeriv : ∀ t ∈ Set.Ico (0 : Real) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g_fam s).inner x v w)
        ((-2 : Real) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam t) x v w)
        (Set.Ici 0) t)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hProbe : IsHeatOneFormOn (I := I)
      (⟨⟨g_fam⟩⟩ : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)).family
      h nablaH nabla2H)
    (t₀ : RealTimeInterval.RegularTime (RealTimeInterval.closedOpen 0 T hT)) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I) (g_fam s) x 1 (h s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M)
            (⟨⟨g_fam⟩⟩ : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)).family s))
      ((-2 : Real) *
          (∫ x, normSq0S (I := I) (g_fam (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)
            ∂(volumeMeasureFamilyOn (I := I) (M := M)
              (⟨⟨g_fam⟩⟩ : SolutionOn (I := I) (M := M)
                (RealTimeInterval.closedOpen 0 T hT)).family (t₀ : Real)))
        + ∫ x,
            ((2 : Real) *
                metricRicciAt (I := I) (g_fam (t₀ : Real)) x
                  (vec2
                    (cotangentSharp (I := I) (g_fam (t₀ : Real)) x (h (t₀ : Real) x))
                    (cotangentSharp (I := I) (g_fam (t₀ : Real)) x (h (t₀ : Real) x)))
              - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M)
                    (⟨⟨g_fam⟩⟩ : SolutionOn (I := I) (M := M)
                      (RealTimeInterval.closedOpen 0 T hT)).family
                    (⟨⟨g_fam⟩⟩ : SolutionOn (I := I) (M := M)
                      (RealTimeInterval.closedOpen 0 T hT)).toRealizedCandidate.ricci
                    (t₀ : Real) x
                  * normSq0S (I := I) (g_fam (t₀ : Real)) x 1 (h (t₀ : Real) x))
          ∂(volumeMeasureFamilyOn (I := I) (M := M)
            (⟨⟨g_fam⟩⟩ : SolutionOn (I := I) (M := M)
              (RealTimeInterval.closedOpen 0 T hT)).family (t₀ : Real)))
      (t₀ : Real) := by
  exact heatOneForm_normSq_integral_hasDerivAt_solution
    (S := (⟨⟨g_fam⟩⟩ : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)))
    (isSolutionOn_of_shortTimeExistence_output hT g₀ g_fam hInit hGram hDeriv)
    h nablaH nabla2H hProbe t₀

end SolutionHeatProbeEnergy
end Evolution
end DifferentialGeometry.PDE.RicciFlow
