import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionHeatProbeEnergy
import DifferentialGeometry.Analysis.Parabolic.OneFormHodgeHeat
import DifferentialGeometry.Geometry.Surface.CurvatureEnergyIdentity
import DifferentialGeometry.Geometry.Surface.OneFormHodgeLaplacianTwoDim

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


private theorem toRS0_sub' {s : ℕ} {z : M}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z) :
    Tensor0SSpace.toRS0 (A - B) = Tensor0SSpace.toRS0 A - Tensor0SSpace.toRS0 B := by
  apply ContinuousLinearMap.ext
  intro c
  rw [Tensor0SSpace.toRS0_apply, ContinuousLinearMap.sub_apply,
    Tensor0SSpace.toRS0_apply, Tensor0SSpace.toRS0_apply, smul_sub]

private theorem toRS0_smul' {s : ℕ} {z : M} (c : Real)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z) :
    Tensor0SSpace.toRS0 (c • A) = c • Tensor0SSpace.toRS0 A := by
  apply ContinuousLinearMap.ext
  intro Dv
  rw [Tensor0SSpace.toRS0_apply, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toRS0_apply, smul_comm]

private theorem inner0S_sub_left'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s (A - B) C =
      inner0S (I := I) g x s A C - inner0S (I := I) g x s B C := by
  let Dt := tensor0SMetricData (I := I) g x s
  change Dt.flat (A - B) C = Dt.flat A C - Dt.flat B C
  rw [map_sub]
  rfl


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
  classical
  have hSR := isRealizedRicciFlowSolutionOn_of_isSolutionOn (I := I) hS
  set W : SmoothCcTensor (S.family.metric (t₀ : Real)) 0 1 :=
    { toSection := (h (t₀ : Real)).toTensorRSField
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW_def
  have hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h (t₀ : Real) y) := fun _ => rfl
  have hbridge : ∀ y : M,
      (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W).toFun y =
          TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaH (t₀ : Real) y))
        ∧ (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W).toFun y =
          TensorRSSpace.toModel
            (Tensor0SSpace.toRS0
              (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                (nabla2H (t₀ : Real) y))) :=
    fun y => oneForm_wrapped_realizes (I := I) (M := M)
      S.toRealizedCandidate hSR h nablaH nabla2H hProbe.realizes t₀ W hW y
  set LW : SmoothCcTensor (S.family.metric (t₀ : Real)) 0 1 :=
    rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W with hLW_def
  set KW : SmoothCcTensor (S.family.metric (t₀ : Real)) 0 1 :=
    TensorSpectral.scalarSmul (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
      ⟨gaussCurvature (I := I) (S.family.metric (t₀ : Real)),
        gaussCurvature_contMDiff (I := I) (M := M) (S.family.metric (t₀ : Real))⟩ W
    with hKW_def
  have hLWfun : ∀ y : M, LW.toFun y =
      TensorRSSpace.toModel
        (Tensor0SSpace.toRS0
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) y))) := fun y => (hbridge y).2
  have hLWs : ∀ y : M, LW.toSection y =
      Tensor0SSpace.toRS0
        (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
          (nabla2H (t₀ : Real) y)) := by
    intro y
    have hb := hLWfun y
    rw [SmoothCcTensor.toFun_apply] at hb
    exact TensorRSSpace.toModel_injective hb
  have hKWs : ∀ y : M, KW.toSection y =
      gaussCurvature (I := I) (S.family.metric (t₀ : Real)) y •
        Tensor0SSpace.toRS0 (h (t₀ : Real) y) := by
    intro y
    rw [hKW_def, TensorSpectral.scalarSmul_toSection_apply, hW y]
    rfl
  have hKWfun : ∀ y : M, KW.toFun y =
      TensorRSSpace.toModel
        (Tensor0SSpace.toRS0
          (gaussCurvature (I := I) (S.family.metric (t₀ : Real)) y • h (t₀ : Real) y)) := by
    intro y
    rw [SmoothCcTensor.toFun_apply, hKWs y, toRS0_smul']
  have hphi : ∀ y : M,
      -(oneFormHodgeLaplacianAt (I := I) (S.family.metric (t₀ : Real))
          (nablaH (t₀ : Real)) (nabla2H (t₀ : Real)) y)
        = roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) y)
          - gaussCurvature (I := I) (S.family.metric (t₀ : Real)) y • (h (t₀ : Real) y) :=
    neg_oneFormHodgeLaplacian_eq_roughLap_sub_gauss_smul_twoDim (I := I) hdim
      (S.family.metric (t₀ : Real)) (h (t₀ : Real)) (nablaH (t₀ : Real)) (nabla2H (t₀ : Real))
      (fun y => hProbe.realizes (RealTimeInterval.regularToFlow t₀) y)
  have hPhi : ∀ y : M, (LW - KW).toSection y =
      Tensor0SSpace.toRS0
        (-(oneFormHodgeLaplacianAt (I := I) (S.family.metric (t₀ : Real))
            (nablaH (t₀ : Real)) (nabla2H (t₀ : Real)) y)) := by
    intro y
    have hstep : (LW - KW).toSection y = LW.toSection y - KW.toSection y := by
      rw [SmoothCcTensor.toSection_sub]
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [hstep, hLWs y, hKWs y, hphi y, toRS0_sub', toRS0_smul']
  have hIntA : MeasureTheory.Integrable
      (fun x : M => normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
        (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
          (nabla2H (t₀ : Real) x)))
      (volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)) := by
    rw [volumeMeasureFamilyOn_eq]
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) LW LW).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [hLWfun x, ← normSq0S_eq_tensorInnerPointwise_toRS0]
  have hIntB : MeasureTheory.Integrable
      (fun x : M => gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
        inner0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) x)))
      (volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)) := by
    rw [volumeMeasureFamilyOn_eq]
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) KW LW).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [hKWfun x, hLWfun x, inner_toRS0, ← inner0S_eq_covariantTensorInnerPointwise,
      inner0S_smul_left]
  have hIpe :
      (∫ x, inner0S (I := I) (S.family.metric (t₀ : Real)) x 1
          (-(oneFormHodgeLaplacianAt (I := I) (S.family.metric (t₀ : Real))
              (nablaH (t₀ : Real)) (nabla2H (t₀ : Real)) x))
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) x))
        ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
      = (∫ x, normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
            (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
              (nabla2H (t₀ : Real) x))
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
        - (∫ x, gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
              inner0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
                (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                  (nabla2H (t₀ : Real) x))
            ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real))) := by
    rw [← MeasureTheory.integral_sub hIntA hIntB]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [hphi x, inner0S_sub_left', inner0S_smul_left, normSq0S_eq_inner]
  refine (evolvingOneForm_gradNormSq_integral_hasDerivAt_ricciFlow (I := I) (M := M)
    (S := S.toRealizedCandidate) hSR
    (fun t => metricRicci (I := I) (S.family.metric t)) ?_
    (fun t x => totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
      (S.family.connection t) (metricRicci (I := I) (S.family.metric t)) x)
    h nablaH nabla2H
    (fun t x =>
      -(oneFormHodgeLaplacianAt (I := I) (S.family.metric t) (nablaH t) (nabla2H t) x))
    ?_ hProbe.toEvolving t₀ (LW - KW) hPhi).congr_deriv ?_
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
  · simp only [SolutionOn.toRealizedCandidate_family]
    rw [hIpe]
    ring


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
