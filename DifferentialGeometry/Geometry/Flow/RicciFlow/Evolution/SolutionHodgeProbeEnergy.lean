import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionHeatProbeEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ReactionTwoDim
import DifferentialGeometry.Analysis.Parabolic.OneFormHodgeHeat
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.WeightedOneFormIBP
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
open DifferentialGeometry.Integral.DivergenceTheorem
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

private theorem inner0S_add_left'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s (A + B) C =
      inner0S (I := I) g x s A C + inner0S (I := I) g x s B C := by
  let Dt := tensor0SMetricData (I := I) g x s
  change Dt.flat (A + B) C = Dt.flat A C + Dt.flat B C
  rw [map_add]
  rfl

private theorem inner0S_symm''
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A B = inner0S (I := I) g x s B A := by
  unfold inner0S MetricFiberData.inner
  exact (tensor0SMetricData (I := I) g x s).symm A B

private theorem inner0S_add_right'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A (B + C) =
      inner0S (I := I) g x s A B + inner0S (I := I) g x s A C := by
  rw [inner0S_symm'' (I := I) g x s A (B + C), inner0S_add_left',
    inner0S_symm'' (I := I) g x s B A, inner0S_symm'' (I := I) g x s C A]

private theorem normSq0S_add_expand'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    normSq0S (I := I) g x s (A + B) =
      normSq0S (I := I) g x s A + 2 * inner0S (I := I) g x s A B
        + normSq0S (I := I) g x s B := by
  rw [normSq0S_eq_inner, inner0S_add_left', inner0S_add_right', inner0S_add_right',
    ← normSq0S_eq_inner, ← normSq0S_eq_inner, inner0S_symm'' (I := I) g x s B A]
  ring

private theorem continuous_inner0S_fields {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Continuous (fun x : M => inner0S (I := I) g x s (A x) (B x)) := by
  have h1 := normSq0S_cont (I := I) g (A + B)
  have h2 := normSq0S_cont (I := I) g A
  have h3 := normSq0S_cont (I := I) g B
  have key : Continuous (fun y : M => (2 : Real)⁻¹ *
      (normSq0S (I := I) g y s ((A + B) y) - normSq0S (I := I) g y s (A y)
        - normSq0S (I := I) g y s (B y))) :=
    continuous_const.mul ((h1.sub h2).sub h3)
  refine key.congr (fun x => ?_)
  have hAB : (A + B) x = A x + B x := by
    rw [ContMDiffSection.coe_add]
    rfl
  rw [hAB, normSq0S_add_expand']
  ring

private theorem covectorProd_eval' {x : M}
    (a b : TangentSpace I x →L[Real] Real)
    (v : Fin 2 → TangentSpace I x) :
    covectorTensorProd0S (I := I) (M := M) a b v = a (v 0) * b (v 1) := by
  unfold covectorTensorProd0S
  change ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      ((a.smulRight b) (v 0))) (fun i : Fin 1 => v i.succ) = a (v 0) * b (v 1)
  have htail : (fun i : Fin 1 => v i.succ) = fun _ : Fin 1 => v 1 := by
    funext i; fin_cases i; rfl
  rw [htail]
  change (a.smulRight b) (v 0) (v 1) = a (v 0) * b (v 1)
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

private def oneFormProd (a b : OneFormSection (I := I) (M := M)) :
    TwoTensorSection (I := I) (M := M) :=
  MultilinearSection.product (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
    (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 1) a b

private theorem oneFormProd_apply
    (a b : OneFormSection (I := I) (M := M)) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    oneFormProd (I := I) a b x v
      = a x (fun _ : Fin 1 => v 0) * b x (fun _ : Fin 1 => v 1) := by
  change Bundle.continuousMultilinearMap.product_fun (a x) (b x) v = _
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  have hl : (v ∘ Fin.castAdd 1) = fun _ : Fin 1 => v 0 := by
    funext i; fin_cases i; rfl
  have hr : (v ∘ Fin.natAdd 1) = fun _ : Fin 1 => v 1 := by
    funext i; fin_cases i; rfl
  rw [hl, hr]

private theorem inner_cotangentSharp_eval (g : SmoothRiemannianMetric I M) (x : M)
    (a : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X : TangentSpace I x) :
    g.inner x (cotangentSharp (I := I) g x a) X = a (fun _ : Fin 1 => X) := by
  rw [cotangentSharp_inner, cotangentToDual_apply]

private theorem inner_gradFun_eval [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hK : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (gaussCurvature (I := I) g))
    (x : M) (X : TangentSpace I x) :
    g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x) X
      = (duSec (I := I) (gaussCurvature (I := I) g) hK) x (fun _ : Fin 1 => X) := by
  rw [duSec_apply, differential1FormFun_apply_eq_extDerivFun]
  exact inner_gradFun (I := I) g (gaussCurvature (I := I) g) x X

private theorem inner0S_duSec_eval [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hK : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (gaussCurvature (I := I) g))
    (h : OneFormSection (I := I) (M := M)) (x : M) :
    inner0S (I := I) g x 1 (h x) ((duSec (I := I) (gaussCurvature (I := I) g) hK) x)
      = g.inner x (cotangentSharp (I := I) g x (h x))
          (gradFun (I := I) g (gaussCurvature (I := I) g) x) := by
  rw [inner0S_one_eq_eval_sharp_right, cotangentToDual_apply_gen, duSec_apply,
    cotangentSharp_differential1FormFun_eq_gradientFun, inner_cotangentSharp_eval]
  rfl

private theorem oneFormReaction2D_decomp [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hK : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (gaussCurvature (I := I) g))
    (h : OneFormSection (I := I) (M := M)) (x : M) :
    oneFormReaction2D (I := I) g (h x)
      = oneFormProd (I := I) (duSec (I := I) (gaussCurvature (I := I) g) hK) h x
          + oneFormProd (I := I) h (duSec (I := I) (gaussCurvature (I := I) g) hK) x
        - (inner0S (I := I) g x 1 (h x)
              ((duSec (I := I) (gaussCurvature (I := I) g) hK) x))
            • metricTensor0S (I := I) g x := by
  ext v
  have hL : oneFormReaction2D (I := I) g (h x) v
      = covectorTensorProd0S (I := I)
            (g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x))
            (g.inner x (cotangentSharp (I := I) g x (h x))) v
        + covectorTensorProd0S (I := I)
            (g.inner x (cotangentSharp (I := I) g x (h x)))
            (g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x)) v
        - (g.inner x (cotangentSharp (I := I) g x (h x))
            (gradFun (I := I) g (gaussCurvature (I := I) g) x))
          • (metricTensor0S (I := I) g x v) := rfl
  have hR : (oneFormProd (I := I) (duSec (I := I) (gaussCurvature (I := I) g) hK) h x
          + oneFormProd (I := I) h (duSec (I := I) (gaussCurvature (I := I) g) hK) x
        - (inner0S (I := I) g x 1 (h x)
              ((duSec (I := I) (gaussCurvature (I := I) g) hK) x))
            • metricTensor0S (I := I) g x) v
      = oneFormProd (I := I) (duSec (I := I) (gaussCurvature (I := I) g) hK) h x v
          + oneFormProd (I := I) h (duSec (I := I) (gaussCurvature (I := I) g) hK) x v
        - (inner0S (I := I) g x 1 (h x)
              ((duSec (I := I) (gaussCurvature (I := I) g) hK) x))
            • (metricTensor0S (I := I) g x v) := rfl
  rw [hL, hR, covectorProd_eval', covectorProd_eval', oneFormProd_apply, oneFormProd_apply]
  simp only [smul_eq_mul, inner_gradFun_eval (I := I) g hK,
    inner_cotangentSharp_eval (I := I) g x, inner0S_duSec_eval (I := I) g hK h x]

private theorem reaction_pairing_continuous [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hK : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (gaussCurvature (I := I) g))
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M)) :
    Continuous (fun x : M =>
      inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)) := by
  have hcont1 := continuous_inner0S_fields (I := I) g
    (oneFormProd (I := I) (duSec (I := I) (gaussCurvature (I := I) g) hK) h) nablaH
  have hcont2 := continuous_inner0S_fields (I := I) g
    (oneFormProd (I := I) h (duSec (I := I) (gaussCurvature (I := I) g) hK)) nablaH
  have hcontc := continuous_inner0S_fields (I := I) g h
    (duSec (I := I) (gaussCurvature (I := I) g) hK)
  have hcontT := (trace02_smooth (I := I) g nablaH).continuous
  refine ((hcont1.add hcont2).sub (hcontc.mul hcontT)).congr (fun x => ?_)
  rw [oneFormReaction2D_decomp (I := I) g hK h x, inner0S_sub_left', inner0S_add_left',
    inner0S_smul_left]
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
  classical
  have hK : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (gaussCurvature (I := I) (S.family.metric (t₀ : Real))) :=
    gaussCurvature_contMDiff (I := I) (M := M) (S.family.metric (t₀ : Real))
  have hR2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) (S.family.metric (t₀ : Real)))
        (h (t₀ : Real)) (nablaH (t₀ : Real)) x (nabla2H (t₀ : Real) x) :=
    fun x => hProbe.realizes (RealTimeInterval.regularToFlow t₀) x
  have hR1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) (S.family.metric (t₀ : Real)))
      (h (t₀ : Real)) (nablaH (t₀ : Real)) := fun x => (hR2 x).1 x
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
      ⟨gaussCurvature (I := I) (S.family.metric (t₀ : Real)), hK⟩ W
    with hKW_def
  have hLWfun : ∀ y : M, LW.toFun y =
      TensorRSSpace.toModel
        (Tensor0SSpace.toRS0
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) y))) := fun y => (hbridge y).2
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
  have hIntA : MeasureTheory.Integrable
      (fun x : M => normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
        (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
          (nabla2H (t₀ : Real) x)))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) := by
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) LW LW).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [hLWfun x, ← normSq0S_eq_tensorInnerPointwise_toRS0]
  have hIntX : MeasureTheory.Integrable
      (fun x : M => gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
        inner0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) x)))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) := by
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) KW LW).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [hKWfun x, hLWfun x, inner_toRS0, ← inner0S_eq_covariantTensorInnerPointwise,
      inner0S_smul_left]
  have hIntDq : MeasureTheory.Integrable
      (fun x : M => gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x ^ 2 *
        normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) (S.family.metric (t₀ : Real))
      ((hK.continuous.pow 2).mul
        (normSq0S_cont (I := I) (S.family.metric (t₀ : Real)) (h (t₀ : Real))))
  have hIntB : MeasureTheory.Integrable
      (fun x : M => gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
        normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) (S.family.metric (t₀ : Real))
      (hK.continuous.mul
        (normSq0S_cont (I := I) (S.family.metric (t₀ : Real)) (nablaH (t₀ : Real))))
  have hIntS : MeasureTheory.Integrable
      (fun x : M => inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
        (oneFormReaction2D (I := I) (S.family.metric (t₀ : Real)) (h (t₀ : Real) x))
        (nablaH (t₀ : Real) x))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) (S.family.metric (t₀ : Real))
      (reaction_pairing_continuous (I := I) (S.family.metric (t₀ : Real)) hK
        (h (t₀ : Real)) (nablaH (t₀ : Real)))
  have hSOSpt : ∀ x : M,
      normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
              (nabla2H (t₀ : Real) x)
            + gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x • (h (t₀ : Real) x))
        = normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
            (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
              (nabla2H (t₀ : Real) x))
          + ((2 : Real) * (gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
                inner0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
                  (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                    (nabla2H (t₀ : Real) x)))
            + gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x ^ 2 *
                normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)) := by
    intro x
    rw [normSq0S_add_expand', inner0S_smul_right]
    rw [show normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
          (gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x • (h (t₀ : Real) x))
        = gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x ^ 2 *
            normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x) from by
      rw [normSq0S_eq_inner, inner0S_smul_left, inner0S_smul_right, ← normSq0S_eq_inner]
      ring]
    rw [inner0S_symm'' (I := I) (S.family.metric (t₀ : Real)) x 1
      (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
        (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x)]
    ring
  have hInt2 : MeasureTheory.Integrable
      (fun x : M => (2 : Real) * (gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
        inner0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) x))))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) :=
    hIntX.const_mul 2
  have hInt23 : MeasureTheory.Integrable
      (fun x : M => (2 : Real) * (gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
            inner0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
              (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                (nabla2H (t₀ : Real) x)))
          + gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x ^ 2 *
              normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) :=
    hInt2.add hIntDq
  have hSOS : (∫ x, normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
              (nabla2H (t₀ : Real) x)
            + gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x • (h (t₀ : Real) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
      = (∫ x, normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
            (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
              (nabla2H (t₀ : Real) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
        + (2 : Real) * (∫ x, gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
              inner0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
                (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                  (nabla2H (t₀ : Real) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
        + (∫ x, gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x ^ 2 *
              normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real)))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hSOSpt),
      MeasureTheory.integral_add hIntA hInt23,
      MeasureTheory.integral_add hInt2 hIntDq,
      MeasureTheory.integral_const_mul]
    ring
  have hRCpt : ∀ x : M,
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
        = (2 : Real) * (gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
              normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
          + (2 : Real) * (inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
              (oneFormReaction2D (I := I) (S.family.metric (t₀ : Real)) (h (t₀ : Real) x))
              (nablaH (t₀ : Real) x)) := by
    intro x
    rw [ReactionTwoDim.reaction_integrand_twoDim (I := I) hdim S hS t₀ x
      (h (t₀ : Real) x) (nablaH (t₀ : Real) x)]
    ring
  have hRC : (∫ x,
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
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
      = (2 : Real) * (∫ x, gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x *
            normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
        + (2 : Real) * (∫ x, inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
              (oneFormReaction2D (I := I) (S.family.metric (t₀ : Real)) (h (t₀ : Real) x))
              (nablaH (t₀ : Real) x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real)))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hRCpt),
      MeasureTheory.integral_add (hIntB.const_mul 2) (hIntS.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hstar := curvatureEnergyIdentity_twoDim (I := I) hdim (S.family.metric (t₀ : Real))
    (h (t₀ : Real)) (nablaH (t₀ : Real)) (nabla2H (t₀ : Real)) hK hR1 hR2
  have hn4 := oneForm_weighted_roughLap_ibp (I := I) (S.family.metric (t₀ : Real))
    (f := gaussCurvature (I := I) (S.family.metric (t₀ : Real))) hK
    (h (t₀ : Real)) (nablaH (t₀ : Real)) (nabla2H (t₀ : Real)) hR2
  rw [hSOS] at hstar
  refine (hodgeHeatOneForm_gradNormSq_integral_hasDerivAt_solution (I := I) (M := M)
    hdim S hS h nablaH nabla2H hProbe t₀).congr_deriv ?_
  simp only [volumeMeasureFamilyOn_eq]
  rw [hRC]
  linarith [hstar, hn4]

end SolutionHodgeProbeEnergy
end Evolution
end DifferentialGeometry.PDE.RicciFlow
