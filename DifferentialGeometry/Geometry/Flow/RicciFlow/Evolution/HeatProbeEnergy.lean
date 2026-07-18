import DifferentialGeometry.Analysis.Parabolic.OneFormHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Volume
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.CotangentRiemannian
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.RankZeroInner
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Geometry.Connection.Laplacian.RankZero
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannTimeDeriv
import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.FamilyProducers

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow
namespace Evolution
namespace HeatProbeEnergy

open MeasureTheory
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic
open Bundle Tensor0SBundle
open Tensor0SNabla
open DifferentialGeometry.Tensor.Coordinates
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


private lemma traceTimeDerivMetricOn_eq_neg_two_scalar
    [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : IsRealizedRicciFlowSolutionOn (I := I) S)
    (t₀ : RealTimeInterval.RegularTime D) (x : M) :
    traceTimeDerivMetric (I := I) (fun s : Real => S.family.metric s) (t₀ : Real) x =
      (-2 : Real) *
        scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci (t₀ : Real) x := by
  classical
  have hderiv_entry : ∀ i j : Fin (Module.finrank Real E),
      deriv (fun s : Real =>
          chartGramMatrix (I := I) (S.family.metric s) x x i j) (t₀ : Real) =
        (-2 : Real) * S.ricci (t₀ : Real) x
          (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x) := by
    intro i j
    have hEq := (hS.equation t₀ x
        (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x)).hasDerivAt (D.regular_mem_nhds t₀.2)
    have hfun :
        (fun s : Real => chartGramMatrix (I := I) (S.family.metric s) x x i j) =
          (fun s : Real => (S.family.metric s).inner x
            (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)) := by
      funext s
      exact chartGramMatrix_apply (I := I) (S.family.metric s) x x i j
    rw [hfun]
    exact hEq.deriv
  rw [traceTimeDerivMetric_eq]
  set Ginv : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    (chartGramMatrix (I := I) (S.family.metric (t₀ : Real)) x x)⁻¹ with hGinv
  have hInvSymm : ∀ i j : Fin (Module.finrank Real E), Ginv j i = Ginv i j := by
    intro i j
    have hHerm : Ginv.IsHermitian := by
      rw [hGinv]
      exact (chartGramMatrix_isHermitian (I := I) (S.family.metric (t₀ : Real)) x x).inv
    simpa [star_trivial] using hHerm.apply i j
  have hScalarEq :
      scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci (t₀ : Real) x =
        ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          Ginv i j * S.ricci (t₀ : Real) x
            (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x) := by
    rw [hGinv]
    exact Volume.scalar_trace_eq_volume_trace_components (I := I) (M := M)
      (S.family.metric (t₀ : Real)) (S.ricci (t₀ : Real))
      (scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci (t₀ : Real))
      (scalarCurvatureFromRicciTraceInFrame_realizes (I := I)
        (S.ricci (t₀ : Real))
        (Volume.volumeTraceInvMetricComponents (I := I) (M := M) (S.family.metric (t₀ : Real)))
        (Volume.volumeTraceFrame (I := I) (M := M))) x
  have hdG :
      (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          deriv (fun s : Real => chartGramMatrix (I := I) (S.family.metric s) x x i j)
            (t₀ : Real)) =
        Matrix.of fun i j : Fin (Module.finrank Real E) =>
          (-2 : Real) * S.ricci (t₀ : Real) x
            (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x) := by
    ext i j
    simp only [Matrix.of_apply]
    exact hderiv_entry i j
  rw [hdG]
  calc
    Matrix.trace
        (Ginv *
          Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) * S.ricci (t₀ : Real) x
              (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x))
        =
        Matrix.trace
          ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
              (-2 : Real) * S.ricci (t₀ : Real) x
                (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)) *
            Ginv) := by
          rw [Matrix.trace_mul_comm]
    _ =
        ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          ((-2 : Real) * S.ricci (t₀ : Real) x
              (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)) *
            Ginv j i := by
          simp [Matrix.trace, Matrix.mul_apply]
    _ =
        (-2 : Real) *
          (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
            Ginv i j * S.ricci (t₀ : Real) x
              (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)) := by
          simp_rw [hInvSymm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
    _ =
        (-2 : Real) *
          scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
            (t₀ : Real) x := by
          rw [hScalarEq]


private lemma chartGram_jointSmooth_of_metricFamilySmoothOn
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (x₀ : M) (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
      (D.regular ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
  Tensor0SBundle.chartGram_jointContMDiffOn_of_metricFamilySmoothOn
    (I := I) (M := M) G hG x₀ i j


private lemma normSq0S_oneForm_jointSmooth
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hProbe : IsHeatOneFormOn (I := I) G h nablaH nabla2H) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => normSq0S (I := I) (G.metric p.1) p.2 1 (h p.1 p.2))
      (D.regular ×ˢ Set.univ) :=
  heatOneForm_normSq_jointContMDiffOn (I := I) (M := M) hG hProbe


private lemma toModel0S_apply {s : ℕ} {z : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z)
    (m : Fin s -> TangentSpace I z) :
    Tensor0SSpace.toModel T m = T m := rfl

private lemma toModel0S_sum {s : ℕ} {z : M} {ι : Type*} (t : Finset ι)
    (f : ι -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z) :
    Tensor0SSpace.toModel (∑ i ∈ t, f i) = ∑ i ∈ t, Tensor0SSpace.toModel (f i) :=
  map_sum (tensor0SSpace_continuousLinearEquiv (I := I) s z) f t

private lemma peel1_koszul
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (W : (y : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    {x : M} (hW : TensorSectionMDiffAt (I := I) 1 W x)
    (Zf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g) W x v)
        ![Zf x] =
      extDerivFun (I := I)
          (scalarFn I M (fun z : M => curriedSection I M W z (Zf z))) x v
        - Tensor0SSpace.toModel (W x)
            ![(LeviCivita (I := I) g).toFun (fun y => Zf y) x v] := by
  classical
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 0 W hW
    Zf v (fun i : Fin 0 => i.elim0)
  have hcons : (Fin.cons (Zf x) (fun i : Fin 0 => (i.elim0 : E)) : Fin 1 -> TangentSpace I x) =
      ![Zf x] := by
    funext i; fin_cases i; rfl
  have hcons2 : (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Zf y) x v)
      (fun i : Fin 0 => (i.elim0 : E)) : Fin 1 -> TangentSpace I x) =
      ![(LeviCivita (I := I) g).toFun (fun y => Zf y) x v] := by
    funext i; fin_cases i; rfl
  rw [hcons, hcons2] at hpeel
  have hd0 : Tensor0SSpace.toModel
      (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => curriedSection I M W y (Zf y)) x v)
      (fun i : Fin 0 => i.elim0) =
      extDerivFun (I := I)
        (scalarFn I M (fun z : M => curriedSection I M W z (Zf z))) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g
      (fun y : M => curriedSection I M W y (Zf y)) x v]
    rfl
  rw [hpeel, hd0]


private lemma abstract1
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hLC : IsLeviCivita (I := I) cov g)
    (α : OneFormSection (I := I) (M := M))
    (β : TwoTensorSection (I := I) (M := M))
    (hreal : NablaOneFormSectionRealizes (I := I) cov α β)
    (Xf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (y : M) (w : TangentSpace I y) :
    Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
          (fun z => α z) y (Xf y)) (fun _ : Fin 1 => w) =
      β y (vec2 (Xf y) w) := by
  classical
  set Zf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) y w, smoothExtensionTangent_contMDiff (I := I) y w⟩
    with hZfdef
  have hZfy : Zf y = w := smoothExtensionTangent_eq (I := I) y w
  have htmd : TensorSectionMDiffAt (I := I) 1 (fun z => α z) y :=
    α.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpeel := peel1_koszul (I := I) (M := M) g (fun z => α z) htmd Zf (Xf y)
  have hLCeq : (LeviCivita (I := I) g).toFun (fun z => Zf z) y (Xf y) =
      (cov (fun z => Zf z) y) (Xf y) :=
    leviCivita_apply_eq_of_smooth_direction
      (I := I) (cov := LeviCivita (I := I) g) (cov' := cov)
      inferInstance inferInstance
      (leviCivitaConnectionOfMetric_isLeviCivita (I := I) g) hLC
      (fun z => Zf z) (Zf.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Xf y)
  have hev := nabla0SFun_one_eval_smooth_slots (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    cov Xf Zf α y
  have hreal_y := (hreal y) Xf (Zf y)
  have hsc : scalarFn I M (fun z : M => curriedSection I M (fun z' => α z') z (Zf z)) =
      (fun p : M => α p (fun _ : Fin 1 => Zf p)) := by
    funext z
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M), curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := α z) (v0 := Zf z) (vs := fun i => Fin.elim0 i), toModel0S_apply]
    congr 1
    funext i; fin_cases i; rfl
  rw [← hZfy, show (fun _ : Fin 1 => Zf y) = ![Zf y] from by funext i; fin_cases i; rfl,
    hpeel, hreal_y, hev, hsc]
  congr 1
  rw [toModel0S_apply, hLCeq]
  congr 1
  funext i; fin_cases i; rfl

private lemma nabla0SFun_two_koszul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (A : TwoTensorSection (I := I) (M := M)) (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X A x
        (vec2 (Y x) (Z x)) =
      extDerivFun (I := I) (fun p : M => A p (vec2 (Y p) (Z p))) x (X x) -
        A x (vec2 ((cov (fun p => Y p) x) (X x)) (Z x)) -
        A x (vec2 (Y x) ((cov (fun p => Z p) x) (X x))) := by
  classical
  have h := nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s := 2) cov X ![Y, Z] A x
  have hslots : (fun a : Fin 2 => (![Y, Z] a) x) = vec2 (Y x) (Z x) := by
    funext a; fin_cases a <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hp : (fun p : M => A p (fun a : Fin 2 => (![Y, Z] a) p)) =
      (fun p : M => A p (vec2 (Y p) (Z p))) := by
    funext p; congr 1; funext a; fin_cases a <;>
      simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hslots, hp, Fin.sum_univ_two] at h
  have hu0 : (Function.update (vec2 (Y x) (Z x)) 0
        ((cov (fun p => (![Y, Z] 0) p) x) (X x))) =
      vec2 ((cov (fun p => Y p) x) (X x)) (Z x) := by
    funext a; fin_cases a <;>
      simp [Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hu1 : (Function.update (vec2 (Y x) (Z x)) 1
        ((cov (fun p => (![Y, Z] 1) p) x) (X x))) =
      vec2 (Y x) ((cov (fun p => Z p) x) (X x)) := by
    funext a; fin_cases a <;>
      simp [Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hu0, hu1] at h
  rw [h]; ring


lemma heatOneForm_wrapped_realizes
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : IsRealizedRicciFlowSolutionOn (I := I) S)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hProbe : IsHeatOneFormOn (I := I) S.family h nablaH nabla2H)
    (t₀ : RealTimeInterval.RegularTime D)
    (W : SmoothCcTensor (S.family.metric (t₀ : Real)) 0 1)
    (hW : ∀ y : M, W.toSection y =
      Tensor0SSpace.toRS0 (h (t₀ : Real) y))
    (x : M) :
    (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W).toFun x =
        TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaH (t₀ : Real) x))
      ∧ (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W).toFun x =
        TensorRSSpace.toModel
          (Tensor0SSpace.toRS0
            (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
              (nabla2H (t₀ : Real) x))) := by
  classical
  have hmc : IsMetricCompatible_gen (I := I) (S.family.connection (t₀ : Real))
      (S.family.metric (t₀ : Real)) := hS.leviCivita.1 (RealTimeInterval.regularToFlow t₀)
  have htf : IsTorsionFree (I := I) (S.family.connection (t₀ : Real)) :=
    hS.leviCivita.2 (RealTimeInterval.regularToFlow t₀)
  have hLC : IsLeviCivita (I := I) (S.family.connection (t₀ : Real))
      (S.family.metric (t₀ : Real)) := isLeviCivita_of_parts hmc htf
  haveI hcovsmooth : CovariantDerivative.ContMDiffCovariantDerivative
      (S.family.connection (t₀ : Real)) ∞ :=
    hS.smoothConnection (RealTimeInterval.regularToFlow t₀)
  have hreal1 : NablaOneFormSectionRealizes (I := I) (S.family.connection (t₀ : Real))
      (h (t₀ : Real)) (nablaH (t₀ : Real)) :=
    (hProbe.realizes (RealTimeInterval.regularToFlow t₀) x).1
  have hWsec : (fun y : M => W.toSection y) =
      (fun y : M => (h (t₀ : Real)).toTensorRSField ∞ y) := by
    funext y
    rw [hW y]
    exact (Tensor0SField.toRS0_eq (I := I) (M := M) ∞ (h (t₀ : Real)) y).symm
  refine ⟨?_, ?_⟩
  · rw [SmoothCcTensor.toFun_apply]
    refine congrArg TensorRSSpace.toModel ?_
    refine ContinuousLinearMap.ext (fun D => ?_)
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    have hconv : TensorRSNabla.tensorRSCovariantDerivative I M 0 1
          (LeviCivita (I := I) (S.family.metric (t₀ : Real)))
          (fun y : M => W.toSection y) x (v 0) =
        Tensor0SSpace.toRS0
          (tensor0SCovariantDerivative I M 1
            (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (h (t₀ : Real)) x (v 0)) := by
      rw [hWsec]
      exact nablaRS_toRS0 (I := I) (M := M)
        (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (h (t₀ : Real)) x (v 0)
    change Tensor0SSpace.toModel
        ((TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W).toSection x
          D) v =
      Tensor0SSpace.toModel (Tensor0SSpace.toRS0 (nablaH (t₀ : Real) x) D) v
    rw [TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M)
        (S.family.metric (t₀ : Real)) 0 1 W x D v,
      TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W x (v 0),
      hconv,
      Tensor0SSpace.toRS0_apply, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toRS0_apply,
      Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
      toModel0S_apply, toModel0S_apply]
    congr 1
    set Xf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ with hXfdef
    have hXfx : Xf x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
    have hab := abstract1 (I := I) (M := M) (S.family.metric (t₀ : Real))
      (S.family.connection (t₀ : Real)) hLC (h (t₀ : Real)) (nablaH (t₀ : Real))
      hreal1 Xf x (v 1)
    rw [hXfx, toModel0S_apply] at hab
    rw [show Matrix.vecTail v = (fun _ : Fin 1 => v 1) from by
      funext i; fin_cases i; rfl, hab,
      show vec2 (I := I) (v 0) (v 1) = v from by funext i; fin_cases i <;> rfl]
  · have hreal2 := (hProbe.realizes (RealTimeInterval.regularToFlow t₀) x).2
    simp only [RealTimeInterval.regularToFlow_val] at hreal2
    have hAsmooth : ContMDiff I (I.prod 𝓘(Real, Tensor0SModel 1 Real E)) (∞ + 1)
        (fun z : M => TotalSpace.mk' (Tensor0SModel 1 Real E)
          (E := fun y : M => Tensor0SSpace 1 I y) z ((h (t₀ : Real)) z)) := by
      simpa using (h (t₀ : Real)).contMDiff
    let dA : Fin (Module.finrank Real E) -> OneFormSection (I := I) (M := M) :=
      fun i => ⟨fun z : M => tensor0SCovariantDerivative I M 1
          (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (h (t₀ : Real)) z
          (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i z),
        by
          have hc := covApply_contMDiffOn
            (cov := tensor0SCovariantDerivative I M 1
              (LeviCivita (I := I) (S.family.metric (t₀ : Real))))
            (smoothOrthoFrame_smooth (I := I) (S.family.metric (t₀ : Real)) x i) hAsmooth
          rwa [contMDiffOn_univ] at hc⟩
    have hdAeq : ∀ i (z : M), dA i z =
        tensor0SCovariantDerivative I M 1
          (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (h (t₀ : Real)) z
          (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i z) := fun i z => rfl
    have hinner : ∀ (i : Fin (Module.finrank Real E)) (tail : Fin 1 -> TangentSpace I x),
        Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M 1
              (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (dA i) x
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)) tail -
          Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M 1
              (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (h (t₀ : Real)) x
              ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x))) tail =
          nabla2H (t₀ : Real) x
            (vec3 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) (tail 0)) := by
      intro i tail
      set Zf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
        ⟨smoothExtensionTangent (I := I) x (tail 0),
          smoothExtensionTangent_contMDiff (I := I) x (tail 0)⟩ with hZf_def
      have hZfx : Zf x = tail 0 := smoothExtensionTangent_eq (I := I) x (tail 0)
      set Wf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
        ⟨smoothExtensionTangent (I := I) x
            ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)),
          smoothExtensionTangent_contMDiff (I := I) x _⟩ with hWf_def
      have hWfx : Wf x =
          (LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) :=
        smoothExtensionTangent_eq (I := I) x _
      have htmddA : TensorSectionMDiffAt (I := I) 1 (fun z => dA i z) x :=
        (dA i).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hpeel := peel1_koszul (I := I) (M := M) (S.family.metric (t₀ : Real))
        (fun z => dA i z) htmddA Zf
        (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)
      have hsc : scalarFn I M (fun z : M => curriedSection I M (fun w => dA i w) z (Zf z)) =
          (fun z : M => nablaH (t₀ : Real) z
            (vec2 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i z) (Zf z))) := by
        funext z
        rw [scalarFn_eq_toModel_elim0 (I := I) (M := M), curriedSection_apply,
          TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := dA i z) (v0 := Zf z) (vs := fun k => Fin.elim0 k), toModel0S_apply,
          show (Fin.cons (Zf z) (fun k : Fin 0 => (k.elim0 : E)) : Fin 1 -> TangentSpace I z) =
              (fun _ : Fin 1 => Zf z) from by funext k; fin_cases k; rfl,
          hdAeq i z]
        have hab := abstract1 (I := I) (M := M) (S.family.metric (t₀ : Real))
          (S.family.connection (t₀ : Real)) hLC (h (t₀ : Real)) (nablaH (t₀ : Real)) hreal1
          ⟨smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i,
            smoothOrthoFrame_smooth (I := I) (S.family.metric (t₀ : Real)) x i⟩ z (Zf z)
        rw [toModel0S_apply] at hab
        exact hab
      have hfirst : Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 1
            (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (dA i) x
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)) tail =
          extDerivFun (I := I)
              (fun z : M => nablaH (t₀ : Real) z
                (vec2 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i z) (Zf z))) x
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) -
            nablaH (t₀ : Real) x
              (vec2 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)
                ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun (fun w => Zf w) x
                  (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x))) := by
        rw [show tail = ![Zf x] from by funext k; fin_cases k; exact hZfx.symm, hpeel, hsc]
        congr 1
        rw [toModel0S_apply, hdAeq i x,
          show (![(LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun (fun w => Zf w) x
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)] :
              Fin 1 -> TangentSpace I x) =
              (fun _ : Fin 1 =>
                (LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun (fun w => Zf w) x
                  (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)) from by
            funext k; fin_cases k; rfl]
        have hab2 := abstract1 (I := I) (M := M) (S.family.metric (t₀ : Real))
          (S.family.connection (t₀ : Real)) hLC (h (t₀ : Real)) (nablaH (t₀ : Real)) hreal1
          ⟨smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i,
            smoothOrthoFrame_smooth (I := I) (S.family.metric (t₀ : Real)) x i⟩ x
          ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun (fun w => Zf w) x
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x))
        rw [toModel0S_apply] at hab2
        exact hab2
      have hsecond : Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 1
            (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (h (t₀ : Real)) x
            ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x))) tail =
          nablaH (t₀ : Real) x
            (vec2 ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)) (tail 0)) := by
        rw [show tail = (fun _ : Fin 1 => tail 0) from by funext k; fin_cases k; rfl]
        have hab3 := abstract1 (I := I) (M := M) (S.family.metric (t₀ : Real))
          (S.family.connection (t₀ : Real)) hLC (h (t₀ : Real)) (nablaH (t₀ : Real)) hreal1
          Wf x (tail 0)
        rw [hWfx] at hab3
        exact hab3
      have hR : nabla2H (t₀ : Real) x
            (vec3 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) (tail 0)) =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (S.family.connection (t₀ : Real))
            ⟨smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i,
              smoothOrthoFrame_smooth (I := I) (S.family.metric (t₀ : Real)) x i⟩
            (nablaH (t₀ : Real)) x
            (vec2 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) (tail 0)) :=
        hreal2 ⟨smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i,
            smoothOrthoFrame_smooth (I := I) (S.family.metric (t₀ : Real)) x i⟩
          (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) (tail 0)
      rw [hfirst, hsecond, hR]
      have hev2 : nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (S.family.connection (t₀ : Real))
            ⟨smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i,
              smoothOrthoFrame_smooth (I := I) (S.family.metric (t₀ : Real)) x i⟩
            (nablaH (t₀ : Real)) x
            (vec2 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) (tail 0)) =
          extDerivFun (I := I) (fun p : M => nablaH (t₀ : Real) p
              (vec2 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i p) (Zf p))) x
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) -
            nablaH (t₀ : Real) x
              (vec2 ((S.family.connection (t₀ : Real))
                  (fun p => smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i p) x
                  (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)) (tail 0)) -
            nablaH (t₀ : Real) x
              (vec2 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)
                ((S.family.connection (t₀ : Real)) (fun p => Zf p) x
                  (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x))) := by
        have hk := nabla0SFun_two_koszul (I := I) (M := M) (S.family.connection (t₀ : Real))
          ⟨smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i,
            smoothOrthoFrame_smooth (I := I) (S.family.metric (t₀ : Real)) x i⟩
          ⟨smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i,
            smoothOrthoFrame_smooth (I := I) (S.family.metric (t₀ : Real)) x i⟩ Zf
          (nablaH (t₀ : Real)) x
        rw [hZfx] at hk
        exact hk
      rw [hev2]
      have hLCa : (S.family.connection (t₀ : Real)) (fun p => Zf p) x
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) =
          (LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun (fun w => Zf w) x
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) :=
        leviCivita_apply_eq_of_smooth_direction (I := I)
          (cov := S.family.connection (t₀ : Real))
          (cov' := LeviCivita (I := I) (S.family.metric (t₀ : Real))) inferInstance inferInstance
          hLC (leviCivitaConnectionOfMetric_isLeviCivita (I := I) (S.family.metric (t₀ : Real)))
          (fun z => Zf z) (Zf.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)
      have hLCb : (S.family.connection (t₀ : Real))
            (fun p => smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i p) x
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) =
          (LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) :=
        leviCivita_apply_eq_of_smooth_direction (I := I)
          (cov := S.family.connection (t₀ : Real))
          (cov' := LeviCivita (I := I) (S.family.metric (t₀ : Real))) inferInstance inferInstance
          hLC (leviCivitaConnectionOfMetric_isLeviCivita (I := I) (S.family.metric (t₀ : Real)))
          (fun z => smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i z)
          ((smoothOrthoFrame_smooth (I := I) (S.family.metric (t₀ : Real)) x i).contMDiffAt.mdifferentiableAt
            (by simp))
          (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)
      rw [hLCa, hLCb]
      ring
    have hterm : ∀ i : Fin (Module.finrank Real E),
        tensorSecondCovDeriv (I := I) (S.family.metric (t₀ : Real)) 0 1
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i)
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i)
            (fun z => W.toSection z) x =
          Tensor0SSpace.toRS0
              (tensor0SCovariantDerivative I M 1
                (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (dA i) x
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)) -
            Tensor0SSpace.toRS0
              (tensor0SCovariantDerivative I M 1
                (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (h (t₀ : Real)) x
                ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
                  (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
                  (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x))) := by
      intro i
      have hcovApply : covApply (tensorCov (I := I) (S.family.metric (t₀ : Real)) 0 1)
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i)
            (fun z => W.toSection z) =
          (fun z : M => (dA i).toTensorRSField ∞ z) := by
        funext z
        rw [covApply_apply,
          show (tensorCov (I := I) (S.family.metric (t₀ : Real)) 0 1).toFun
                (fun w => W.toSection w) z
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i z) =
              TensorRSNabla.tensorRSCovariantDerivative I M 0 1
                (LeviCivita (I := I) (S.family.metric (t₀ : Real)))
                (fun w => W.toSection w) z
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i z) from rfl, hWsec,
          nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) (S.family.metric (t₀ : Real)))
            (h (t₀ : Real)) z (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i z),
          Tensor0SField.toRS0_eq]
        rfl
      rw [tensorSecondCovDeriv_def, hcovApply,
        show (tensorCov (I := I) (S.family.metric (t₀ : Real)) 0 1).toFun
              (fun z : M => (dA i).toTensorRSField ∞ z) x
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) =
            TensorRSNabla.tensorRSCovariantDerivative I M 0 1
              (LeviCivita (I := I) (S.family.metric (t₀ : Real)))
              ((dA i).toTensorRSField ∞) x
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) from rfl,
        nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) (S.family.metric (t₀ : Real)))
          (dA i) x (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x),
        show (tensorCov (I := I) (S.family.metric (t₀ : Real)) 0 1).toFun
              (fun z => W.toSection z) x
              ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)) =
            TensorRSNabla.tensorRSCovariantDerivative I M 0 1
              (LeviCivita (I := I) (S.family.metric (t₀ : Real))) (fun w => W.toSection w) x
              ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)) from rfl,
        hWsec,
        nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) (S.family.metric (t₀ : Real)))
          (h (t₀ : Real)) x
          ((LeviCivita (I := I) (S.family.metric (t₀ : Real))).toFun
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i) x
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x))]
    have horth : ∀ a b : Fin (Module.finrank Real E),
        (S.family.metric (t₀ : Real)).inner x
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x a x)
            (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x b x) =
          if a = b then 1 else 0 :=
      fun a b => smoothOrthoFrame_orthonormal_at_center (I := I)
        (S.family.metric (t₀ : Real)) x a b
    have hli : LinearIndependent Real
        (fun i : Fin (Module.finrank Real E) =>
          smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) := by
      classical
      rw [Fintype.linearIndependent_iff]
      intro c hc j
      have hpair : (S.family.metric (t₀ : Real)).inner x
          (∑ a, c a • smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x a x)
          (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x j x) = 0 := by
        rw [hc]; simp
      rw [map_sum, ContinuousLinearMap.sum_apply, Finset.sum_eq_single j] at hpair
      · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, horth j j,
          if_pos rfl, smul_eq_mul, mul_one] at hpair
        exact hpair
      · intro a _ haj
        rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, horth a j,
          if_neg (by simpa using haj), smul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    let basis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
      basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; rfl)
    have hbasis : ∀ i, basis i = smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x := by
      intro i
      change (basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; rfl)) i =
        smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    have hinv : MetricInverseInBasis_gen (I := I) (S.family.metric (t₀ : Real)) x basis
        (identityInvMetric (Idx := Fin (Module.finrank Real E))) := by
      intro a b
      simp only [identityInvMetric, diagonalInvMetric, hbasis]
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_eq_single a]
        · rw [if_pos rfl, one_mul, horth]
        · intro c _ hc; rw [if_neg (fun heq => hc heq.symm), zero_mul]
        · intro hcon; exact absurd (Finset.mem_univ a) hcon
      · rw [Finset.sum_eq_single b]
        · rw [if_pos rfl, mul_one, horth]
        · intro c _ hc; rw [if_neg hc, mul_zero]
        · intro hcon; exact absurd (Finset.mem_univ b) hcon
    have hcollapse : ∀ tail : Fin 1 -> TangentSpace I x,
        roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
          (nabla2H (t₀ : Real) x) tail =
          ∑ i : Fin (Module.finrank Real E),
            nabla2H (t₀ : Real) x
              (vec3 (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x)
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i x) (tail 0)) := by
      intro tail
      rw [roughLap0STensor_apply,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) (S.family.metric (t₀ : Real)) basis
          (identityInvMetric (Idx := Fin (Module.finrank Real E))) hinv]
      unfold metricTrace0S2InBasis
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_eq_single a]
      · rw [identityInvMetric_apply_self, one_mul, hbasis,
          show metricTraceInput (I := I)
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x a x)
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x a x) tail =
              metricTraceInput (I := I)
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x a x)
                (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x a x)
                (fun _ : Fin 1 => tail 0) from by
            congr 1; funext k; fin_cases k; rfl,
          metricTraceInput_one_eq_vec3]
      · intro b _ hba
        rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun heq => hba heq.symm),
          zero_mul]
      · intro hcon; exact absurd (Finset.mem_univ a) hcon
    rw [SmoothCcTensor.toFun_apply]
    refine congrArg TensorRSSpace.toModel ?_
    rw [rawTensorConnLapSmooth_toSection_apply,
      rawTensorConnLap_eq_frame_trace_secondCovDeriv]
    refine ContinuousLinearMap.ext (fun D => ?_)
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun tail => ?_)
    change Tensor0SSpace.toModel
        ((∑ i : Fin (Module.finrank Real E),
            tensorSecondCovDeriv (I := I) (S.family.metric (t₀ : Real)) 0 1
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i)
              (smoothOrthoFrame (I := I) (S.family.metric (t₀ : Real)) x i)
              (fun z => W.toSection z) x) D) tail =
      Tensor0SSpace.toModel
        (Tensor0SSpace.toRS0
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) x)) D) tail
    rw [ContinuousLinearMap.sum_apply, toModel0S_sum, ContinuousMultilinearMap.sum_apply,
      Tensor0SSpace.toRS0_apply, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, toModel0S_apply, hcollapse, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hterm i, ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply, Tensor0SSpace.toRS0_apply, Tensor0SSpace.toRS0_apply,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
      ← smul_sub, hinner i tail]


private lemma jointSmooth_timeDeriv_continuous
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (F : Real -> M -> Real)
    (hF : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => F p.1 p.2) (D.regular ×ˢ (Set.univ : Set M)))
    (t₀ : RealTimeInterval.RegularTime D) :
    Continuous (fun x : M => deriv (fun s : Real => F s x) (t₀ : Real)) := by
  classical
  obtain ⟨ρ, hρsmooth, hρmem, hρeq⟩ := exists_time_retract D.regular_isOpen t₀.2
  have hρmdiff : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ ρ := by
    rw [contMDiff_iff_contDiff]; exact hρsmooth
  have hinner : ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M => (ρ p.1, p.2)) :=
    (hρmdiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hf'smooth : ContMDiff (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => F (ρ p.1) p.2) :=
    hF.comp_contMDiff hinner (fun p => ⟨hρmem p.1, Set.mem_univ p.2⟩)
  let F' : C^∞⟮𝓘(Real, Real).prod I, Real × M; Real⟯ :=
    ⟨fun p : Real × M => F (ρ p.1) p.2, hf'smooth⟩
  have hpartial : Continuous
      (fun p : Real × M => deriv (fun r : Real => F' (r, p.2)) p.1) :=
    (DifferentialGeometry.contMDiff_partial_deriv_fst I F').continuous
  have hslice : Continuous
      (fun x : M => deriv (fun r : Real => F' (r, x)) (t₀ : Real)) :=
    hpartial.comp (continuous_const.prodMk continuous_id)
  refine hslice.congr (fun x => ?_)
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [hρeq] with s hs
  change F (ρ s) x = F s x
  rw [hs]


set_option maxHeartbeats 1600000 in
private lemma metricFamily_traceTimeDeriv_continuous
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (t₀ : RealTimeInterval.RegularTime D) :
    Continuous
      (fun x : M => traceTimeDerivMetric (I := I) (fun s : Real => G.metric s) (t₀ : Real) x) := by
  classical
  obtain ⟨ρ, hρsmooth, hρmem, hρeq⟩ := exists_time_retract D.regular_isOpen t₀.2
  have hρmdiff : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ ρ := by
    rw [contMDiff_iff_contDiff]; exact hρsmooth
  have hinner : ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M => (ρ p.1, p.2)) :=
    (hρmdiff.comp contMDiff_fst).prodMk contMDiff_snd
  let g' : Real → SmoothRiemannianMetric I M := fun s : Real => G.metric (ρ s)
  have hg'smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g' p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hcomp := (chartGram_jointSmooth_of_metricFamilySmoothOn (I := I) (M := M)
        G hG x₀ i j).comp hinner.contMDiffOn (by
      intro p (hp : p ∈ Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
      exact ⟨hρmem p.1, hp.2⟩)
    simpa only [Function.comp_apply, g'] using hcomp
  have hg'reg : MetricFamilyRegularAt (I := I) g' (t₀ : Real) := by
    refine
      { hasDerivAt_chartGramMatrix := ?_
        continuousOn_chartGramMatrix := ?_
        continuousOn_deriv_chartGramMatrix := ?_ }
    · intro x₀ i j x hx s
      have hp : (s, x) ∈ Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet :=
        ⟨Set.mem_univ _, hx⟩
      have hopen : IsOpen (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
        (isOpen_univ : IsOpen (Set.univ : Set Real)).prod
          (trivializationAt E (TangentSpace I) x₀).open_baseSet
      have hAt : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M => chartGramMatrix (I := I) (g' p.1) x₀ p.2 i j) (s, x) :=
        ((hg'smooth x₀ i j) (s, x) hp).contMDiffAt (hopen.mem_nhds hp)
      have hsl : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real) ∞
          (fun r : Real => chartGramMatrix (I := I) (g' r) x₀ x i j) s := by
        simpa only [Function.comp_apply] using
          hAt.comp s (contMDiffAt_id.prodMk contMDiffAt_const)
      exact ((contMDiffAt_iff_contDiffAt.mp hsl).differentiableAt (by simp)).hasDerivAt
    · intro x₀ i j
      exact (hg'smooth x₀ i j).continuousOn
    · intro x₀ i j p hp
      have hopen : IsOpen (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
        (isOpen_univ : IsOpen (Set.univ : Set Real)).prod
          (trivializationAt E (TangentSpace I) x₀).open_baseSet
      have hAt : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun q : Real × M => chartGramMatrix (I := I) (g' q.1) x₀ q.2 i j) p :=
        ((hg'smooth x₀ i j) p hp).contMDiffAt (hopen.mem_nhds hp)
      have hdAt : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun q : Real × M =>
            deriv (fun s : Real => chartGramMatrix (I := I) (g' s) x₀ q.2 i j) q.1) p :=
        DifferentialGeometry.timeDeriv_smoothAt hAt (by simp)
      exact hdAt.continuousAt.continuousWithinAt
  have hρt : ρ (t₀ : Real) = (t₀ : Real) := hρeq.eq_of_nhds
  have hTC' := traceTimeDerivMetric_continuous (I := I) (M := M) hg'reg
  refine hTC'.congr (fun x => ?_)
  have hGinvEq : g' (t₀ : Real) = G.metric (t₀ : Real) := by
    simp only [g', hρt]
  have hdG : ∀ i j : Fin (Module.finrank Real E),
      deriv (fun s : Real => chartGramMatrix (I := I) (g' s) x x i j) (t₀ : Real)
        = deriv (fun s : Real => chartGramMatrix (I := I) (G.metric s) x x i j) (t₀ : Real) := by
    intro i j
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hρeq] with s hs
    show chartGramMatrix (I := I) (g' s) x x i j
        = chartGramMatrix (I := I) (G.metric s) x x i j
    simp only [g', hs]
  rw [traceTimeDerivMetric_eq, traceTimeDerivMetric_eq, hGinvEq]
  congr 1
  congr 1
  ext i j
  exact hdG i j


set_option maxHeartbeats 1600000 in
private lemma heatOneForm_normSq_reaction_ibp
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
    (∫ x,
        (2 * ric (t₀ : Real) x
              (vec2
                (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x))
                (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x)))
          + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 1
              (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x)
          - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                (t₀ : Real) x
              * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x))
        ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
      =
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
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real))) := by
  classical
  simp only [volumeMeasureFamilyOn_eq]
  set g := S.family.metric (t₀ : Real) with hg_def
  set ν := riemannianVolumeMeasure (I := I) (M := M) g with hν_def
  set W : SmoothCcTensor g 0 1 :=
    { toSection := (h (t₀ : Real)).toTensorRSField
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW_def
  have hWfun : ∀ y : M,
      W.toFun y = TensorRSSpace.toModel (Tensor0SSpace.toRS0 (h (t₀ : Real) y)) := fun _ => rfl
  have hbridge := fun x : M =>
    heatOneForm_wrapped_realizes (I := I) (M := M) S hS h nablaH nabla2H hProbe t₀ W
      (fun _ => rfl) x
  have hB1 : ∀ x : M,
      (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x =
        TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaH (t₀ : Real) x)) :=
    fun x => (hbridge x).1
  have hB2 : ∀ x : M,
      (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun x =
        TensorRSSpace.toModel
          (Tensor0SSpace.toRS0
            (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x))) :=
    fun x => (hbridge x).2
  have hInnerB : ∀ x : M,
      inner0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x)
        = tensorInnerPointwise (I := I) (M := M) g 0 1 x
            ((rawTensorConnLapSmooth (I := I) g 0 1 W).toFun x) (W.toFun x) := by
    intro x
    rw [hB2 x, hWfun x,
      inner_toRS0 (I := I) (M := M) g 1 x
        (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x),
      inner0S_eq_covariantTensorInnerPointwise (I := I) g x 1
        (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x)]
  have hInnerNq : ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g 0 2 x
          ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x)
          ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x)
        = normSq0S (I := I) g x 2 (nablaH (t₀ : Real) x) := by
    intro x
    rw [hB1 x, ← normSq0S_eq_tensorInnerPointwise_toRS0 (I := I) g x 2 (nablaH (t₀ : Real) x)]
  have htL2_1 :
      tensorL2Inner (I := I) (M := M) g 0 1
          (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun W.toFun
        = ∫ x, inner0S (I := I) g x 1
            (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x)
          ∂ν := by
    change (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
        ((rawTensorConnLapSmooth (I := I) g 0 1 W).toFun x) (W.toFun x) ∂ν) = _
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (hInnerB x).symm))
  have htL2_2 :
      tensorL2Inner (I := I) (M := M) g 0 2
          (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
          (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
        = ∫ x, normSq0S (I := I) g x 2 (nablaH (t₀ : Real) x) ∂ν := by
    change (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 2 x
        ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x)
        ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x) ∂ν) = _
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hInnerNq x))
  have hGreenId :
      tensorL2Inner (I := I) (M := M) g 0 2
          (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
          (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
        = - tensorL2Inner (I := I) (M := M) g 0 1
            (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun W.toFun :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen (I := I) (M := M) g 1 W W
  have hInnerInt :
      (∫ x, inner0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x) ∂ν)
        = - ∫ x, normSq0S (I := I) g x 2 (nablaH (t₀ : Real) x) ∂ν := by
    rw [← htL2_1, ← htL2_2]
    linarith [hGreenId]
  have hBint : Integrable
      (fun x : M => 2 * inner0S (I := I) g x 1
        (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x)) ν := by
    have hcross := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (rawTensorConnLapSmooth (I := I) g 0 1 W) W
    have heq :
        (fun x : M => 2 * inner0S (I := I) g x 1
            (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x))
          = (fun x : M => 2 * tensorInnerPointwise (I := I) (M := M) g 0 1 x
              ((rawTensorConnLapSmooth (I := I) g 0 1 W).toFun x) (W.toFun x)) := by
      funext x; rw [hInnerB x]
    rw [heq]
    exact hcross.const_mul 2
  have hGreen :
      (∫ x, (2 * inner0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x)) ∂ν)
        = -2 * ∫ x, normSq0S (I := I) g x 2 (nablaH (t₀ : Real) x) ∂ν := by
    rw [MeasureTheory.integral_const_mul, hInnerInt]; ring
  have hDerivCont := jointSmooth_timeDeriv_continuous (I := I) (M := M)
    (fun s x => normSq0S (I := I) (S.family.metric s) x 1 (h s x))
    (heatOneForm_normSq_jointContMDiffOn (I := I) (M := M) hS.smoothMetric hProbe) t₀
  have hDerivInt : Integrable
      (fun x : M => deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 1 (h s x))
        (t₀ : Real)) ν :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hDerivCont
  have hApt : ∀ x : M,
      deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 1 (h s x)) (t₀ : Real)
        = 2 * ric (t₀ : Real) x
              (vec2 (cotangentSharp (I := I) g x (h (t₀ : Real) x))
                (cotangentSharp (I := I) g x (h (t₀ : Real) x)))
          + 2 * inner0S (I := I) g x 1
              (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x) := by
    intro x
    have hg_hyp : ∀ X Y : TangentSpace I x,
        HasDerivAt (fun r : Real => (S.family.metric r).inner x X Y)
          ((-2 : Real) * ric (t₀ : Real) x (vec2 X Y)) (t₀ : Real) := by
      intro X Y
      have hEq := (hS.equation t₀ x X Y).hasDerivAt (D.regular_mem_nhds t₀.2)
      rw [hric (t₀ : Real) x X Y]
      exact hEq
    have hnst := normSq_one_time (I := I) (x := x) (t := (t₀ : Real))
      (g := fun s : Real => S.family.metric s)
      (Q := ric (t₀ : Real) x)
      (A := fun s : Real => h s x)
      (Adot := roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x))
      hg_hyp (hProbe.equation t₀ x)
    exact hnst.deriv
  have hAint : Integrable
      (fun x : M => 2 * ric (t₀ : Real) x
        (vec2 (cotangentSharp (I := I) g x (h (t₀ : Real) x))
          (cotangentSharp (I := I) g x (h (t₀ : Real) x)))) ν := by
    have heq :
        (fun x : M => 2 * ric (t₀ : Real) x
            (vec2 (cotangentSharp (I := I) g x (h (t₀ : Real) x))
              (cotangentSharp (I := I) g x (h (t₀ : Real) x))))
          = (fun x : M =>
              deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 1 (h s x)) (t₀ : Real)
                - 2 * inner0S (I := I) g x 1
                    (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x))
                    (h (t₀ : Real) x)) := by
      funext x; rw [hApt x]; ring
    rw [heq]
    exact hDerivInt.sub hBint
  have hTraceCont := metricFamily_traceTimeDeriv_continuous (I := I) (M := M)
    S.family hS.smoothMetric t₀
  have hNSjoint := normSq0S_oneForm_jointSmooth (I := I) (M := M) S.family hS.smoothMetric
    h nablaH nabla2H hProbe
  have hNormSqCont : Continuous
      (fun x : M => normSq0S (I := I) g x 1 (h (t₀ : Real) x)) := by
    have hmap : ContMDiff I (𝓘(Real, Real).prod I) ∞ (fun x : M => ((t₀ : Real), x)) :=
      contMDiff_const.prodMk contMDiff_id
    have hmaps : ∀ x : M, ((t₀ : Real), x) ∈ D.regular ×ˢ (Set.univ : Set M) :=
      fun x => ⟨t₀.2, Set.mem_univ _⟩
    exact (hNSjoint.comp_contMDiff hmap hmaps).continuous
  have hCint : Integrable
      (fun x : M => scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
          (t₀ : Real) x
        * normSq0S (I := I) g x 1 (h (t₀ : Real) x)) ν := by
    have htrace : ∀ x : M,
        scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci (t₀ : Real) x
          = (-(1 / 2 : Real)) *
              traceTimeDerivMetric (I := I) (fun s : Real => S.family.metric s) (t₀ : Real) x := by
      intro x
      have hh := traceTimeDerivMetricOn_eq_neg_two_scalar (I := I) (M := M) S hS t₀ x
      linarith [hh]
    have hcont : Continuous
        (fun x : M => scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
            (t₀ : Real) x * normSq0S (I := I) g x 1 (h (t₀ : Real) x)) := by
      have hcont' : Continuous
          (fun x : M => ((-(1 / 2 : Real)) *
              traceTimeDerivMetric (I := I) (fun s : Real => S.family.metric s) (t₀ : Real) x)
            * normSq0S (I := I) g x 1 (h (t₀ : Real) x)) :=
        (continuous_const.mul hTraceCont).mul hNormSqCont
      refine hcont'.congr (fun x => ?_)
      rw [htrace x]
    exact integrable_of_continuous_compactSpace (I := I) (M := M) g hcont
  have hABint : Integrable
      (fun x : M => 2 * ric (t₀ : Real) x
            (vec2 (cotangentSharp (I := I) g x (h (t₀ : Real) x))
              (cotangentSharp (I := I) g x (h (t₀ : Real) x)))
          + 2 * inner0S (I := I) g x 1
              (roughLap0STensor (I := I) g (s := 1) (nabla2H (t₀ : Real) x))
              (h (t₀ : Real) x)) ν :=
    hAint.add hBint
  rw [MeasureTheory.integral_sub hABint hCint,
    MeasureTheory.integral_add hAint hBint,
    MeasureTheory.integral_sub hAint hCint, hGreen]
  ring


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
      (t₀ : Real) := by
  classical
  have hderiv := first_var_joint (I := I) (M := M)
    (g_fam := fun s : Real => S.family.metric s)
    (f := fun (s : Real) (y : M) => normSq0S (I := I) (S.family.metric s) y 1 (h s y))
    (U := D.regular) (t := (t₀ : Real))
    D.regular_isOpen t₀.2
    (fun x₀ i j =>
      chartGram_jointSmooth_of_metricFamilySmoothOn (I := I) (M := M)
        S.family hS.smoothMetric x₀ i j)
    (normSq0S_oneForm_jointSmooth (I := I) (M := M)
      S.family hS.smoothMetric h nablaH nabla2H hProbe)
  refine hderiv.congr_deriv
    (Eq.trans ?_
      (heatOneForm_normSq_reaction_ibp (I := I) (M := M)
        S hS ric hric h nablaH nabla2H hProbe t₀))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  change deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 1 (h s x)) (t₀ : Real)
        + (1 / 2 : Real) *
            traceTimeDerivMetric (I := I) (fun s : Real => S.family.metric s) (t₀ : Real) x
          * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
      = 2 * ric (t₀ : Real) x
            (vec2 (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x))
              (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x)))
        + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 1
            (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
              (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x)
        - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci (t₀ : Real) x
            * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1 (h (t₀ : Real) x)
  have hg_hyp : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (S.family.metric r).inner x X Y)
        ((-2 : Real) * ric (t₀ : Real) x (vec2 X Y)) (t₀ : Real) := by
    intro X Y
    have hEq := (hS.equation t₀ x X Y).hasDerivAt (D.regular_mem_nhds t₀.2)
    rw [hric (t₀ : Real) x X Y]
    exact hEq
  have hnst := normSq_one_time (I := I) (x := x) (t := (t₀ : Real))
    (g := fun s : Real => S.family.metric s)
    (Q := ric (t₀ : Real) x)
    (A := fun s : Real => h s x)
    (Adot := roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
      (nabla2H (t₀ : Real) x))
    hg_hyp (hProbe.equation t₀ x)
  have hderiv_pt :
      deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 1 (h s x)) (t₀ : Real) =
        2 * ric (t₀ : Real) x
            (vec2 (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x))
              (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x)))
          + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 1
              (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
                (nabla2H (t₀ : Real) x)) (h (t₀ : Real) x) := hnst.deriv
  have htrace := traceTimeDerivMetricOn_eq_neg_two_scalar (I := I) (M := M) S hS t₀ x
  rw [hderiv_pt, htrace]
  ring


private lemma toRS0_eval_one0 {s : ℕ} (x : M)
    (T : TensorRSSpace 0 s I x) :
    Tensor0SSpace.toRS0
        (T (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ x)) = T := by
  classical
  have hsmul_one : ∀ c : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 x,
      c = tensor0SSpace_evalScalar x c •
        Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ x := by
    intro c
    apply (tensor0SSpace_continuousLinearEquiv (I := I) 0 x).injective
    refine ContinuousMultilinearMap.ext fun v => ?_
    change Tensor0SSpace.toModel c v =
      Tensor0SSpace.toModel (tensor0SSpace_evalScalar x c •
        Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ x) v
    rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
      Tensor0SField.one0_apply, smul_eq_mul, mul_one, Tensor0SSpace.evalScalar_apply]
    exact congrArg (Tensor0SSpace.toModel c) (Subsingleton.elim v Fin.elim0)
  refine ContinuousLinearMap.ext fun c => ?_
  rw [Tensor0SSpace.toRS0_apply]
  conv_rhs => rw [hsmul_one c]
  rw [map_smul]


private lemma vec2_eq_cons {x : M} (X Y : TangentSpace I x) :
    vec2 (I := I) X Y = Fin.cons X (fun _ : Fin 1 => Y) := by
  funext i
  fin_cases i <;> rfl

private lemma curry_eval {n : ℕ} {z : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n + 1) z)
    (v0 : TangentSpace I z) (vs : Fin n -> TangentSpace I z) :
    (tensor0S_curry (𝕜 := Real) (I := I) n z T v0) vs = T (Fin.cons v0 vs) :=
  TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) T v0 vs

private lemma swap_vec2_eval {x : M} (X Y : TangentSpace I x) :
    (fun i => (vec2 (I := I) X Y) ((Equiv.swap (0 : Fin 2) 1) i)) = vec2 (I := I) Y X := by
  funext i
  fin_cases i <;>
    simp [vec2, DifferentialGeometry.Integral.Connection.vec2]

private lemma endoSlotFirst_apply {x : M}
    (A : TangentSpace I x →L[Real] TangentSpace I x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (X Y : TangentSpace I x) :
    endoSlotFirst (I := I) A T (vec2 (I := I) X Y) = T (vec2 (I := I) (A X) Y) := by
  have h1 : tensor0S_curry (𝕜 := Real) (I := I) 1 x (endoSlotFirst (I := I) A T)
      = ((tensor0S_curry (𝕜 := Real) (I := I) 1 x) T).comp A :=
    (tensor0S_curry (𝕜 := Real) (I := I) 1 x).apply_symm_apply _
  rw [vec2_eq_cons X Y,
    ← curry_eval (I := I) (endoSlotFirst (I := I) A T) X (fun _ : Fin 1 => Y), h1,
    ContinuousLinearMap.comp_apply, curry_eval (I := I) T (A X) (fun _ : Fin 1 => Y),
    ← vec2_eq_cons (A X) Y]

private lemma endoSlotSecond_apply {x : M}
    (A : TangentSpace I x →L[Real] TangentSpace I x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (X Y : TangentSpace I x) :
    endoSlotSecond (I := I) A T (vec2 (I := I) X Y) = T (vec2 (I := I) X (A Y)) := by
  have hkey : endoSlotSecond (I := I) A T (vec2 (I := I) X Y)
      = endoSlotFirst (I := I) A (T.domDomCongr (Equiv.swap (0 : Fin 2) 1))
          (fun i => (vec2 (I := I) X Y) ((Equiv.swap (0 : Fin 2) 1) i)) := rfl
  rw [hkey, swap_vec2_eval X Y,
    endoSlotFirst_apply (I := I) A (T.domDomCongr (Equiv.swap (0 : Fin 2) 1)) Y X]
  change T (fun i => (vec2 (I := I) (A Y) X) ((Equiv.swap (0 : Fin 2) 1) i))
      = T (vec2 (I := I) X (A Y))
  rw [swap_vec2_eval (A Y) X]

private lemma ricciSharpEndo_eval {x : M}
    (g : SmoothRiemannianMetric I M)
    (r : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (X : TangentSpace I x) :
    ricciSharpEndo (I := I) g x r X
      = cotangentSharp (I := I) g x ((tensor0S_curry (𝕜 := Real) (I := I) 1 x) r X) := rfl

private lemma curry_two_eval {x : M}
    (r : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (X Y : TangentSpace I x) :
    ((tensor0S_curry (𝕜 := Real) (I := I) 1 x) r X) (fun _ : Fin 1 => Y)
      = r (vec2 (I := I) X Y) := by
  rw [curry_eval (I := I) r X (fun _ : Fin 1 => Y), ← vec2_eq_cons X Y]


private lemma sum_fin_two {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  rw [Fintype.sum_equiv (finTwoArrowEquiv Idx) F
    (fun p : Idx × Idx => F (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [finTwoArrowEquiv]

private lemma sum3_rotate {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (H0 : Idx -> Idx -> Idx -> α) :
    (∑ j : Idx, ∑ k : Idx, ∑ l : Idx, H0 j k l) =
      ∑ k : Idx, ∑ l : Idx, ∑ j : Idx, H0 j k l := by
  calc (∑ j : Idx, ∑ k : Idx, ∑ l : Idx, H0 j k l)
      = ∑ k : Idx, ∑ j : Idx, ∑ l : Idx, H0 j k l := Finset.sum_comm
    _ = ∑ k : Idx, ∑ l : Idx, ∑ j : Idx, H0 j k l := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Finset.sum_comm

private lemma sum4_pull {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (H0 : Idx -> Idx -> Idx -> Idx -> α) :
    (∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx, H0 j k l p) =
      ∑ p : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, H0 j k l p := by
  calc (∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx, H0 j k l p)
      = ∑ j : Idx, ∑ k : Idx, ∑ p : Idx, ∑ l : Idx, H0 j k l p := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        exact Finset.sum_comm
    _ = ∑ j : Idx, ∑ p : Idx, ∑ k : Idx, ∑ l : Idx, H0 j k l p := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact Finset.sum_comm
    _ = ∑ p : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, H0 j k l p := Finset.sum_comm

private lemma sum4_push {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (H0 : Idx -> Idx -> Idx -> Idx -> α) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, H0 i j k l) =
      ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, H0 i j k l := by
  calc (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, H0 i j k l)
      = ∑ j : Idx, ∑ i : Idx, ∑ k : Idx, ∑ l : Idx, H0 i j k l := Finset.sum_comm
    _ = ∑ j : Idx, ∑ k : Idx, ∑ i : Idx, ∑ l : Idx, H0 i j k l := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact Finset.sum_comm
    _ = ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, H0 i j k l := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        exact Finset.sum_comm


private lemma tensor2_first_slot_sum {x : M} {Idx : Type*} [Fintype Idx]
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Idx -> Real) (V : Idx -> TangentSpace I x) (Y : TangentSpace I x) :
    T (vec2 (I := I) (∑ p : Idx, c p • V p) Y) =
      ∑ p : Idx, c p * T (vec2 (I := I) (V p) Y) := by
  classical
  let base : Fin 2 -> TangentSpace I x := vec2 (I := I) (∑ p : Idx, c p • V p) Y
  have hbase : Function.update base (0 : Fin 2) (∑ p : Idx, c p • V p) = base := by
    funext q
    fin_cases q <;>
      simp [base, Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hupdate : ∀ Z : TangentSpace I x,
      Function.update base (0 : Fin 2) Z = vec2 (I := I) Z Y := by
    intro Z
    funext q
    fin_cases q <;>
      simp [base, Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hsum := T.toMultilinearMap.map_update_sum
    (Finset.univ : Finset Idx) (0 : Fin 2) (fun p : Idx => c p • V p) base
  have hsum' : T (Function.update base (0 : Fin 2) (∑ p : Idx, c p • V p)) =
      ∑ p : Idx, c p * T (Function.update base (0 : Fin 2) (V p)) := by
    simpa using hsum
  calc T (vec2 (I := I) (∑ p : Idx, c p • V p) Y)
      = T (Function.update base (0 : Fin 2) (∑ p : Idx, c p • V p)) := by rw [hbase]
    _ = ∑ p : Idx, c p * T (Function.update base (0 : Fin 2) (V p)) := hsum'
    _ = ∑ p : Idx, c p * T (vec2 (I := I) (V p) Y) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hupdate (V p)]

private lemma tensor2_second_slot_sum {x : M} {Idx : Type*} [Fintype Idx]
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Idx -> Real) (V : Idx -> TangentSpace I x) (X : TangentSpace I x) :
    T (vec2 (I := I) X (∑ p : Idx, c p • V p)) =
      ∑ p : Idx, c p * T (vec2 (I := I) X (V p)) := by
  classical
  let base : Fin 2 -> TangentSpace I x := vec2 (I := I) X (∑ p : Idx, c p • V p)
  have hbase : Function.update base (1 : Fin 2) (∑ p : Idx, c p • V p) = base := by
    funext q
    fin_cases q <;>
      simp [base, Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hupdate : ∀ Z : TangentSpace I x,
      Function.update base (1 : Fin 2) Z = vec2 (I := I) X Z := by
    intro Z
    funext q
    fin_cases q <;>
      simp [base, Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hsum := T.toMultilinearMap.map_update_sum
    (Finset.univ : Finset Idx) (1 : Fin 2) (fun p : Idx => c p • V p) base
  have hsum' : T (Function.update base (1 : Fin 2) (∑ p : Idx, c p • V p)) =
      ∑ p : Idx, c p * T (Function.update base (1 : Fin 2) (V p)) := by
    simpa using hsum
  calc T (vec2 (I := I) X (∑ p : Idx, c p • V p))
      = T (Function.update base (1 : Fin 2) (∑ p : Idx, c p • V p)) := by rw [hbase]
    _ = ∑ p : Idx, c p * T (Function.update base (1 : Fin 2) (V p)) := hsum'
    _ = ∑ p : Idx, c p * T (vec2 (I := I) X (V p)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hupdate (V p)]


private lemma ricciSharpEndo_basis_expand {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (i : Idx) :
    ricciSharpEndo (I := I) g x Q (basis i) =
      ∑ p : Idx, (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m))) • basis p := by
  rw [ricciSharpEndo_eval (I := I) g Q (basis i),
    cotangentSharp_eq_sum_inv (I := I) g x basis gInv hinv
      ((tensor0S_curry (𝕜 := Real) (I := I) 1 x) Q (basis i))]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine congrArg (fun t : Real => t • (basis p : TangentSpace I x)) ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  refine congrArg (fun t : Real => gInv p m * t) ?_
  rw [cotangentToDual_apply]
  exact curry_two_eval (I := I) Q (basis i) (basis m)


private lemma inner0S_two_coord_vec2 {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l * A (vec2 (I := I) (basis i) (basis j))
          * B (vec2 (I := I) (basis k) (basis l)) := by
  rw [inner0S_two_eq_coord (I := I) g x basis gInv hinv A B]
  rfl


private lemma ricReact_two {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv ric : Idx -> Idx -> Real)
    (cT : (Fin 2 -> Idx) -> Real)
    (Q T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (hgsym : ∀ i j : Idx, gInv i j = gInv j i)
    (hric : ∀ i j : Idx, ric i j = Q (vec2 (I := I) (basis i) (basis j)))
    (hcT : ∀ u v : Idx,
      cT (fun a : Fin 2 => if a = 0 then u else v) = T (vec2 (I := I) (basis u) (basis v)))
    (hQsymm : ∀ X Y : TangentSpace I x, Q (vec2 (I := I) X Y) = Q (vec2 (I := I) Y X)) :
    ricReactionContract gInv ric cT cT = ricciReactionInner (I := I) g x Q T := by
  classical
  have hRic : ∀ p k : Idx,
      (∑ i : Idx, gInv i k * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))) =
        ∑ a : Idx, ∑ b : Idx, gInv p a * gInv k b * Q (vec2 (I := I) (basis a) (basis b)) := by
    intro p k
    calc (∑ i : Idx, gInv i k * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m))))
        = ∑ i : Idx, ∑ m : Idx,
            gInv i k * (gInv p m * Q (vec2 (I := I) (basis i) (basis m))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ m : Idx, ∑ i : Idx,
            gInv i k * (gInv p m * Q (vec2 (I := I) (basis i) (basis m))) :=
          Finset.sum_comm
      _ = ∑ a : Idx, ∑ b : Idx, gInv p a * gInv k b * Q (vec2 (I := I) (basis a) (basis b)) := by
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
          rw [hgsym i k, hQsymm (basis i) (basis m)]
          ring
  have hexp : ricReactionContract gInv ric cT cT
      = 2 * ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (gInv j l * (∑ a : Idx, ∑ b : Idx,
              gInv i a * gInv k b * Q (vec2 (I := I) (basis a) (basis b)))
            + gInv i k * (∑ a : Idx, ∑ b : Idx,
                gInv j a * gInv l b * Q (vec2 (I := I) (basis a) (basis b))))
            * T (vec2 (I := I) (basis i) (basis j)) * T (vec2 (I := I) (basis k) (basis l)) := by
    unfold ricReactionContract
    simp only [sum_fin_two]
    beta_reduce
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hcT i j, hcT k l]
    have he0 : ((Finset.univ : Finset (Fin 2)).erase 0) = {1} := by decide
    have he1 : ((Finset.univ : Finset (Fin 2)).erase 1) = {0} := by decide
    rw [Fin.sum_univ_two, he0, he1, Finset.prod_singleton, Finset.prod_singleton]
    have hif0 : (if (0 : Fin 2) = 0 then i else j) = i := if_pos rfl
    have hif1 : (if (1 : Fin 2) = 0 then i else j) = j := if_neg (by decide)
    have hif0' : (if (0 : Fin 2) = 0 then k else l) = k := if_pos rfl
    have hif1' : (if (1 : Fin 2) = 0 then k else l) = l := if_neg (by decide)
    rw [hif0, hif1, hif0', hif1']
    simp only [hric]
  have hinner1 : inner0S (I := I) g x 2
        (endoSlotFirst (I := I) (ricciSharpEndo (I := I) g x Q) T) T
      = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i k * gInv j l *
            (∑ p : Idx, (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))
              * T (vec2 (I := I) (basis p) (basis j)))
            * T (vec2 (I := I) (basis k) (basis l)) := by
    rw [inner0S_two_coord_vec2 (I := I) g basis gInv hinv
      (endoSlotFirst (I := I) (ricciSharpEndo (I := I) g x Q) T) T]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hval : endoSlotFirst (I := I) (ricciSharpEndo (I := I) g x Q) T
        (vec2 (I := I) (basis i) (basis j))
        = ∑ p : Idx, (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))
            * T (vec2 (I := I) (basis p) (basis j)) := by
      rw [endoSlotFirst_apply (I := I) (ricciSharpEndo (I := I) g x Q) T (basis i) (basis j),
        ricciSharpEndo_basis_expand (I := I) g basis gInv hinv Q i,
        tensor2_first_slot_sum (I := I) T
          (fun p => ∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))
          (fun p => basis p) (basis j)]
    rw [hval]
  have hinner2 : inner0S (I := I) g x 2
        (endoSlotSecond (I := I) (ricciSharpEndo (I := I) g x Q) T) T
      = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i k * gInv j l *
            (∑ p : Idx, (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis j) (basis m)))
              * T (vec2 (I := I) (basis i) (basis p)))
            * T (vec2 (I := I) (basis k) (basis l)) := by
    rw [inner0S_two_coord_vec2 (I := I) g basis gInv hinv
      (endoSlotSecond (I := I) (ricciSharpEndo (I := I) g x Q) T) T]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hval : endoSlotSecond (I := I) (ricciSharpEndo (I := I) g x Q) T
        (vec2 (I := I) (basis i) (basis j))
        = ∑ p : Idx, (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis j) (basis m)))
            * T (vec2 (I := I) (basis i) (basis p)) := by
      rw [endoSlotSecond_apply (I := I) (ricciSharpEndo (I := I) g x Q) T (basis i) (basis j),
        ricciSharpEndo_basis_expand (I := I) g basis gInv hinv Q j,
        tensor2_second_slot_sum (I := I) T
          (fun p => ∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis j) (basis m)))
          (fun p => basis p) (basis i)]
    rw [hval]
  have hpiece1 :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i k * gInv j l *
            (∑ p : Idx, (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))
              * T (vec2 (I := I) (basis p) (basis j)))
            * T (vec2 (I := I) (basis k) (basis l)))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv j l * (∑ a : Idx, ∑ b : Idx,
                gInv i a * gInv k b * Q (vec2 (I := I) (basis a) (basis b)))
              * T (vec2 (I := I) (basis i) (basis j))
              * T (vec2 (I := I) (basis k) (basis l)) := by
    calc (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * gInv j l *
              (∑ p : Idx, (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))
                * T (vec2 (I := I) (basis p) (basis j)))
              * T (vec2 (I := I) (basis k) (basis l)))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
            gInv j l * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis p) (basis j))
              * (gInv i k * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ = ∑ i : Idx, ∑ p : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv j l * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis p) (basis j))
              * (gInv i k * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact sum4_pull _
      _ = ∑ p : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv j l * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis p) (basis j))
              * (gInv i k * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))) :=
          Finset.sum_comm
      _ = ∑ p : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ i : Idx,
            gInv j l * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis p) (basis j))
              * (gInv i k * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          exact sum4_push _
      _ = ∑ p : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv j l * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis p) (basis j))
              * (∑ i : Idx, gInv i k * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis i) (basis m)))) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum]
      _ = ∑ p : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv j l * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis p) (basis j))
              * (∑ a : Idx, ∑ b : Idx,
                  gInv p a * gInv k b * Q (vec2 (I := I) (basis a) (basis b))) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [hRic p k]
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv j l * (∑ a : Idx, ∑ b : Idx,
                gInv i a * gInv k b * Q (vec2 (I := I) (basis a) (basis b)))
              * T (vec2 (I := I) (basis i) (basis j))
              * T (vec2 (I := I) (basis k) (basis l)) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  have hpiece2 :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i k * gInv j l *
            (∑ p : Idx, (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis j) (basis m)))
              * T (vec2 (I := I) (basis i) (basis p)))
            * T (vec2 (I := I) (basis k) (basis l)))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * (∑ a : Idx, ∑ b : Idx,
                gInv j a * gInv l b * Q (vec2 (I := I) (basis a) (basis b)))
              * T (vec2 (I := I) (basis i) (basis j))
              * T (vec2 (I := I) (basis k) (basis l)) := by
    calc (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * gInv j l *
              (∑ p : Idx, (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis j) (basis m)))
                * T (vec2 (I := I) (basis i) (basis p)))
              * T (vec2 (I := I) (basis k) (basis l)))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
            gInv i k * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis i) (basis p))
              * (gInv j l * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis j) (basis m)))) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ = ∑ i : Idx, ∑ p : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis i) (basis p))
              * (gInv j l * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis j) (basis m)))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact sum4_pull _
      _ = ∑ i : Idx, ∑ p : Idx, ∑ k : Idx, ∑ l : Idx, ∑ j : Idx,
            gInv i k * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis i) (basis p))
              * (gInv j l * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis j) (basis m)))) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
          exact sum3_rotate _
      _ = ∑ i : Idx, ∑ p : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis i) (basis p))
              * (∑ j : Idx, gInv j l * (∑ m : Idx, gInv p m * Q (vec2 (I := I) (basis j) (basis m)))) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum]
      _ = ∑ i : Idx, ∑ p : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * T (vec2 (I := I) (basis k) (basis l))
              * T (vec2 (I := I) (basis i) (basis p))
              * (∑ a : Idx, ∑ b : Idx,
                  gInv p a * gInv l b * Q (vec2 (I := I) (basis a) (basis b))) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [hRic p l]
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * (∑ a : Idx, ∑ b : Idx,
                gInv j a * gInv l b * Q (vec2 (I := I) (basis a) (basis b)))
              * T (vec2 (I := I) (basis i) (basis j))
              * T (vec2 (I := I) (basis k) (basis l)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  have hsplit : (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (gInv j l * (∑ a : Idx, ∑ b : Idx,
            gInv i a * gInv k b * Q (vec2 (I := I) (basis a) (basis b)))
          + gInv i k * (∑ a : Idx, ∑ b : Idx,
              gInv j a * gInv l b * Q (vec2 (I := I) (basis a) (basis b))))
          * T (vec2 (I := I) (basis i) (basis j)) * T (vec2 (I := I) (basis k) (basis l)))
      = (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv j l * (∑ a : Idx, ∑ b : Idx,
              gInv i a * gInv k b * Q (vec2 (I := I) (basis a) (basis b)))
            * T (vec2 (I := I) (basis i) (basis j)) * T (vec2 (I := I) (basis k) (basis l)))
        + ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * (∑ a : Idx, ∑ b : Idx,
                gInv j a * gInv l b * Q (vec2 (I := I) (basis a) (basis b)))
              * T (vec2 (I := I) (basis i) (basis j)) * T (vec2 (I := I) (basis k) (basis l)) := by
    calc (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (gInv j l * (∑ a : Idx, ∑ b : Idx,
              gInv i a * gInv k b * Q (vec2 (I := I) (basis a) (basis b)))
            + gInv i k * (∑ a : Idx, ∑ b : Idx,
                gInv j a * gInv l b * Q (vec2 (I := I) (basis a) (basis b))))
            * T (vec2 (I := I) (basis i) (basis j)) * T (vec2 (I := I) (basis k) (basis l)))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            (gInv j l * (∑ a : Idx, ∑ b : Idx,
                gInv i a * gInv k b * Q (vec2 (I := I) (basis a) (basis b)))
              * T (vec2 (I := I) (basis i) (basis j)) * T (vec2 (I := I) (basis k) (basis l))
            + gInv i k * (∑ a : Idx, ∑ b : Idx,
                gInv j a * gInv l b * Q (vec2 (I := I) (basis a) (basis b)))
              * T (vec2 (I := I) (basis i) (basis j)) * T (vec2 (I := I) (basis k) (basis l))) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = _ := by
          simp only [Finset.sum_add_distrib]
  rw [hexp,
    show ricciReactionInner (I := I) g x Q T
      = 2 * (inner0S (I := I) g x 2
          (endoSlotFirst (I := I) (ricciSharpEndo (I := I) g x Q) T) T
        + inner0S (I := I) g x 2
            (endoSlotSecond (I := I) (ricciSharpEndo (I := I) g x Q) T) T) from rfl,
    hinner1, hinner2, hpiece1, hpiece2, hsplit]


private lemma comp_two_eq_vec2 {x : M} {Idx : Type*}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) (u v : Idx) :
    tensor0SComponent (I := I) T (fun i => basis i) (fun a : Fin 2 => if a = 0 then u else v)
      = T (vec2 (I := I) (basis u) (basis v)) := by
  change T (fun a : Fin 2 => basis (if a = 0 then u else v)) = T (vec2 (I := I) (basis u) (basis v))
  congr 1
  funext a
  by_cases hcase : a = 0 <;>
    simp [hcase, vec2, DifferentialGeometry.Integral.Connection.vec2]


private lemma inner0S_add_left {x : M}
    (g : SmoothMetric I M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s (A + B) C =
      inner0S (I := I) g x s A C + inner0S (I := I) g x s B C := by
  unfold inner0S MetricFiberData.inner
  rw [map_add]
  rfl


private lemma normSq_two_time {x : M} {t : Real}
    (g : Real -> SmoothMetric I M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hQsymm : ∀ X Y : TangentSpace I x, Q (vec2 (I := I) X Y) = Q (vec2 (I := I) Y X))
    (A : Real -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (Adot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (vec2 (I := I) X Y)) t)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => A r (vec2 (I := I) X Y)) (Adot (vec2 (I := I) X Y)) t) :
    HasDerivAt
      (fun r : Real => normSq0S (I := I) (g r) x 2 (A r))
      (ricciReactionInner (I := I) (g t) x Q (A t) +
        2 * inner0S (I := I) (g t) x 2 Adot (A t)) t := by
  classical
  let basis : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  let gInv : Real ->
      Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) -> Real := fun r =>
    basisInvMetric (I := I) (g r) x basis
  let ric :
      Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) -> Real := fun i j =>
    Q (vec2 (I := I) (basis i) (basis j))
  let gInvDt :
      Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) -> Real := fun i j =>
    -(∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j)
  let Tdt :
      (Fin 2 -> Fin (Module.finrank Real (TangentSpace I x))) -> Real := fun I0 =>
    tensor0SComponent (I := I) Adot (fun i => basis i) I0
  have hinvAll (r : Real) :
      MetricInverseInBasis (I := I) (g r) x basis (gInv r) := by
    simpa [gInv] using basisInvMetric_real (I := I) (g r) x basis
  have hgInv (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) Set.univ t := by
    simpa [gInv, gInvDt, ric] using
      (basisInv_time (I := I) g
        (fun p q => (-2 : Real) * ric p q) basis
        (fun p q => by simpa [ric] using hg (basis p) (basis q)) i j)
  have hT (I0 : Fin 2 -> Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (A r) (fun i => basis i) I0)
        (Tdt I0) Set.univ t := by
    have hslots :
        (fun a : Fin 2 => basis (I0 a)) = vec2 (I := I) (basis (I0 0)) (basis (I0 1)) := by
      funext a
      fin_cases a <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
    have hslots' : (fun a : Fin 2 => (basis : _ -> TangentSpace I x) (I0 a)) =
        vec2 (I := I) (basis (I0 0)) (basis (I0 1)) := hslots
    change HasDerivWithinAt
      (fun r : Real => A r (fun a : Fin 2 => basis (I0 a)))
      (Adot (fun a : Fin 2 => basis (I0 a))) Set.univ t
    rw [hslots]
    exact (hA (basis (I0 0)) (basis (I0 1))).hasDerivWithinAt
  have hTdot (I0 : Fin 2 -> Fin (Module.finrank Real (TangentSpace I x))) :
      tensor0SComponent (I := I) Adot (fun i => basis i) I0 = Tdt I0 := by
    rfl
  have hflow (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      gInvDt i j =
        2 * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
    have hterm :
        (∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j) =
          ∑ p, ∑ q, (-2 : Real) *
            (gInv t i p * gInv t j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [gInv]
      rw [basisInvMetric_symm (I := I) (g t) x basis q j]
      ring
    have hfactor :
        (∑ p, ∑ q, (-2 : Real) *
            (gInv t i p * gInv t j q * ric p q)) =
          (-2 : Real) *
            (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    simp only [gInvDt]
    rw [hterm, hfactor]
    ring
  have hbase :=
    hasDerivWithinAt_normSq0S_ricciFlow
      (I := I) (s := 2) (u := Set.univ) (t := t)
      g gInv gInvDt ric A Tdt Adot basis hinvAll hgInv hT hTdot hflow
  have hat := hbase.hasDerivAt (by simp)
  rw [show gInv t = basisInvMetric (I := I) (g t) x basis from rfl,
    show ric = fun i j => Q (vec2 (I := I) (basis i) (basis j)) from rfl] at hat
  rw [ricReact_two (I := I) (g t) basis
      (basisInvMetric (I := I) (g t) x basis)
      (fun i j => Q (vec2 (I := I) (basis i) (basis j)))
      (fun I0 => tensor0SComponent (I := I) (A t) (fun i => basis i) I0)
      Q (A t)
      (by simpa using basisInvMetric_real (I := I) (g t) x basis)
      (basisInvMetric_symm (I := I) (g t) x basis)
      (fun _ _ => rfl)
      (fun u v => comp_two_eq_vec2 (I := I) basis (A t) u v)
      hQsymm] at hat
  exact hat


private lemma ricci_symm_of_solution
    [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : IsRealizedRicciFlowSolutionOn (I := I) S)
    (t₀ : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x) :
    S.ricci (t₀ : Real) x X Y = S.ricci (t₀ : Real) x Y X := by
  have h1 := (hS.equation t₀ x X Y).hasDerivAt (D.regular_mem_nhds t₀.2)
  have h2 := (hS.equation t₀ x Y X).hasDerivAt (D.regular_mem_nhds t₀.2)
  have hfun : (fun s : Real => (S.family.metric s).inner x Y X)
      = (fun s : Real => (S.family.metric s).inner x X Y) := by
    funext s
    exact (S.family.metric s).symm x Y X
  rw [hfun] at h2
  have huniq := h1.unique h2
  linarith


private lemma fin1_eta' {x : M} (slots : Fin 1 -> TangentSpace I x) :
    slots = fun _ : Fin 1 => slots 0 := by
  funext q
  rw [Subsingleton.elim q 0]

private lemma toRS0_one0_eval {s : ℕ} {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    Tensor0SSpace.toRS0 A
        (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ x) = A := by
  rw [Tensor0SSpace.toRS0_apply]
  have h1 : tensor0SSpace_evalScalar x
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply]
    exact Tensor0SField.one0_apply (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      ∞ x Fin.elim0
  rw [h1, one_smul]

private lemma oneFormRealizes_toTotal
    [T2Space M] [SigmaCompactSpace M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (α : OneFormSection (I := I) (M := M))
    (β : TwoTensorSection (I := I) (M := M))
    (h1 : NablaOneFormSectionRealizes (I := I) cov α β) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov α β := by
  intro X x slots
  have h2 := (h1 x) X (slots 0)
  have hcons : (Fin.cons (X x) slots : Fin 2 -> TangentSpace I x) =
      vec2 (I := I) (X x) (slots 0) := by
    rw [vec2_eq_cons, ← fin1_eta' (I := I) slots]
  rw [hcons, h2]
  exact congrArg _ (fin1_eta' (I := I) slots).symm

private lemma abstract1'
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hLC : IsLeviCivita (I := I) cov g)
    (α : OneFormSection (I := I) (M := M))
    (Xf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (y : M) (w : TangentSpace I y) :
    Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
          (fun z => α z) y (Xf y)) (fun _ : Fin 1 => w) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov Xf α y (fun _ : Fin 1 => w) := by
  classical
  set Zf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) y w, smoothExtensionTangent_contMDiff (I := I) y w⟩
    with hZfdef
  have hZfy : Zf y = w := smoothExtensionTangent_eq (I := I) y w
  have htmd : TensorSectionMDiffAt (I := I) 1 (fun z => α z) y :=
    α.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpeel := peel1_koszul (I := I) (M := M) g (fun z => α z) htmd Zf (Xf y)
  have hLCeq : (LeviCivita (I := I) g).toFun (fun z => Zf z) y (Xf y) =
      (cov (fun z => Zf z) y) (Xf y) :=
    leviCivita_apply_eq_of_smooth_direction
      (I := I) (cov := LeviCivita (I := I) g) (cov' := cov)
      inferInstance inferInstance
      (leviCivitaConnectionOfMetric_isLeviCivita (I := I) g) hLC
      (fun z => Zf z) (Zf.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Xf y)
  have hev := nabla0SFun_one_eval_smooth_slots (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    cov Xf Zf α y
  have hsc : scalarFn I M (fun z : M => curriedSection I M (fun z' => α z') z (Zf z)) =
      (fun p : M => α p (fun _ : Fin 1 => Zf p)) := by
    funext z
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M), curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := α z) (v0 := Zf z) (vs := fun i => Fin.elim0 i), toModel0S_apply]
    congr 1
    funext i; fin_cases i; rfl
  rw [← hZfy]
  conv_lhs =>
    rw [show (fun _ : Fin 1 => Zf y) = ![Zf y] from by funext i; fin_cases i; rfl, hpeel]
  rw [hev, hsc]
  congr 1
  rw [toModel0S_apply, hLCeq]
  congr 1
  funext i; fin_cases i; rfl

private lemma smoothCcTensor_unit_contMDiff
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : SmoothCcTensor (I := I) (M := M) g 0 s) :
    ContMDiff I (I.prod 𝓘(Real, Tensor0SModel s Real E)) (∞ : WithTop ℕ∞)
      (fun y : M => TotalSpace.mk' (Tensor0SModel s Real E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (T.toSection y
          (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ y))) := by
  exact ContMDiff.clm_bundle_apply (𝕜 := Real) (n := (∞ : WithTop ℕ∞))
    (F₁ := Tensor0SModel 0 Real E) (F₂ := Tensor0SModel s Real E)
    (E₁ := fun z : M => Tensor0SSpace 0 I z)
    (E₂ := fun z : M => Tensor0SSpace s I z)
    (IM := I) (IB := I) (b := id)
    (ϕ := fun y : M =>
      (show Tensor0SSpace 0 I y →L[Real] Tensor0SSpace s I y from T.toSection y))
    (v := fun y : M =>
      Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ y)
    T.toSection.contMDiff
    (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞).contMDiff

private noncomputable def unitValField
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : SmoothCcTensor (I := I) (M := M) g 0 s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  ⟨fun y : M => T.toSection y
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ y),
    smoothCcTensor_unit_contMDiff (I := I) (M := M) g T⟩

private lemma unitValField_apply
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : SmoothCcTensor (I := I) (M := M) g 0 s) (y : M) :
    unitValField (I := I) (M := M) g T y =
      T.toSection y
        (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ y) := rfl

private lemma toSection_eq_toRS0_unitValField
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : SmoothCcTensor (I := I) (M := M) g 0 s) (y : M) :
    T.toSection y = Tensor0SSpace.toRS0 (unitValField (I := I) (M := M) g T y) := by
  rw [unitValField_apply]
  exact (toRS0_eval_one0 (I := I) (M := M) y (T.toSection y)).symm

private lemma covGrad_unit_realizes
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hLC : IsLeviCivita (I := I) cov g)
    (Wcc : SmoothCcTensor (I := I) (M := M) g 0 1) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov
      (unitValField (I := I) (M := M) g Wcc)
      (unitValField (I := I) (M := M) g
        (TensorSpectral.covGrad (I := I) (M := M) g 0 1 Wcc)) := by
  intro X x slots
  have hslots := fin1_eta' (I := I) slots
  have hWsec : (fun y : M => Wcc.toSection y) =
      (fun y : M => (unitValField (I := I) (M := M) g Wcc).toTensorRSField ∞ y) := by
    funext y
    rw [Tensor0SField.toRS0_eq]
    exact toSection_eq_toRS0_unitValField (I := I) (M := M) g Wcc y
  change Tensor0SSpace.toModel
      ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 Wcc).toSection x
        (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ x))
      (Fin.cons (X x) slots) = _
  rw [TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M) g 0 1 Wcc x
    (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ x)
    (Fin.cons (X x) slots)]
  rw [show (Fin.cons (X x) slots : Fin 2 -> TangentSpace I x) 0 = X x from rfl]
  rw [show Matrix.vecTail (Fin.cons (X x) slots : Fin 2 -> TangentSpace I x) = slots from by
    funext q
    simp [Matrix.vecTail]]
  rw [TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) g 0 1 Wcc x (X x)]
  rw [hWsec]
  rw [nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) g)
    (unitValField (I := I) (M := M) g Wcc) x (X x)]
  rw [toRS0_one0_eval (I := I) (M := M)]
  rw [hslots]
  exact abstract1' (I := I) (M := M) g cov hLC
    (unitValField (I := I) (M := M) g Wcc) X x (slots 0)

section GammaClones

variable [T2Space M] [SigmaCompactSpace M]
variable {Idx : Type} [Fintype Idx] [DecidableEq Idx] {u : Set M}

private lemma coeff_invMetric_pt
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u)
    (hinvx : ∀ i j : Idx,
      (∑ k : Idx, gInv x i k * g.inner x (frame k x) (frame j x)) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx, g.inner x (frame i x) (frame k x) * gInv x k j) =
          (if i = j then 1 else 0))
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv x k l * g.inner x (frame l x) V := by
  let basis := hframe.toBasisAt hx
  have hcoord :
      basis.coord k V =
        ∑ l : Idx, gInv x k l * g.inner x (basis l) V := by
    symm
    calc
      (∑ l : Idx, gInv x k l * g.inner x (basis l) V)
          = ∑ l : Idx, gInv x k l *
              g.inner x (basis l) (∑ j : Idx, basis.coord j V • basis j) := by
            rw [show (∑ j : Idx, basis.coord j V • basis j) = V from basis.sum_repr V]
      _ = ∑ l : Idx, ∑ j : Idx,
            gInv x k l * (basis.coord j V * g.inner x (basis l) (basis j)) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_sum]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j : Idx, basis.coord j V *
            (∑ l : Idx, gInv x k l * g.inner x (basis l) (basis j)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = ∑ j : Idx, basis.coord j V * (if k = j then 1 else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [show
              (∑ l : Idx, gInv x k l * g.inner x (basis l) (basis j)) =
                (if k = j then 1 else 0) by
                  simpa [basis, IsLocalFrameOn.toBasisAt_coe] using (hinvx k j).1]
      _ = basis.coord k V := by
            simp
  calc
    hframe.coeff k x V = basis.coord k V := by
      simp [basis, IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv x k l * g.inner x (frame l x) V := by
      simpa [basis, IsLocalFrameOn.toBasisAt_coe] using hcoord

private lemma gammaDerivOfLower_on
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real)
    (hinvOn : ∀ x : M, x ∈ u -> ∀ i j : Idx,
      (∑ k : Idx, gInv x i k * (G.metric base).inner x (frame k x) (frame j x)) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx, (G.metric base).inner x (frame i x) (frame k x) * gInv x k j) =
          (if i = j then 1 else 0))
    (hlower : lowerPairDerivOn (I := I) G frame base u lowerDot) :
    gammaDerivOn (I := I) G frame hframe base u
      (fun x k i j => gammaFromLower gInv lowerDot x i j k) := by
  intro x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (G.metric base).inner x (frame l x)
        ((G.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivAt
        (fun s : Real => ∑ l : Idx, gInv x k l * pair l s)
        (∑ l : Idx, gInv x k l * lowerDot x i j l)
        base := by
    simpa [pair] using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv x k l * pair l s)
        (A' := fun l => gInv x k l * lowerDot x i j l)
        (x := base)
        (fun l _hl =>
          HasDerivAt.const_mul
            (gInv x k l) (hlower x hx i j l)))
  have hEq :
      (fun s : Real =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k) =ᶠ[nhds base]
        (fun s : Real => ∑ l : Idx, gInv x k l * pair l s) := by
    exact Filter.Eventually.of_forall fun s => by
      simpa [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame, pair] using
        coeff_invMetric_pt (I := I) (M := M)
          (G.metric base) gInv frame hframe hx (hinvOn x hx) k
          ((G.connection s (frame j) x) (frame i x))
  simpa [gammaFromLower, pair] using hsum.congr_of_eventuallyEq hEq

private lemma lcGammaVar_on
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hinvOn : ∀ x : M, x ∈ u -> ∀ i j : Idx,
      (∑ k : Idx, gInv x i k * (G.metric base).inner x (frame k x) (frame j x)) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx, (G.metric base).inner x (frame i x) (frame k x) * gInv x k j) =
          (if i = j then 1 else 0))
    (hmetricVar :
      metricVarOn (I := I) G frame base u metricDot)
    (hmetric :
      metricCovVarOn (I := I) G frame base u metricCovDerivDt)
    (hgamma :
      gammaDerivOn (I := I) G frame hframe base u gammaDot) :
    gammaVarEqOn gInv metricCovDerivDt gammaDot u := by
  intro x hx i j k
  have hlow :
      ∀ l : Idx,
        (∑ a : Idx,
          gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x)) =
          metricVarLowerRHS metricCovDerivDt x i j l := by
    intro l
    have hL :
        HasDerivAt
          (fun s : Real =>
            2 * connDiffLow (I := I) G frame s base s x i j l)
          (2 * ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x))
          base := by
      exact HasDerivAt.const_mul (2 : Real)
        (varLowDeriv (I := I) G frame hframe base metricDot gammaDot
          hmetricVar hgamma hx i j l)
    have hR :
        HasDerivAt
          (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j)
          (metricCovDerivDt x i j l +
            metricCovDerivDt x j i l - metricCovDerivDt x l i j)
          base := by
      exact ((hmetric x hx i j l).add (hmetric x hx j i l)).sub
        (hmetric x hx l i j)
    have hEq :
        (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j) =ᶠ[nhds base]
          (fun s : Real =>
            2 * connDiffLow (I := I) G frame s base s x i j l) := by
      exact Filter.Eventually.of_forall fun s => by
        exact (finiteDiffKoszul (I := I) G hLC frame hframe hu hx base s i j l).symm
    have hL_as_R :
        HasDerivAt
          (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j)
          (2 * ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x))
          base := hL.congr_of_eventuallyEq hEq
    have hderiv :
        2 * (∑ a : Idx,
          gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x)) =
          metricCovDerivDt x i j l +
            metricCovDerivDt x j i l - metricCovDerivDt x l i j :=
      hL_as_R.unique hR
    unfold metricVarLowerRHS
    linarith
  let V : TangentSpace I x :=
    ∑ a : Idx, gammaDot x a i j • frame a x
  have hcoeff :
      hframe.coeff k x V = gammaDot x k i j := by
    let basis := hframe.toBasisAt hx
    have hbasis :
        ∀ a : Idx, basis.repr (frame a x) k = if a = k then 1 else 0 := by
      intro a
      have hframe_eq : frame a x = basis a := by
        simp [basis]
      rw [hframe_eq]
      by_cases h : a = k
      · subst k
        simp
      · simp [h]
    calc
      hframe.coeff k x V = basis.repr V k := by
        simp [basis, IsLocalFrameOn.coeff, hx]
      _ = ∑ a : Idx, gammaDot x a i j * basis.repr (frame a x) k := by
        simp [V, map_sum, map_smul, smul_eq_mul]
      _ = ∑ a : Idx, gammaDot x a i j * (if a = k then 1 else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hbasis a]
      _ = gammaDot x k i j := by
        simp
  have hinner :
      ∀ l : Idx,
        (G.metric base).inner x (frame l x) V =
          metricVarLowerRHS metricCovDerivDt x i j l := by
    intro l
    calc
      (G.metric base).inner x (frame l x) V =
          ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame l x) (frame a x) := by
            simp [V, map_sum, smul_eq_mul]
      _ = ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [(G.metric base).symm x (frame l x) (frame a x)]
      _ = metricVarLowerRHS metricCovDerivDt x i j l := hlow l
  calc
    gammaDot x k i j = hframe.coeff k x V := hcoeff.symm
    _ = ∑ l : Idx, gInv x k l * (G.metric base).inner x (frame l x) V := by
      exact coeff_invMetric_pt (I := I) (M := M)
        (G.metric base) gInv frame hframe hx (hinvOn x hx) k V
    _ = ∑ l : Idx, gInv x k l * metricVarLowerRHS metricCovDerivDt x i j l := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hinner l]
    _ = metricVarGammaRHS gInv metricCovDerivDt x i j k := by
      rfl

end GammaClones

private lemma christoffel_dt_ricciFlow
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : IsRealizedRicciFlowSolutionOn (I := I) S)
    (ricT : Real -> TwoTensorSection (I := I) (M := M))
    (hricT : forall (t : Real) (x : M) (X Y : TangentSpace I x),
      (ricT t) x (vec2 X Y) = S.ricci t x X Y)
    (t₀ : RealTimeInterval.RegularTime D)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (frame : Idx -> (y : M) -> TangentSpace I y) {u : Set M}
    (hframeInf : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hframe1 : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (gInv : M -> Idx -> Idx -> Real)
    (hinvOn : ∀ y : M, y ∈ u -> ∀ i j : Idx,
      (∑ k : Idx, gInv y i k *
          (S.family.metric (t₀ : Real)).inner y (frame k y) (frame j y)) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx, (S.family.metric (t₀ : Real)).inner y (frame i y) (frame k y) *
            gInv y k j) =
          (if i = j then 1 else 0)) :
    ∃ gammaDot : M -> Idx -> Idx -> Idx -> Real,
      (∀ y : M, y ∈ u -> ∀ i j k : Idx,
        HasDerivAt
          (fun s : Real =>
            christoffelSymbolInFrame (S.family.connection s) frame hframe1 y i j k)
          (gammaDot y k i j) (t₀ : Real)) ∧
      (∀ y : M, y ∈ u -> ∀ i j k : Idx,
        gammaDot y k i j =
          metricVarGammaRHS gInv
            (dotCovAt (I := I) (S.family.connection (t₀ : Real)) frame hframe1
              (fun z a b => (-2 : Real) *
                ricT (t₀ : Real) z (vec2 (I := I) (frame a z) (frame b z))))
            y i j k) := by
  classical
  obtain ⟨ρ, hρsmooth, hρmem, hρeq⟩ := exists_time_retract D.regular_isOpen t₀.2
  have hρt : ρ (t₀ : Real) = (t₀ : Real) := hρeq.eq_of_nhds
  have hρmdiff : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ ρ := by
    rw [contMDiff_iff_contDiff]; exact hρsmooth
  have hinnerρ : ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M => (ρ p.1, p.2)) :=
    (hρmdiff.comp contMDiff_fst).prodMk contMDiff_snd
  let Gr : RealizedMetricFamilyOn (I := I) (M := M) D :=
    { metric := fun s => S.family.metric (ρ s)
      connection := fun s => S.family.connection (ρ s)
      metricCompatible := fun t =>
        S.family.metricCompatible ⟨ρ (t : Real), D.regular_subset (hρmem (t : Real))⟩ }
  have hLCall : ∀ s : Real, IsLeviCivita (I := I) (Gr.connection s) (Gr.metric s) := by
    intro s
    have hmc : IsMetricCompatible_gen (I := I)
        (S.family.connection (ρ s)) (S.family.metric (ρ s)) :=
      hS.leviCivita.1 ⟨ρ s, D.regular_subset (hρmem s)⟩
    have htf : IsTorsionFree (I := I) (S.family.connection (ρ s)) :=
      hS.leviCivita.2 ⟨ρ s, D.regular_subset (hρmem s)⟩
    exact isLeviCivita_of_parts hmc htf
  have hsmoothGr : MetricFamilySmoothOn (I := I) (M := M) D Gr := by
    refine
      { coeff := ?_
        coeff_cont := ?_
        metricTensor_cont := ?_
        frameCompSmooth := ?_ }
    · intro x X Y
      have h0 := hS.smoothMetric.coeff x X Y
      have hρon : ContDiffOn Real ∞ ρ D.regular := hρsmooth.contDiffOn
      have hcomp := h0.comp hρon (fun s _ => hρmem s)
      simpa [Function.comp] using hcomp
    · intro x X Y
      have h0 := hS.smoothMetric.coeff_cont x X Y
      have hρonC : ContinuousOn ρ D.carrier := hρsmooth.continuous.continuousOn
      have hcomp := ContinuousOn.comp h0 hρonC
        (fun s _ => D.regular_subset (hρmem s))
      simpa [Function.comp] using hcomp
    · have h0 := hS.smoothMetric.metricTensor_cont
      unfold Tensor0SFamilyContinuousOnSet at h0 ⊢
      let φ : {t : Real // t ∈ D.carrier} × M -> {t : Real // t ∈ D.carrier} × M :=
        fun q => (⟨ρ q.1.1, D.regular_subset (hρmem q.1.1)⟩, q.2)
      have hφ : Continuous φ := by
        refine Continuous.prodMk ?_ continuous_snd
        exact (hρsmooth.continuous.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _
      exact h0.comp hφ
    · intro Idx' _ frame' u' hframe' i j
      have h0 := hS.smoothMetric.frameCompSmooth frame' hframe' i j
      have hcomp := h0.comp hinnerρ.contMDiffOn (by
        intro p (hp : p ∈ D.regular ×ˢ u')
        exact ⟨hρmem p.1, hp.2⟩)
      simpa [Function.comp] using hcomp
  have hbase : D.regular ∈ nhds (t₀ : Real) := D.regular_isOpen.mem_nhds t₀.2
  have hlower := lowerPairDeriv_of_metricFamilySmoothOn (I := I) Gr hLCall hsmoothGr
    frame hframeInf hu (t₀ : Real) hbase
  have hGrmet : (Gr.toRealizedMetricFamily hLCall).metric (t₀ : Real) =
      S.family.metric (t₀ : Real) := by
    change S.family.metric (ρ (t₀ : Real)) = S.family.metric (t₀ : Real)
    rw [hρt]
  have hGrconn : (Gr.toRealizedMetricFamily hLCall).connection (t₀ : Real) =
      S.family.connection (t₀ : Real) := by
    change S.family.connection (ρ (t₀ : Real)) = S.family.connection (t₀ : Real)
    rw [hρt]
  have hinvOn' : ∀ y : M, y ∈ u -> ∀ i j : Idx,
      (∑ k : Idx, gInv y i k *
          ((Gr.toRealizedMetricFamily hLCall).metric (t₀ : Real)).inner y
            (frame k y) (frame j y)) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx,
            ((Gr.toRealizedMetricFamily hLCall).metric (t₀ : Real)).inner y
              (frame i y) (frame k y) * gInv y k j) =
          (if i = j then 1 else 0) := by
    intro y hy i j
    rw [hGrmet]
    exact hinvOn y hy i j
  have hgammaGr := gammaDerivOfLower_on (I := I) (M := M)
    (Gr.toRealizedMetricFamily hLCall) gInv frame hframe1 (t₀ : Real)
    (connectionPairingTimeDeriv (I := I) (Gr.toRealizedMetricFamily hLCall) frame (t₀ : Real))
    hinvOn' hlower
  refine ⟨fun x k i j =>
    gammaFromLower gInv
      (connectionPairingTimeDeriv (I := I) (Gr.toRealizedMetricFamily hLCall) frame (t₀ : Real))
      x i j k, ?_, ?_⟩
  · intro y hy i j k
    have h0 := hgammaGr y hy i j k
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [hρeq] with s hs
    have hcs : (Gr.toRealizedMetricFamily hLCall).connection s = S.family.connection s := by
      change S.family.connection (ρ s) = S.family.connection s
      rw [hs]
    rw [hcs]
  · intro y hy i j k
    have hflowGr : metricVarOn (I := I) (Gr.toRealizedMetricFamily hLCall) frame (t₀ : Real) u
        (fun z a b => (-2 : Real) *
          ricT (t₀ : Real) z (vec2 (I := I) (frame a z) (frame b z))) := by
      intro z hz a b
      beta_reduce
      have h1 := (hS.equation t₀ z (frame a z) (frame b z)).hasDerivAt
        (D.regular_mem_nhds t₀.2)
      have h2 : (-2 : Real) * ricT (t₀ : Real) z (vec2 (I := I) (frame a z) (frame b z)) =
          (-2 : Real) * S.ricci (t₀ : Real) z (frame a z) (frame b z) := by
        rw [hricT]
      rw [h2]
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hρeq] with s hs
      change ((Gr.toRealizedMetricFamily hLCall).metric s).inner z (frame a z) (frame b z) =
        (S.family.metric s).inner z (frame a z) (frame b z)
      have hms : (Gr.toRealizedMetricFamily hLCall).metric s = S.family.metric s := by
        change S.family.metric (ρ s) = S.family.metric s
        rw [hs]
      rw [hms]
    have hExtGr : metricExtDtOn (I := I) (Gr.toRealizedMetricFamily hLCall) frame
        (t₀ : Real) u
        (fun z a b => (-2 : Real) *
          ricT (t₀ : Real) z (vec2 (I := I) (frame a z) (frame b z))) := by
      intro z hz d a b
      have hbig : FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
          D.regular D.regular u
          (fun s w => (S.family.metric s).inner w (frame a w) (frame b w))
          (fun t w => (-2 : Real) *
            ricT t w (vec2 (I := I) (frame a w) (frame b w))) := by
        refine fixedBaseOnRegSmooth hu D.regular_isOpen
          (fun ht => D.regular_isOpen.mem_nhds ht) ?_ ?_
        · intro t ht w hw
          have hcomp := hS.smoothMetric.frameCompSmooth frame hframeInf a b
          have hmem : (t, w) ∈ D.regular ×ˢ u := ⟨ht, hw⟩
          have hn : D.regular ×ˢ u ∈ nhds (t, w) :=
            (D.regular_isOpen.prod hu).mem_nhds hmem
          exact (hcomp.contMDiffAt hn).of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)
        · intro t ht w hw
          have h1 := (hS.equation ⟨t, ht⟩ w (frame a w) (frame b w)).hasDerivAt
            (D.regular_mem_nhds ht)
          have h2 : (-2 : Real) * ricT t w (vec2 (I := I) (frame a w) (frame b w)) =
              (-2 : Real) * S.ricci t w (frame a w) (frame b w) := by
            rw [hricT]
          rw [h2]
          exact h1.hasDerivWithinAt
      have hAt := (hbig (t₀ : Real) t₀.2 z hz (frame d z)).hasDerivAt
        (D.regular_isOpen.mem_nhds t₀.2)
      refine hAt.congr_of_eventuallyEq ?_
      filter_upwards [hρeq] with s hs
      have hms : (Gr.toRealizedMetricFamily hLCall).metric s = S.family.metric s := by
        change S.family.metric (ρ s) = S.family.metric s
        rw [hs]
      rw [hms]
    have hmcv := metricCovVarOn_of_ricciFlow (I := I)
      (Gr.toRealizedMetricFamily hLCall) frame hframe1 (t₀ : Real)
      (fun z a b => ricT (t₀ : Real) z (vec2 (I := I) (frame a z) (frame b z)))
      hflowGr hExtGr
    have hvarEq := lcGammaVar_on (I := I) (M := M)
      (Gr.toRealizedMetricFamily hLCall) hLCall gInv frame hframe1 hu (t₀ : Real)
      (fun z a b => (-2 : Real) *
        ricT (t₀ : Real) z (vec2 (I := I) (frame a z) (frame b z)))
      (dotCovAt (I := I) ((Gr.toRealizedMetricFamily hLCall).connection (t₀ : Real))
        frame hframe1
        (fun z a b => (-2 : Real) *
          ricT (t₀ : Real) z (vec2 (I := I) (frame a z) (frame b z))))
      (fun x k i j =>
        gammaFromLower gInv
          (connectionPairingTimeDeriv (I := I) (Gr.toRealizedMetricFamily hLCall)
            frame (t₀ : Real)) x i j k)
      hinvOn' hflowGr hmcv hgammaGr
    have h0 := hvarEq y hy i j k
    rw [h0, hGrconn]

private lemma tensor3_first_slot_sum {x : M} {Idx : Type*} [Fintype Idx]
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (c : Idx -> Real) (V : Idx -> TangentSpace I x) (Y Z : TangentSpace I x) :
    T (vec3 (I := I) (∑ p : Idx, c p • V p) Y Z) =
      ∑ p : Idx, c p * T (vec3 (I := I) (V p) Y Z) := by
  classical
  let base : Fin 3 -> TangentSpace I x := vec3 (I := I) (∑ p : Idx, c p • V p) Y Z
  have hbase : Function.update base (0 : Fin 3) (∑ p : Idx, c p • V p) = base := by
    funext q
    fin_cases q <;>
      simp [base, Function.update, vec3, DifferentialGeometry.Integral.Connection.vec3]
  have hupdate : ∀ W : TangentSpace I x,
      Function.update base (0 : Fin 3) W = vec3 (I := I) W Y Z := by
    intro W
    funext q
    fin_cases q <;>
      simp [base, Function.update, vec3, DifferentialGeometry.Integral.Connection.vec3]
  have hsum := T.toMultilinearMap.map_update_sum
    (Finset.univ : Finset Idx) (0 : Fin 3) (fun p : Idx => c p • V p) base
  have hsum' : T (Function.update base (0 : Fin 3) (∑ p : Idx, c p • V p)) =
      ∑ p : Idx, c p * T (Function.update base (0 : Fin 3) (V p)) := by
    simpa using hsum
  calc T (vec3 (I := I) (∑ p : Idx, c p • V p) Y Z)
      = T (Function.update base (0 : Fin 3) (∑ p : Idx, c p • V p)) := by rw [hbase]
    _ = ∑ p : Idx, c p * T (Function.update base (0 : Fin 3) (V p)) := hsum'
    _ = ∑ p : Idx, c p * T (vec3 (I := I) (V p) Y Z) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hupdate (V p)]

private lemma tensor3_third_slot_sum {x : M} {Idx : Type*} [Fintype Idx]
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (c : Idx -> Real) (V : Idx -> TangentSpace I x) (X Y : TangentSpace I x) :
    T (vec3 (I := I) X Y (∑ p : Idx, c p • V p)) =
      ∑ p : Idx, c p * T (vec3 (I := I) X Y (V p)) := by
  classical
  let base : Fin 3 -> TangentSpace I x := vec3 (I := I) X Y (∑ p : Idx, c p • V p)
  have hbase : Function.update base (2 : Fin 3) (∑ p : Idx, c p • V p) = base := by
    funext q
    fin_cases q <;>
      simp [base, Function.update, vec3, DifferentialGeometry.Integral.Connection.vec3]
  have hupdate : ∀ W : TangentSpace I x,
      Function.update base (2 : Fin 3) W = vec3 (I := I) X Y W := by
    intro W
    funext q
    fin_cases q <;>
      simp [base, Function.update, vec3, DifferentialGeometry.Integral.Connection.vec3]
  have hsum := T.toMultilinearMap.map_update_sum
    (Finset.univ : Finset Idx) (2 : Fin 3) (fun p : Idx => c p • V p) base
  have hsum' : T (Function.update base (2 : Fin 3) (∑ p : Idx, c p • V p)) =
      ∑ p : Idx, c p * T (Function.update base (2 : Fin 3) (V p)) := by
    simpa using hsum
  calc T (vec3 (I := I) X Y (∑ p : Idx, c p • V p))
      = T (Function.update base (2 : Fin 3) (∑ p : Idx, c p • V p)) := by rw [hbase]
    _ = ∑ p : Idx, c p * T (Function.update base (2 : Fin 3) (V p)) := hsum'
    _ = ∑ p : Idx, c p * T (vec3 (I := I) X Y (V p)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hupdate (V p)]

private lemma ricReact_eval (g : SmoothRiemannianMetric I M) (x : M)
    (nR : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    ricciVariationOneFormReaction (I := I) g x nR α (vec2 (I := I) X Y) =
      nR (vec3 (I := I) X Y (cotangentSharp (I := I) g x α)) +
        nR (vec3 (I := I) Y X (cotangentSharp (I := I) g x α)) -
        nR (vec3 (I := I) (cotangentSharp (I := I) g x α) X Y) := by
  classical
  set Hs : TangentSpace I x := cotangentSharp (I := I) g x α with hHs
  have hexpand : ricciVariationOneFormReaction (I := I) g x nR α (vec2 (I := I) X Y) =
      (tensor0S_curry (𝕜 := Real) (I := I) 2 x (nR.domDomCongr (finRotate 3))) Hs
          (vec2 (I := I) X Y) +
        ((tensor0S_curry (𝕜 := Real) (I := I) 2 x (nR.domDomCongr (finRotate 3))) Hs).domDomCongr
            (Equiv.swap (0 : Fin 2) 1) (vec2 (I := I) X Y) -
        (tensor0S_curry (𝕜 := Real) (I := I) 2 x nR) Hs (vec2 (I := I) X Y) := rfl
  have hterm1 : (tensor0S_curry (𝕜 := Real) (I := I) 2 x (nR.domDomCongr (finRotate 3))) Hs
      (vec2 (I := I) X Y) = nR (vec3 (I := I) X Y Hs) := by
    rw [curry_eval (I := I) (nR.domDomCongr (finRotate 3)) Hs (vec2 (I := I) X Y),
      ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hterm2 : ((tensor0S_curry (𝕜 := Real) (I := I) 2 x
        (nR.domDomCongr (finRotate 3))) Hs).domDomCongr
      (Equiv.swap (0 : Fin 2) 1) (vec2 (I := I) X Y) = nR (vec3 (I := I) Y X Hs) := by
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hsw : (fun i => (vec2 (I := I) X Y) ((Equiv.swap (0 : Fin 2) 1) i)) =
        vec2 (I := I) Y X := swap_vec2_eval (I := I) X Y
    rw [show (fun i => (vec2 (I := I) X Y) ((Equiv.swap (0 : Fin 2) 1) i)) =
        vec2 (I := I) Y X from hsw]
    rw [curry_eval (I := I) (nR.domDomCongr (finRotate 3)) Hs (vec2 (I := I) Y X),
      ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hterm3 : (tensor0S_curry (𝕜 := Real) (I := I) 2 x nR) Hs (vec2 (I := I) X Y) =
      nR (vec3 (I := I) Hs X Y) := by
    rw [curry_eval (I := I) nR Hs (vec2 (I := I) X Y)]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hexpand, hterm1, hterm2, hterm3]

private lemma dotCovAt_ric_components
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (ricT : Real -> TwoTensorSection (I := I) (M := M))
    (nablaRic : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hNablaRic : forall t : RealTimeInterval.FlowTime D, forall x : M,
      forall (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
        (Y Z : TangentSpace I x),
        nablaRic (t : Real) x (vec3 (X x) Y Z) =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 (S.family.connection (t : Real)) X (ricT (t : Real)) x (vec2 Y Z))
    (t₀ : RealTimeInterval.RegularTime D)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (Yg : Idx -> Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) {u : Set M}
    (hframe1 : IsLocalFrameOn I E 1 (fun i (y : M) => Yg i y) u)
    {x : M} (hx : x ∈ u) (d a b : Idx) :
    dotCovAt (I := I) (S.family.connection (t₀ : Real)) (fun i (y : M) => Yg i y) hframe1
        (fun z p q => (-2 : Real) *
          ricT (t₀ : Real) z (vec2 (I := I) (Yg p z) (Yg q z)))
        x d a b =
      (-2 : Real) * nablaRic (t₀ : Real) x (vec3 (I := I) (Yg d x) (Yg a x) (Yg b x)) := by
  classical
  have hmd : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => ricT (t₀ : Real) y (vec2 (I := I) (Yg a y) (Yg b y))) x := by
    have h0 := tensor0SField_eval_C1_slots_mdiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (ricT (t₀ : Real))
      (fun q : Fin 2 => if q = 0 then (fun y : M => Yg a y) else (fun y : M => Yg b y))
      x
      (by
        intro q
        by_cases hq : q = 0 <;>
          simp only [hq, if_pos, ite_false] <;>
          exact ((Yg _).contMDiff.contMDiffAt).of_le (by norm_num))
    have hshape : (fun p : M => ricT (t₀ : Real) p
        (fun q : Fin 2 => (if q = 0 then (fun y : M => Yg a y) else fun y : M => Yg b y) p)) =
        (fun y : M => ricT (t₀ : Real) y (vec2 (I := I) (Yg a y) (Yg b y))) := by
      funext p
      congr 1
      funext q
      by_cases hq : q = 0 <;>
        simp [hq, vec2, DifferentialGeometry.Integral.Connection.vec2]
    rwa [hshape] at h0
  have hnr := hNablaRic (RealTimeInterval.regularToFlow t₀) x (Yg d) (Yg a x) (Yg b x)
  simp only [RealTimeInterval.regularToFlow_val] at hnr
  have hkos := nabla0SFun_two_koszul (I := I) (M := M)
    (S.family.connection (t₀ : Real)) (Yg d) (Yg a) (Yg b) (ricT (t₀ : Real)) x
  have hca := covariantDerivative_eq_sum_christoffel
    (𝕜 := Real) (I := I) (cov := S.family.connection (t₀ : Real))
    (frame := fun i (y : M) => Yg i y) (hframe := hframe1) hx d a
  have hcb := covariantDerivative_eq_sum_christoffel
    (𝕜 := Real) (I := I) (cov := S.family.connection (t₀ : Real))
    (frame := fun i (y : M) => Yg i y) (hframe := hframe1) hx d b
  have hslotA : ricT (t₀ : Real) x
      (vec2 (I := I)
        ((S.family.connection (t₀ : Real) (fun p => Yg a p) x) (Yg d x)) (Yg b x)) =
      ∑ p : Idx,
        christoffelSymbolInFrame (S.family.connection (t₀ : Real))
            (fun i (y : M) => Yg i y) hframe1 x d a p *
          ricT (t₀ : Real) x (vec2 (I := I) (Yg p x) (Yg b x)) := by
    rw [show (S.family.connection (t₀ : Real) (fun p => Yg a p) x) (Yg d x) =
        ∑ k : Idx,
          christoffelSymbolInFrame (S.family.connection (t₀ : Real))
              (fun i (y : M) => Yg i y) hframe1 x d a k • Yg k x from hca]
    exact tensor2_first_slot_sum (I := I) (ricT (t₀ : Real) x)
      (fun k => christoffelSymbolInFrame (S.family.connection (t₀ : Real))
        (fun i (y : M) => Yg i y) hframe1 x d a k)
      (fun k => Yg k x) (Yg b x)
  have hslotB : ricT (t₀ : Real) x
      (vec2 (I := I) (Yg a x)
        ((S.family.connection (t₀ : Real) (fun p => Yg b p) x) (Yg d x))) =
      ∑ p : Idx,
        christoffelSymbolInFrame (S.family.connection (t₀ : Real))
            (fun i (y : M) => Yg i y) hframe1 x d b p *
          ricT (t₀ : Real) x (vec2 (I := I) (Yg a x) (Yg p x)) := by
    rw [show (S.family.connection (t₀ : Real) (fun p => Yg b p) x) (Yg d x) =
        ∑ k : Idx,
          christoffelSymbolInFrame (S.family.connection (t₀ : Real))
              (fun i (y : M) => Yg i y) hframe1 x d b k • Yg k x from hcb]
    exact tensor2_second_slot_sum (I := I) (ricT (t₀ : Real) x)
      (fun k => christoffelSymbolInFrame (S.family.connection (t₀ : Real))
        (fun i (y : M) => Yg i y) hframe1 x d b k)
      (fun k => Yg k x) (Yg a x)
  have hext2 : extDerivFun (I := I)
      (fun z : M => (-2 : Real) *
        ricT (t₀ : Real) z (vec2 (I := I) (Yg a z) (Yg b z))) x
      ((fun i (y : M) => Yg i y) d x) =
      (-2 : Real) * extDerivFun (I := I)
        (fun z : M => ricT (t₀ : Real) z (vec2 (I := I) (Yg a z) (Yg b z))) x (Yg d x) := by
    rw [extDerivFun_const_mul I (-2 : Real) hmd]
    rfl
  unfold dotCovAt
  rw [hext2, hnr, hkos]
  rw [hslotA, hslotB]
  rw [show (∑ p : Idx,
      christoffelSymbolInFrame (S.family.connection (t₀ : Real))
          (fun i (y : M) => Yg i y) hframe1 x d a p *
        ((fun z p' q => (-2 : Real) *
          ricT (t₀ : Real) z (vec2 (I := I) (Yg p' z) (Yg q z))) x p b)) =
      (-2 : Real) * ∑ p : Idx,
        christoffelSymbolInFrame (S.family.connection (t₀ : Real))
            (fun i (y : M) => Yg i y) hframe1 x d a p *
          ricT (t₀ : Real) x (vec2 (I := I) (Yg p x) (Yg b x)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring]
  rw [show (∑ p : Idx,
      christoffelSymbolInFrame (S.family.connection (t₀ : Real))
          (fun i (y : M) => Yg i y) hframe1 x d b p *
        ((fun z p' q => (-2 : Real) *
          ricT (t₀ : Real) z (vec2 (I := I) (Yg p' z) (Yg q z))) x a p)) =
      (-2 : Real) * ∑ p : Idx,
        christoffelSymbolInFrame (S.family.connection (t₀ : Real))
            (fun i (y : M) => Yg i y) hframe1 x d b p *
          ricT (t₀ : Real) x (vec2 (I := I) (Yg a x) (Yg p x)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring]
  ring


private lemma heatOneForm_nablaH_timeDeriv_ricciFlow
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
    (t₀ : RealTimeInterval.RegularTime D)
    (W : SmoothCcTensor (S.family.metric (t₀ : Real)) 0 1)
    (hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h (t₀ : Real) y))
    (GLap : (y : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hGLap : ∀ y : M, Tensor0SSpace.toRS0 (GLap y) =
      (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
        (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)).toSection y)
    (x : M) (X Y : TangentSpace I x) :
    HasDerivAt (fun s : Real => nablaH s x (vec2 X Y))
      (GLap x (vec2 X Y)
        + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
            (nablaRic (t₀ : Real) x) (h (t₀ : Real) x) (vec2 X Y))
      (t₀ : Real) := by
  classical
  have hbridge2 : ∀ y : M,
      (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W).toFun y =
        TensorRSSpace.toModel
          (Tensor0SSpace.toRS0
            (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
              (nabla2H (t₀ : Real) y))) :=
    fun y => (heatOneForm_wrapped_realizes (I := I) (M := M) S hS h nablaH nabla2H
      hProbe t₀ W hW y).2
  have hmc : IsMetricCompatible_gen (I := I) (S.family.connection (t₀ : Real))
      (S.family.metric (t₀ : Real)) := hS.leviCivita.1 (RealTimeInterval.regularToFlow t₀)
  have htf : IsTorsionFree (I := I) (S.family.connection (t₀ : Real)) :=
    hS.leviCivita.2 (RealTimeInterval.regularToFlow t₀)
  have hLC : IsLeviCivita (I := I) (S.family.connection (t₀ : Real))
      (S.family.metric (t₀ : Real)) := isLeviCivita_of_parts hmc htf
  haveI hcovsmooth : CovariantDerivative.ContMDiffCovariantDerivative
      (S.family.connection (t₀ : Real)) ∞ :=
    hS.smoothConnection (RealTimeInterval.regularToFlow t₀)
  set eT := trivializationAt E (TangentSpace I : M -> Type _) x with heT
  have hxe : x ∈ eT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hframe₀ := eT.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) (Module.finBasis Real E)
  obtain ⟨Yg, hYg⟩ := hframe₀.exists_contMDiffSection_eqOn_nhd eT.open_baseSet hxe
  obtain ⟨u₀, hu₀mem, hu₀open, hxu₀⟩ := eventually_nhds_iff.mp hYg
  have hu : IsOpen (u₀ ∩ eT.baseSet) := hu₀open.inter eT.open_baseSet
  have hxu : x ∈ u₀ ∩ eT.baseSet := ⟨hxu₀, hxe⟩
  have hframeInf : IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (fun i (y : M) => Yg i y) (u₀ ∩ eT.baseSet) := by
    refine IsLocalFrameOn.congr ((hframe₀.mono Set.inter_subset_right)) ?_
    intro i y hy
    exact (hu₀mem y hy.1 i).symm
  have hframe1 : IsLocalFrameOn I E 1 (fun i (y : M) => Yg i y) (u₀ ∩ eT.baseSet) :=
    { linearIndependent := fun {y} hy => hframeInf.linearIndependent hy
      generating := fun {y} hy => hframeInf.generating hy
      contMDiffOn := fun i => (hframeInf.contMDiffOn i).of_le (by exact_mod_cast le_top) }
  set gInvF : M -> Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) -> Real :=
    fun y i j =>
      if hy : y ∈ u₀ ∩ eT.baseSet then
        basisInvMetric (I := I) (S.family.metric (t₀ : Real)) y (hframe1.toBasisAt hy) i j
      else 0
    with hgInvF
  have hinvOn : ∀ y : M, y ∈ u₀ ∩ eT.baseSet ->
      ∀ i j : Fin (Module.finrank Real E),
      (∑ k, gInvF y i k *
          (S.family.metric (t₀ : Real)).inner y (Yg k y) (Yg j y)) =
          (if i = j then 1 else 0) ∧
        (∑ k, (S.family.metric (t₀ : Real)).inner y (Yg i y) (Yg k y) *
            gInvF y k j) =
          (if i = j then 1 else 0) := by
    intro y hy i j
    have hreal := basisInvMetric_real (I := I) (S.family.metric (t₀ : Real)) y
      (hframe1.toBasisAt hy)
    have hco : ∀ k, (hframe1.toBasisAt hy) k = Yg k y :=
      fun k => hframe1.toBasisAt_coe hy k
    constructor
    · have h1 := (hreal i j).1
      simp only [hco] at h1
      rw [hgInvF]
      beta_reduce
      simp only [dif_pos hy]
      exact h1
    · have h2 := (hreal i j).2
      simp only [hco] at h2
      rw [hgInvF]
      beta_reduce
      simp only [dif_pos hy]
      exact h2
  have hinvOn' : ∀ y : M, y ∈ u₀ ∩ eT.baseSet ->
      ∀ i j : Fin (Module.finrank Real E),
      (∑ k, gInvF y i k *
          (S.family.metric (t₀ : Real)).inner y
            ((fun i (z : M) => Yg i z) k y) ((fun i (z : M) => Yg i z) j y)) =
          (if i = j then 1 else 0) ∧
        (∑ k, (S.family.metric (t₀ : Real)).inner y
            ((fun i (z : M) => Yg i z) i y) ((fun i (z : M) => Yg i z) k y) *
            gInvF y k j) =
          (if i = j then 1 else 0) := hinvOn
  obtain ⟨gammaDot, hgammaDeriv, hgammaEq⟩ :=
    christoffel_dt_ricciFlow (I := I) (M := M) S hS ricT hricT t₀
      (fun i (y : M) => Yg i y) hframeInf hframe1 hu gInvF hinvOn'
  set Wlap := rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W with hWlap
  have hlapSec : ∀ y : M, Wlap.toSection y =
      Tensor0SSpace.toRS0 (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
        (nabla2H (t₀ : Real) y)) := by
    intro y
    have hb := hbridge2 y
    rw [SmoothCcTensor.toFun_apply] at hb
    exact TensorRSSpace.toModel_injective hb
  have hLFeq : ∀ y : M,
      unitValField (I := I) (M := M) (S.family.metric (t₀ : Real)) Wlap y =
        roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
          (nabla2H (t₀ : Real) y) := by
    intro y
    rw [unitValField_apply, hlapSec y]
    exact toRS0_one0_eval (I := I) (M := M) _
  have hGLapEq : ∀ y : M, GLap y =
      unitValField (I := I) (M := M) (S.family.metric (t₀ : Real))
        (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 Wlap) y := by
    intro y
    have h1 := congrArg (fun T : TensorRSSpace 0 2 I y =>
      T (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ y)) (hGLap y)
    simp only at h1
    rw [toRS0_one0_eval (I := I) (M := M) (GLap y)] at h1
    rw [h1, unitValField_apply]
  have hrealL := covGrad_unit_realizes (I := I) (M := M) (S.family.metric (t₀ : Real))
    (S.family.connection (t₀ : Real)) hLC Wlap
  have hcomp : ∀ i j : Fin (Module.finrank Real E),
      HasDerivAt (fun s : Real => nablaH s x (vec2 (I := I) (Yg i x) (Yg j x)))
        (GLap x (vec2 (I := I) (Yg i x) (Yg j x))
          + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
              (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)
              (vec2 (I := I) (Yg i x) (Yg j x)))
        (t₀ : Real) := by
    intro i j
    set n : Fin 2 -> Fin (Module.finrank Real E) := ![i, j] with hn
    have hn0 : n 0 = i := rfl
    have hn1 : n 1 = j := rfl
    have htail : Fin.tail n = fun _ : Fin 1 => j := by
      funext q
      rw [Subsingleton.elim q 0]
      rfl
    set A : Real -> M -> (Fin 1 -> Fin (Module.finrank Real E)) -> Real :=
      fun s => frameComp0S (I := I) (h s) (fun i (y : M) => Yg i y) with hA
    set Adt : Real -> M -> (Fin 1 -> Fin (Module.finrank Real E)) -> Real :=
      fun t y m =>
        roughLap0STensor (I := I) (S.family.metric t) (s := 1) (nabla2H t y)
          (frameTuple (I := I) (fun i (z : M) => Yg i z) y m) with hAdt
    set chr : Real -> M -> Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) ->
        Fin (Module.finrank Real E) -> Real :=
      fun s y => christoffelSymbolInFrame (S.family.connection s)
        (fun i (z : M) => Yg i z) hframe1 y with hchrdef
    set chrDtF : Real -> M -> Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) ->
        Fin (Module.finrank Real E) -> Real :=
      fun _ y i' a p => gammaDot y p i' a with hchrDtF
    have hslot1 : ∀ (y : M) (m : Fin 1 -> Fin (Module.finrank Real E)),
        frameTuple (I := I) (fun i (z : M) => Yg i z) y m =
          (fun _ : Fin 1 => Yg (m 0) y) := by
      intro y m
      funext q
      rw [Subsingleton.elim q 0]
      rfl
    have hAeq : ∀ (s : Real) (y : M) (m : Fin 1 -> Fin (Module.finrank Real E)),
        A s y m = h s y (fun _ : Fin 1 => Yg (m 0) y) := by
      intro s y m
      change h s y (frameTuple (I := I) (fun i (z : M) => Yg i z) y m) = _
      rw [hslot1 y m]
    have hAdteq : ∀ (t : Real) (y : M) (m : Fin 1 -> Fin (Module.finrank Real E)),
        Adt t y m =
          roughLap0STensor (I := I) (S.family.metric t) (s := 1) (nabla2H t y)
            (fun _ : Fin 1 => Yg (m 0) y) := by
      intro t y m
      change roughLap0STensor (I := I) (S.family.metric t) (s := 1) (nabla2H t y)
          (frameTuple (I := I) (fun i (z : M) => Yg i z) y m) = _
      rw [hslot1 y m]
    have hAder : ∀ m : Fin 1 -> Fin (Module.finrank Real E),
        HasDerivWithinAt (fun s : Real => A s x m) (Adt (t₀ : Real) x m)
          D.regular (t₀ : Real) := by
      intro m
      have heq := hProbe.equation t₀ x (Yg (m 0) x)
      have hfun : (fun s : Real => A s x m) =
          (fun s : Real => h s x (fun _ : Fin 1 => Yg (m 0) x)) := by
        funext s
        exact hAeq s x m
      rw [hfun, hAdteq (t₀ : Real) x m]
      exact heq.hasDerivWithinAt
    have hchrDer : ∀ i' a p : Fin (Module.finrank Real E),
        HasDerivWithinAt (fun s : Real => chr s x i' a p) (chrDtF (t₀ : Real) x i' a p)
          D.regular (t₀ : Real) :=
      fun i' a p => (hgammaDeriv x hxu i' a p).hasDerivWithinAt
    have hswap : ∀ m : Fin 1 -> Fin (Module.finrank Real E),
        HasDerivWithinAt
          (fun s : Real =>
            extDerivFun (I := I) (fun y : M => A s y m) x
              ((fun i (z : M) => Yg i z) (n 0) x))
          (extDerivFun (I := I) (fun y : M => Adt (t₀ : Real) y m) x
            ((fun i (z : M) => Yg i z) (n 0) x))
          D.regular (t₀ : Real) := by
      intro m
      have hbig : FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
          D.regular D.regular (u₀ ∩ eT.baseSet)
          (fun s y => A s y m)
          (fun t y => Adt t y m) := by
        refine fixedBaseOnRegSmooth hu D.regular_isOpen
          (fun ht => D.regular_isOpen.mem_nhds ht) ?_ ?_
        · intro t ht y hy
          have hjs := hProbe.jointSmooth (fun i (z : M) => Yg i z) hframeInf (m 0)
          have hjs' : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
              (fun p : Real × M => A p.1 p.2 m) (D.regular ×ˢ (u₀ ∩ eT.baseSet)) := by
            refine hjs.congr (fun p _ => ?_)
            exact hAeq p.1 p.2 m
          have hmem : (t, y) ∈ D.regular ×ˢ (u₀ ∩ eT.baseSet) := ⟨ht, hy⟩
          have hnh : D.regular ×ˢ (u₀ ∩ eT.baseSet) ∈ nhds (t, y) :=
            (D.regular_isOpen.prod hu).mem_nhds hmem
          exact (hjs'.contMDiffAt hnh).of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)
        · intro t ht y hy
          have heq := hProbe.equation ⟨t, ht⟩ y (Yg (m 0) y)
          have hfun : (fun s : Real => A s y m) =
              (fun s : Real => h s y (fun _ : Fin 1 => Yg (m 0) y)) := by
            funext s
            exact hAeq s y m
          rw [hfun, hAdteq t y m]
          exact heq.hasDerivWithinAt
      exact hbig (t₀ : Real) t₀.2 x hxu ((fun i (z : M) => Yg i z) (n 0) x)
    have hEng := covDerivStepComp_hasDerivWithinAt
      (I := I) (fun i (z : M) => Yg i z) A Adt chr chrDtF
      (D := D.regular) (t := (t₀ : Real)) x n hAder hchrDer hswap
    have hFn : ∀ s ∈ D.regular,
        covDerivStepComp
            (frameExtData (I := I) (fun i (z : M) => Yg i z) (fun y : M => A s y) x)
            (chr s x) (A s x) n =
          nablaH s x (frameTuple (I := I) (fun i (z : M) => Yg i z) x n) := by
      intro s hs
      have hreal1 : NablaOneFormSectionRealizes (I := I) (S.family.connection s)
          (h s) (nablaH s) :=
        (hProbe.realizes ⟨s, D.regular_subset hs⟩ x).1
      have hTot := oneFormRealizes_toTotal (I := I) (M := M)
        (S.family.connection s) (h s) (nablaH s) hreal1
      exact covDerivStepComp_frameComp_eq
        (I := I) (S.family.connection s) (h s) (nablaH s) hTot
        (fun i (z : M) => Yg i z) hframe1 hu hxu n
    have hW2 := hEng.congr (fun s hs => (hFn s hs).symm) ((hFn (t₀ : Real) t₀.2).symm)
    have hAt := hW2.hasDerivAt (D.regular_isOpen.mem_nhds t₀.2)
    have hft : frameTuple (I := I) (fun i (z : M) => Yg i z) x n =
        vec2 (I := I) (Yg i x) (Yg j x) := by
      funext q
      fin_cases q <;>
        simp [frameTuple, n, vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [hft] at hAt
    have hval : covDerivStepComp
          (frameExtData (I := I) (fun i (z : M) => Yg i z) (fun y : M => Adt (t₀ : Real) y) x)
          (chr (t₀ : Real) x) (Adt (t₀ : Real) x) n -
        covDerivStepDt (chrDtF (t₀ : Real) x) (A (t₀ : Real) x) n =
        GLap x (vec2 (I := I) (Yg i x) (Yg j x))
          + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
              (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)
              (vec2 (I := I) (Yg i x) (Yg j x)) := by
      have hAdtF : Adt (t₀ : Real) =
          frameComp0S (I := I)
            (unitValField (I := I) (M := M) (S.family.metric (t₀ : Real)) Wlap)
            (fun i (z : M) => Yg i z) := by
        funext y m
        change roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) y)
            (frameTuple (I := I) (fun i (z : M) => Yg i z) y m) = _
        rw [show frameComp0S (I := I)
            (unitValField (I := I) (M := M) (S.family.metric (t₀ : Real)) Wlap)
            (fun i (z : M) => Yg i z) y m =
            unitValField (I := I) (M := M) (S.family.metric (t₀ : Real)) Wlap y
              (frameTuple (I := I) (fun i (z : M) => Yg i z) y m) from rfl]
        rw [hLFeq y]
      have h1 : covDerivStepComp
          (frameExtData (I := I) (fun i (z : M) => Yg i z) (fun y : M => Adt (t₀ : Real) y) x)
          (chr (t₀ : Real) x) (Adt (t₀ : Real) x) n =
          unitValField (I := I) (M := M) (S.family.metric (t₀ : Real))
            (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 Wlap) x
            (frameTuple (I := I) (fun i (z : M) => Yg i z) x n) := by
        rw [hAdtF]
        exact covDerivStepComp_frameComp_eq
          (I := I) (S.family.connection (t₀ : Real))
          (unitValField (I := I) (M := M) (S.family.metric (t₀ : Real)) Wlap)
          (unitValField (I := I) (M := M) (S.family.metric (t₀ : Real))
            (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 Wlap))
          hrealL (fun i (z : M) => Yg i z) hframe1 hu hxu n
      have h2 : covDerivStepDt (chrDtF (t₀ : Real) x) (A (t₀ : Real) x) n =
          - ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
              (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)
              (vec2 (I := I) (Yg i x) (Yg j x)) := by
        have hupd : ∀ p : Fin (Module.finrank Real E),
            Function.update (Fin.tail n) (0 : Fin 1) p = (fun _ : Fin 1 => p) := by
          intro p
          funext q
          rw [Subsingleton.elim q 0]
          simp
        have hsteps : covDerivStepDt (chrDtF (t₀ : Real) x) (A (t₀ : Real) x) n =
            ∑ p, gammaDot x p i j * h (t₀ : Real) x (fun _ : Fin 1 => Yg p x) := by
          change (∑ q : Fin 1, ∑ p, chrDtF (t₀ : Real) x (n 0) (Fin.tail n q) p *
              A (t₀ : Real) x (Function.update (Fin.tail n) q p)) = _
          rw [Fin.sum_univ_one]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hupd p]
          have hA1 : A (t₀ : Real) x (fun _ : Fin 1 => p) =
              h (t₀ : Real) x (fun _ : Fin 1 => Yg p x) := by
            rw [hAeq]
          rw [hA1]
          rfl
        have hmcd : ∀ d a b : Fin (Module.finrank Real E),
            dotCovAt (I := I) (S.family.connection (t₀ : Real))
              (fun i' (z : M) => Yg i' z) hframe1
              (fun z p q => (-2 : Real) *
                ricT (t₀ : Real) z (vec2 (I := I) (Yg p z) (Yg q z)))
              x d a b =
            (-2 : Real) *
              nablaRic (t₀ : Real) x (vec3 (I := I) (Yg d x) (Yg a x) (Yg b x)) :=
          fun d a b => dotCovAt_ric_components (I := I) (M := M) S ricT nablaRic hNablaRic t₀
            Yg hframe1 hxu d a b
        have hgamma_p : ∀ p : Fin (Module.finrank Real E),
            gammaDot x p i j =
              ∑ l, gInvF x p l *
                ((-(1 : Real)) *
                  (nablaRic (t₀ : Real) x (vec3 (I := I) (Yg i x) (Yg j x) (Yg l x)) +
                    nablaRic (t₀ : Real) x (vec3 (I := I) (Yg j x) (Yg i x) (Yg l x)) -
                    nablaRic (t₀ : Real) x (vec3 (I := I) (Yg l x) (Yg i x) (Yg j x)))) := by
          intro p
          have he := hgammaEq x hxu i j p
          rw [he]
          change (∑ l, gInvF x p l *
              metricVarLowerRHS
                (dotCovAt (I := I) (S.family.connection (t₀ : Real))
                  (fun i' (z : M) => Yg i' z) hframe1
                  (fun z a b => (-2 : Real) *
                    ricT (t₀ : Real) z (vec2 (I := I) (Yg a z) (Yg b z))))
                x i j l) = _
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 1
          change (1 / 2 : Real) * (_ + _ - _) = _
          rw [hmcd i j l, hmcd j i l, hmcd l i j]
          ring
        have hbasisco : ∀ k, (hframe1.toBasisAt hxu) k = Yg k x :=
          fun k => hframe1.toBasisAt_coe hxu k
        have hinvB : MetricInverseInBasis (I := I) (S.family.metric (t₀ : Real)) x
            (hframe1.toBasisAt hxu) (fun p m => gInvF x p m) := by
          intro i' j'
          have hp := hinvOn x hxu i' j'
          constructor
          · simpa [hbasisco] using hp.1
          · simpa [hbasisco] using hp.2
        have hsymmG : ∀ p l, gInvF x p l = gInvF x l p := by
          intro p l
          rw [hgInvF]
          beta_reduce
          simp only [dif_pos hxu]
          exact basisInvMetric_symm (I := I) (S.family.metric (t₀ : Real)) x
            (hframe1.toBasisAt hxu) p l
        have hHsexp : cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x
            (h (t₀ : Real) x) =
            ∑ p, (∑ m, gInvF x p m * h (t₀ : Real) x (fun _ : Fin 1 => Yg m x)) • Yg p x := by
          rw [cotangentSharp_eq_sum_inv (I := I) (S.family.metric (t₀ : Real)) x
            (hframe1.toBasisAt hxu) (fun p m => gInvF x p m) hinvB (h (t₀ : Real) x)]
          refine Finset.sum_congr rfl fun p _ => ?_
          congr 1
          · refine Finset.sum_congr rfl fun m _ => ?_
            congr 1
            rw [cotangentToDual_apply]
            congr 1
            funext q
            rw [hbasisco m]
          · exact hbasisco p
        have hreact := ricReact_eval (I := I) (M := M) (S.family.metric (t₀ : Real)) x
          (nablaRic (t₀ : Real) x) (h (t₀ : Real) x) (Yg i x) (Yg j x)
        have ht1 : nablaRic (t₀ : Real) x
            (vec3 (I := I) (Yg i x) (Yg j x)
              (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x))) =
            ∑ p, (∑ m, gInvF x p m * h (t₀ : Real) x (fun _ : Fin 1 => Yg m x)) *
              nablaRic (t₀ : Real) x (vec3 (I := I) (Yg i x) (Yg j x) (Yg p x)) := by
          rw [hHsexp]
          exact tensor3_third_slot_sum (I := I) (nablaRic (t₀ : Real) x) _ _ _ _
        have ht2 : nablaRic (t₀ : Real) x
            (vec3 (I := I) (Yg j x) (Yg i x)
              (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x))) =
            ∑ p, (∑ m, gInvF x p m * h (t₀ : Real) x (fun _ : Fin 1 => Yg m x)) *
              nablaRic (t₀ : Real) x (vec3 (I := I) (Yg j x) (Yg i x) (Yg p x)) := by
          rw [hHsexp]
          exact tensor3_third_slot_sum (I := I) (nablaRic (t₀ : Real) x) _ _ _ _
        have ht3 : nablaRic (t₀ : Real) x
            (vec3 (I := I)
              (cotangentSharp (I := I) (S.family.metric (t₀ : Real)) x (h (t₀ : Real) x))
              (Yg i x) (Yg j x)) =
            ∑ p, (∑ m, gInvF x p m * h (t₀ : Real) x (fun _ : Fin 1 => Yg m x)) *
              nablaRic (t₀ : Real) x (vec3 (I := I) (Yg p x) (Yg i x) (Yg j x)) := by
          rw [hHsexp]
          exact tensor3_first_slot_sum (I := I) (nablaRic (t₀ : Real) x) _ _ _ _
        rw [hsteps, hreact, ht1, ht2, ht3]
        rw [show (∑ p, gammaDot x p i j * h (t₀ : Real) x (fun _ : Fin 1 => Yg p x)) =
            ∑ p, ∑ l, gInvF x p l *
              ((-(1 : Real)) *
                (nablaRic (t₀ : Real) x (vec3 (I := I) (Yg i x) (Yg j x) (Yg l x)) +
                  nablaRic (t₀ : Real) x (vec3 (I := I) (Yg j x) (Yg i x) (Yg l x)) -
                  nablaRic (t₀ : Real) x (vec3 (I := I) (Yg l x) (Yg i x) (Yg j x)))) *
                h (t₀ : Real) x (fun _ : Fin 1 => Yg p x) from by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hgamma_p p, Finset.sum_mul]]
        rw [show (∑ p, (∑ m, gInvF x p m * h (t₀ : Real) x (fun _ : Fin 1 => Yg m x)) *
              nablaRic (t₀ : Real) x (vec3 (I := I) (Yg i x) (Yg j x) (Yg p x))) +
            (∑ p, (∑ m, gInvF x p m * h (t₀ : Real) x (fun _ : Fin 1 => Yg m x)) *
              nablaRic (t₀ : Real) x (vec3 (I := I) (Yg j x) (Yg i x) (Yg p x))) -
            (∑ p, (∑ m, gInvF x p m * h (t₀ : Real) x (fun _ : Fin 1 => Yg m x)) *
              nablaRic (t₀ : Real) x (vec3 (I := I) (Yg p x) (Yg i x) (Yg j x))) =
            ∑ p, ∑ m, gInvF x p m * h (t₀ : Real) x (fun _ : Fin 1 => Yg m x) *
              (nablaRic (t₀ : Real) x (vec3 (I := I) (Yg i x) (Yg j x) (Yg p x)) +
                nablaRic (t₀ : Real) x (vec3 (I := I) (Yg j x) (Yg i x) (Yg p x)) -
                nablaRic (t₀ : Real) x (vec3 (I := I) (Yg p x) (Yg i x) (Yg j x))) from by
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
            ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring]
        rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hsymmG l p]
        ring
      rw [h1, hft, h2, ← hGLapEq x]
      ring
    rw [hval] at hAt
    exact hAt
  set basisX := hframe1.toBasisAt hxu with hbX
  have hbco : ∀ k, basisX k = Yg k x := fun k => hframe1.toBasisAt_coe hxu k
  have hXexp : X = ∑ i', basisX.repr X i' • Yg i' x := by
    conv_lhs => rw [show X = ∑ i', basisX.repr X i' • basisX i' from (basisX.sum_repr X).symm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [hbco i']
  have hYexp : Y = ∑ j', basisX.repr Y j' • Yg j' x := by
    conv_lhs => rw [show Y = ∑ j', basisX.repr Y j' • basisX j' from (basisX.sum_repr Y).symm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hbco j']
  have hTexp : ∀ T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      T (vec2 (I := I) X Y) =
        ∑ i', basisX.repr X i' * (∑ j', basisX.repr Y j' *
          T (vec2 (I := I) (Yg i' x) (Yg j' x))) := by
    intro T
    conv_lhs => rw [hXexp, hYexp]
    rw [tensor2_first_slot_sum (I := I) T (fun i' => basisX.repr X i') (fun i' => Yg i' x)
      (∑ j', basisX.repr Y j' • Yg j' x)]
    refine Finset.sum_congr rfl fun i' _ => ?_
    congr 1
    exact tensor2_second_slot_sum (I := I) T (fun j' => basisX.repr Y j')
      (fun j' => Yg j' x) (Yg i' x)
  have hbig : HasDerivAt
      (fun s : Real => ∑ i', basisX.repr X i' * (∑ j', basisX.repr Y j' *
        nablaH s x (vec2 (I := I) (Yg i' x) (Yg j' x))))
      (∑ i', basisX.repr X i' * (∑ j', basisX.repr Y j' *
        (GLap x (vec2 (I := I) (Yg i' x) (Yg j' x))
          + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
              (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)
              (vec2 (I := I) (Yg i' x) (Yg j' x)))))
      (t₀ : Real) := by
    refine HasDerivAt.fun_sum ?_
    intro i' _
    refine HasDerivAt.const_mul (basisX.repr X i') ?_
    refine HasDerivAt.fun_sum ?_
    intro j' _
    exact (hcomp i' j').const_mul (basisX.repr Y j')
  have hfun : (fun s : Real => nablaH s x (vec2 (I := I) X Y)) =
      (fun s : Real => ∑ i', basisX.repr X i' * (∑ j', basisX.repr Y j' *
        nablaH s x (vec2 (I := I) (Yg i' x) (Yg j' x)))) := by
    funext s
    exact hTexp (nablaH s x)
  rw [hfun]
  have hvaleq : GLap x (vec2 (I := I) X Y)
      + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
          (nablaRic (t₀ : Real) x) (h (t₀ : Real) x) (vec2 (I := I) X Y) =
      ∑ i', basisX.repr X i' * (∑ j', basisX.repr Y j' *
        (GLap x (vec2 (I := I) (Yg i' x) (Yg j' x))
          + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
              (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)
              (vec2 (I := I) (Yg i' x) (Yg j' x)))) := by
    rw [hTexp (GLap x), hTexp (ricciVariationOneFormReaction (I := I)
      (S.family.metric (t₀ : Real)) x (nablaRic (t₀ : Real) x) (h (t₀ : Real) x) :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    ring
  rw [hvaleq]
  exact hbig


private lemma heatOneForm_gradNormSq_pointwise
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
    (t₀ : RealTimeInterval.RegularTime D)
    (W : SmoothCcTensor (S.family.metric (t₀ : Real)) 0 1)
    (hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h (t₀ : Real) y))
    (GLap : (y : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hGLap : ∀ y : M, Tensor0SSpace.toRS0 (GLap y) =
      (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
        (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)).toSection y)
    (x : M) :
    deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x)) (t₀ : Real)
      = ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x
          ((ricT (t₀ : Real)) x) (nablaH (t₀ : Real) x)
        + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x) (nablaH (t₀ : Real) x)
        + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
            (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
              (nablaRic (t₀ : Real) x) (h (t₀ : Real) x))
            (nablaH (t₀ : Real) x) := by
  classical
  have hg_hyp : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (S.family.metric r).inner x X Y)
        ((-2 : Real) * ((ricT (t₀ : Real)) x (vec2 (I := I) X Y))) (t₀ : Real) := by
    intro X Y
    have hEq := (hS.equation t₀ x X Y).hasDerivAt (D.regular_mem_nhds t₀.2)
    rw [hricT (t₀ : Real) x X Y]
    exact hEq
  have hQsymm : ∀ X Y : TangentSpace I x,
      (ricT (t₀ : Real)) x (vec2 (I := I) X Y) = (ricT (t₀ : Real)) x (vec2 (I := I) Y X) := by
    intro X Y
    rw [hricT (t₀ : Real) x X Y, hricT (t₀ : Real) x Y X]
    exact ricci_symm_of_solution (I := I) (M := M) S hS t₀ x X Y
  have hA : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => nablaH r x (vec2 (I := I) X Y))
        ((GLap x + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
            (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (vec2 (I := I) X Y)) (t₀ : Real) := by
    intro X Y
    have hp := heatOneForm_nablaH_timeDeriv_ricciFlow (I := I) (M := M) S hS ricT hricT
      nablaRic h nablaH nabla2H hNablaRic hProbe t₀ W hW GLap hGLap x X Y
    have hval : (GLap x + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
          (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (vec2 (I := I) X Y)
        = GLap x (vec2 (I := I) X Y)
          + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
              (nablaRic (t₀ : Real) x) (h (t₀ : Real) x) (vec2 (I := I) X Y) := rfl
    rw [hval]
    exact hp
  have hnst := normSq_two_time (I := I) (M := M)
    (g := fun s : Real => S.family.metric s)
    (Q := (ricT (t₀ : Real)) x) hQsymm
    (A := fun s : Real => nablaH s x)
    (Adot := GLap x + ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
      (nablaRic (t₀ : Real) x) (h (t₀ : Real) x))
    hg_hyp hA
  rw [show deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x))
        (t₀ : Real) = _ from hnst.deriv,
    inner0S_add_left (I := I) (S.family.metric (t₀ : Real)) 2 (GLap x)
      (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
        (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (nablaH (t₀ : Real) x)]
  ring


set_option maxHeartbeats 1600000 in
private lemma heatOneForm_gradNormSq_reaction_ibp
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
    (t₀ : RealTimeInterval.RegularTime D)
    (W : SmoothCcTensor (S.family.metric (t₀ : Real)) 0 1)
    (hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h (t₀ : Real) y))
    (GLap : (y : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hGLap : ∀ y : M, Tensor0SSpace.toRS0 (GLap y) =
      (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
        (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)).toSection y) :
    (∫ x, (ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x
            ((ricT (t₀ : Real)) x) (nablaH (t₀ : Real) x)
          + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x) (nablaH (t₀ : Real) x)
          + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
              (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
                (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (nablaH (t₀ : Real) x)
          - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                (t₀ : Real) x
              * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
        ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real)))
      =
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
          ∂(volumeMeasureFamilyOn (I := I) (M := M) S.family (t₀ : Real))) := by
  classical
  have hpt := heatOneForm_gradNormSq_pointwise (I := I) (M := M) S hS ricT hricT nablaRic
    h nablaH nabla2H hNablaRic hProbe t₀ W hW GLap hGLap
  simp only [volumeMeasureFamilyOn_eq]
  have hbridge := fun x : M =>
    heatOneForm_wrapped_realizes (I := I) (M := M) S hS h nablaH nabla2H hProbe t₀ W hW x
  have hB1 : ∀ x : M,
      (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W).toFun x =
        TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaH (t₀ : Real) x)) :=
    fun x => (hbridge x).1
  have hB2 : ∀ x : M,
      (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W).toFun x =
        TensorRSSpace.toModel
          (Tensor0SSpace.toRS0
            (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
              (nabla2H (t₀ : Real) x))) :=
    fun x => (hbridge x).2
  have hIP : ∀ x : M,
      inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x) (nablaH (t₀ : Real) x) =
        tensorInnerPointwise (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 2 x
          ((TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
            (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)).toFun x)
          ((TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W).toFun x) := by
    intro x
    rw [hB1 x, SmoothCcTensor.toFun_apply, ← hGLap x,
      inner_toRS0 (I := I) (M := M) (S.family.metric (t₀ : Real)) 2 x (GLap x)
        (nablaH (t₀ : Real) x),
      inner0S_eq_covariantTensorInnerPointwise (I := I) (S.family.metric (t₀ : Real)) x 2
        (GLap x) (nablaH (t₀ : Real) x)]
  have hcross : Integrable (fun x : M =>
      2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x) (nablaH (t₀ : Real) x))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) := by
    have hcross0 := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
        (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W))
      (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W)
    have heq : (fun x : M =>
        2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x) (nablaH (t₀ : Real) x))
        = fun x : M => 2 * tensorInnerPointwise (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 2 x
            ((TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
              (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)).toFun x)
            ((TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W).toFun x) := by
      funext x
      rw [hIP x]
    rw [heq]
    exact hcross0.const_mul 2
  have hWeitz := covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_gen (I := I) (M := M)
    (S.family.metric (t₀ : Real)) 1 W
  have htL2Norm : tensorL2Norm (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
      (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W).toFun ^ 2
      = ∫ x, normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
      (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)]
    change (∫ x, tensorInnerPointwise (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 x
        ((rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W).toFun x)
        ((rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real)))) = _
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [hB2 x, ← normSq0S_eq_tensorInnerPointwise_toRS0 (I := I) (S.family.metric (t₀ : Real)) x 1
      (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1) (nabla2H (t₀ : Real) x))]
  have hL2 : (∫ x, 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x)
        (nablaH (t₀ : Real) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
      = (-2 : Real) * ∫ x, normSq0S (I := I) (S.family.metric (t₀ : Real)) x 1
          (roughLap0STensor (I := I) (S.family.metric (t₀ : Real)) (s := 1)
            (nabla2H (t₀ : Real) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) := by
    have h1 : (∫ x, inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x)
          (nablaH (t₀ : Real) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
        = tensorL2Inner (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 (1 + 1)
            (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
              (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)).toFun
            (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W).toFun := by
      have h2 : (∫ x, inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x)
            (nablaH (t₀ : Real) x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
          = ∫ x, tensorInnerPointwise (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 2 x
              ((TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
                (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)).toFun x)
              ((TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1 W).toFun x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => hIP x))
      rw [h2]
      rfl
    rw [MeasureTheory.integral_const_mul, h1, hWeitz, htL2Norm]
    ring
  have hDerivCont : Continuous (fun x : M =>
      deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x))
        (t₀ : Real)) :=
    jointSmooth_timeDeriv_continuous (I := I) (M := M)
      (fun s x => normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x))
      (heatOneForm_nablaNormSq_jointContMDiffOn (I := I) (M := M) hS.smoothMetric hProbe) t₀
  have hDerivInt : Integrable (fun x : M =>
      deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x))
        (t₀ : Real))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) (S.family.metric (t₀ : Real))
      hDerivCont
  have hTraceCont := metricFamily_traceTimeDeriv_continuous (I := I) (M := M)
    S.family hS.smoothMetric t₀
  have hNSjoint := heatOneForm_nablaNormSq_jointContMDiffOn (I := I) (M := M)
    hS.smoothMetric hProbe
  have hNormSqCont : Continuous
      (fun x : M => normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)) := by
    have hmap : ContMDiff I (𝓘(Real, Real).prod I) ∞ (fun x : M => ((t₀ : Real), x)) :=
      contMDiff_const.prodMk contMDiff_id
    have hmaps : ∀ x : M, ((t₀ : Real), x) ∈ D.regular ×ˢ (Set.univ : Set M) :=
      fun x => ⟨t₀.2, Set.mem_univ _⟩
    exact (hNSjoint.comp_contMDiff hmap hmaps).continuous
  have hRfInt : Integrable (fun x : M =>
      scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci (t₀ : Real) x
        * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) := by
    have htrace : ∀ x : M,
        scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci (t₀ : Real) x
          = (-(1 / 2 : Real)) *
              traceTimeDerivMetric (I := I) (fun s : Real => S.family.metric s) (t₀ : Real) x := by
      intro x
      have hh := traceTimeDerivMetricOn_eq_neg_two_scalar (I := I) (M := M) S hS t₀ x
      linarith [hh]
    have hcont : Continuous (fun x : M =>
        scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci (t₀ : Real) x
          * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)) := by
      have hcont' : Continuous (fun x : M =>
          ((-(1 / 2 : Real)) *
              traceTimeDerivMetric (I := I) (fun s : Real => S.family.metric s) (t₀ : Real) x)
            * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)) :=
        (continuous_const.mul hTraceCont).mul hNormSqCont
      refine hcont'.congr (fun x => ?_)
      rw [htrace x]
    exact integrable_of_continuous_compactSpace (I := I) (M := M) (S.family.metric (t₀ : Real))
      hcont
  have hRestInt : Integrable (fun x : M =>
      ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x ((ricT (t₀ : Real)) x)
          (nablaH (t₀ : Real) x)
        + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
            (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
              (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (nablaH (t₀ : Real) x)
        - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
              (t₀ : Real) x
            * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
      (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) := by
    have heq : (fun x : M =>
        ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x ((ricT (t₀ : Real)) x)
            (nablaH (t₀ : Real) x)
          + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
              (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
                (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (nablaH (t₀ : Real) x)
          - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                (t₀ : Real) x
              * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
        = (fun x : M =>
            (deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x))
                (t₀ : Real)
              - 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x)
                  (nablaH (t₀ : Real) x))
            - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                  (t₀ : Real) x
                * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)) := by
      funext x
      rw [hpt x]
      ring
    rw [heq]
    exact (hDerivInt.sub hcross).sub hRfInt
  have hsplitInt : (∫ x,
        (ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x ((ricT (t₀ : Real)) x)
            (nablaH (t₀ : Real) x)
          + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x)
              (nablaH (t₀ : Real) x)
          + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
              (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
                (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (nablaH (t₀ : Real) x)
          - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                (t₀ : Real) x
              * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
      = (∫ x, 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x)
            (nablaH (t₀ : Real) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))))
        + ∫ x,
            (ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x ((ricT (t₀ : Real)) x)
                (nablaH (t₀ : Real) x)
              + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
                  (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
                    (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (nablaH (t₀ : Real) x)
              - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                    (t₀ : Real) x
                  * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric (t₀ : Real))) := by
    have heq2 : (fun x : M =>
        ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x ((ricT (t₀ : Real)) x)
            (nablaH (t₀ : Real) x)
          + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x)
              (nablaH (t₀ : Real) x)
          + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
              (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
                (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (nablaH (t₀ : Real) x)
          - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                (t₀ : Real) x
              * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x))
        = (fun x : M =>
            2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x)
                (nablaH (t₀ : Real) x)
              + (ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x
                    ((ricT (t₀ : Real)) x) (nablaH (t₀ : Real) x)
                + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
                    (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
                      (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (nablaH (t₀ : Real) x)
                - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
                      (t₀ : Real) x
                    * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2
                        (nablaH (t₀ : Real) x))) := by
      funext x
      ring
    rw [heq2]
    exact MeasureTheory.integral_add hcross hRestInt
  rw [hsplitInt, hL2]


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
      (t₀ : Real) := by
  classical
  set W : SmoothCcTensor (S.family.metric (t₀ : Real)) 0 1 :=
    { toSection := (h (t₀ : Real)).toTensorRSField
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW_def
  have hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h (t₀ : Real) y) := fun _ => rfl
  set GLap : (y : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y :=
    fun y => (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
        (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)).toSection y
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ y) with hGLap_def
  have hGLap : ∀ y : M, Tensor0SSpace.toRS0 (GLap y) =
      (TensorSpectral.covGrad (I := I) (M := M) (S.family.metric (t₀ : Real)) 0 1
        (rawTensorConnLapSmooth (I := I) (S.family.metric (t₀ : Real)) 0 1 W)).toSection y :=
    fun y => toRS0_eval_one0 (I := I) (M := M) y _
  have hderiv := first_var_joint (I := I) (M := M)
    (g_fam := fun s : Real => S.family.metric s)
    (f := fun (s : Real) (y : M) => normSq0S (I := I) (S.family.metric s) y 2 (nablaH s y))
    (U := D.regular) (t := (t₀ : Real))
    D.regular_isOpen t₀.2
    (fun x₀ i j =>
      chartGram_jointSmooth_of_metricFamilySmoothOn (I := I) (M := M)
        S.family hS.smoothMetric x₀ i j)
    (heatOneForm_nablaNormSq_jointContMDiffOn (I := I) (M := M) hS.smoothMetric hProbe)
  refine hderiv.congr_deriv
    (Eq.trans ?_
      (heatOneForm_gradNormSq_reaction_ibp (I := I) (M := M)
        S hS ricT hricT nablaRic h nablaH nabla2H hNablaRic hProbe t₀ W hW GLap hGLap))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  change deriv (fun s : Real => normSq0S (I := I) (S.family.metric s) x 2 (nablaH s x)) (t₀ : Real)
        + (1 / 2 : Real) *
            traceTimeDerivMetric (I := I) (fun s : Real => S.family.metric s) (t₀ : Real) x
          * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)
      = ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x
            ((ricT (t₀ : Real)) x) (nablaH (t₀ : Real) x)
        + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2 (GLap x) (nablaH (t₀ : Real) x)
        + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
            (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
              (nablaRic (t₀ : Real) x) (h (t₀ : Real) x)) (nablaH (t₀ : Real) x)
        - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family S.ricci
              (t₀ : Real) x
            * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 (nablaH (t₀ : Real) x)
  rw [heatOneForm_gradNormSq_pointwise (I := I) (M := M) S hS ricT hricT nablaRic
      h nablaH nabla2H hNablaRic hProbe t₀ W hW GLap hGLap x,
    traceTimeDerivMetricOn_eq_neg_two_scalar (I := I) (M := M) S hS t₀ x]
  ring

end HeatProbeEnergy
end Evolution
end DifferentialGeometry.PDE.RicciFlow
