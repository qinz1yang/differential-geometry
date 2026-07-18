import DifferentialGeometry.Analysis.Parabolic.OneFormHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Volume
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.CotangentRiemannian
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.RankZeroInner
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Geometry.Connection.Laplacian.RankZero
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator

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
