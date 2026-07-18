import DifferentialGeometry.Geometry.Curvature.EinsteinMetric
import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Geometry.Metric.TensorInner.CotangentRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]


set_option linter.unusedVariables false in
def OneFormIsClosed
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  ∀ (x : M) (X Y : TangentSpace I x),
    nablaAlpha x (vec2 (I := I) X Y) = nablaAlpha x (vec2 (I := I) Y X)


def oneFormCodifferentialAt
    (g : SmoothRiemannianMetric I M)
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) (x : M) : Real :=
  -(metricTracePair0SAt (I := I) g (nablaAlpha x))


def OneFormIsCoclosed
    (g : SmoothRiemannianMetric I M)
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  ∀ x : M, oneFormCodifferentialAt (I := I) g nablaAlpha x = 0


def IsHarmonicOneForm
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  NablaOneFormSectionRealizes (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha ∧
    OneFormIsClosed (I := I) α nablaAlpha ∧
    OneFormIsCoclosed (I := I) g nablaAlpha


theorem IsHarmonicOneForm.realizes
    {g : SmoothRiemannianMetric I M}
    {α : OneFormSection (I := I) (M := M)}
    {nablaAlpha : TwoTensorSection (I := I) (M := M)}
    (h : IsHarmonicOneForm (I := I) g α nablaAlpha) :
    NablaOneFormSectionRealizes (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha :=
  h.1


theorem IsHarmonicOneForm.closed
    {g : SmoothRiemannianMetric I M}
    {α : OneFormSection (I := I) (M := M)}
    {nablaAlpha : TwoTensorSection (I := I) (M := M)}
    (h : IsHarmonicOneForm (I := I) g α nablaAlpha) :
    OneFormIsClosed (I := I) α nablaAlpha :=
  h.2.1


theorem IsHarmonicOneForm.coclosed
    {g : SmoothRiemannianMetric I M}
    {α : OneFormSection (I := I) (M := M)}
    {nablaAlpha : TwoTensorSection (I := I) (M := M)}
    (h : IsHarmonicOneForm (I := I) g α nablaAlpha) :
    OneFormIsCoclosed (I := I) g nablaAlpha :=
  h.2.2


theorem isHarmonicOneForm_roughLap_eq_ricciSharp
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hHarm : IsHarmonicOneForm (I := I) g α nablaAlpha)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha x
        (nabla2Alpha x)) :
    ∀ (x : M) (X : TangentSpace I x),
      roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X) =
        metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (cotangentSharp (I := I) g x (α x)) X) := by
  classical
  haveI : IsManifold I 3 M :=
    IsManifold.of_le (by decide : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  intro x X
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv := by
    simpa [basis, gInv] using
      (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x)
  obtain ⟨W, hW⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hsymmSec : ∀ y : M, ∀ U V : TangentSpace I y,
      nablaAlpha y (fun q : Fin 2 => if q = 0 then U else V) =
        nablaAlpha y (fun q : Fin 2 => if q = 0 then V else U) := by
    intro y U V
    exact hHarm.closed y U V
  have hsymm : OneFormLastTwoSymmAt (I := I) (nabla2Alpha x) := by
    intro A Y Z
    obtain ⟨WA, hWA⟩ :=
      ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A
    have h1 := (hRealizes2 x).2 WA Y Z
    have h2 := (hRealizes2 x).2 WA Z Y
    have hs :=
      DifferentialGeometry.Tensor.Coordinates.nabla0SFun_two_symm_of_symm
        (I := I) (metricCov (I := I) (M := M) g) WA nablaAlpha x hsymmSec Y Z
    have hcomb : nabla2Alpha x (vec3 (I := I) (WA x) Y Z) =
        nabla2Alpha x (vec3 (I := I) (WA x) Z Y) := by
      rw [h1, h2]
      exact hs
    rw [hWA] at hcomb
    exact hcomb
  have hR2' : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) α nablaAlpha x (nabla2Alpha x) :=
    hRealizes2 x
  have hcomm : OneFormThirdCovDerivCommAt (I := I)
      (metricRm13 (I := I) (M := M) g) (α x) (nabla2Alpha x) :=
    oneFormThirdCovDerivCommAt_of_leviCivita (I := I) g
      (metricRm13 (I := I) (M := M) g) α nablaAlpha (α x) (nabla2Alpha x)
      (metricCurvData (I := I) (M := M) g).h_rm13 rfl hR2'
  have hSkew : Rm13MetricSkewAt (I := I) g x (metricRm13 (I := I) (M := M) g x) :=
    rm13MetricSkewAt_of_leviCivita_realizes (I := I) g
      (metricRm13 (I := I) (M := M) g) (metricRm04 (I := I) (M := M) g)
      (metricCurvData (I := I) (M := M) g).h_rm13
      (metricCurvData (I := I) (M := M) g).h_rm04 (x := x)
  have hAlpha : α x =
      dualToCotangent_gen (I := I)
        ((tangentFlatLinear_gen (I := I) g x)
          (cotangentSharp (I := I) g x (α x))) := by
    ext v
    have hv : (fun _ : Fin 1 => v 0) = v := by
      funext i
      fin_cases i
      rfl
    rw [← hv]
    rw [dualToCotangent_apply_gen, tangentFlatLinear_apply_gen]
    rw [cotangentSharp_inner, cotangentToDual_apply]
  have hcurvV : CurvatureTraceOneFormEqRicVectorAt (I := I)
      (metricRicci (I := I) (M := M) g) (metricRm13 (I := I) (M := M) g)
      (α x) basis gInv (cotangentSharp (I := I) g x (α x)) :=
    curvatureTraceOneFormEqRicVectorAt_of_metric_dual (I := I) g
      (metricRicci (I := I) (M := M) g) (metricRm13 (I := I) (M := M) g)
      (α x) basis gInv (cotangentSharp (I := I) g x (α x)) hinv
      (metricCurvData (I := I) (M := M) g).h_ricci13 hSkew hAlpha
  have hcurv : ∀ Y : TangentSpace I x,
      -∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          gInv i j * metricRm13 (I := I) (M := M) g x (α x)
            (vec3 (I := I) (basis i) Y (basis j)) =
        metricRicci (I := I) (M := M) g x
          (vec2 (I := I) Y (cotangentSharp (I := I) g x (α x))) := by
    intro Y
    exact hcurvV Y
  have hassemble :=
    oneForm_ricci_trace_comm_of_third_comm (I := I)
      (metricRicci (I := I) (M := M) g) (metricRm13 (I := I) (M := M) g)
      (α x) basis gInv (cotangentSharp (I := I) g x (α x)) (nabla2Alpha x)
      hsymm hcomm hcurv
  have hmc : IsMetricCompatible_gen (I := I) (metricCov (I := I) (M := M) g) g :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hd : differential1FormFun (I := I)
      (fun y : M => metricTracePair0SAt (I := I) g (nablaAlpha y)) x
      (fun _ : Fin 1 => W x) =
    metricTracePair0SAt (I := I) g
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (metricCov (I := I) (M := M) g) W nablaAlpha x) :=
    dTrace02_eq (I := I) (M := M) (metricCov (I := I) (M := M) g) g hmc nablaAlpha W x
  have hfun0 : (fun y : M => metricTracePair0SAt (I := I) g (nablaAlpha y)) =
      (fun _ : M => (0 : Real)) := by
    funext y
    have hc : -(metricTracePair0SAt (I := I) g (nablaAlpha y)) = 0 :=
      hHarm.coclosed y
    linarith
  rw [hfun0] at hd
  have hdz : differential1FormFun (I := I) (fun _ : M => (0 : Real)) x
      (fun _ : Fin 1 => W x) = 0 := by
    rw [differential1FormFun_apply_eq_extDerivFun]
    rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv]
    rw [mfderiv_const]
    rfl
  have htr0 : metricTracePair0SAt (I := I) g
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (metricCov (I := I) (M := M) g) W nablaAlpha x) = 0 :=
    hd.symm.trans hdz
  have hterm : ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      nabla2Alpha x (vec3 (I := I) X (basis i) (basis j)) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (metricCov (I := I) (M := M) g) W nablaAlpha x
          (vec2 (I := I) (basis i) (basis j)) := by
    intro i j
    rw [← hW]
    exact (hRealizes2 x).2 W (basis i) (basis j)
  have h3 : traceNablaOneFormAt (I := I) basis gInv (nabla2Alpha x) X = 0 := by
    calc
      traceNablaOneFormAt (I := I) basis gInv (nabla2Alpha x) X
          = ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
              ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
                gInv i j *
                  nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                    2 (metricCov (I := I) (M := M) g) W nablaAlpha x
                    (vec2 (I := I) (basis i) (basis j)) := by
            unfold traceNablaOneFormAt
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hterm i j]
      _ = metricTracePair0SAt (I := I) g
            (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 (metricCov (I := I) (M := M) g) W nablaAlpha x) :=
            (metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv _).symm
      _ = 0 := htr0
  have hswap : ∀ U V : TangentSpace I x,
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) U V) =
        metricRicciAt (I := I) (M := M) g x (vec2 (I := I) V U) := by
    intro U V
    have hcomp : ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        metricRicciAt (I := I) (M := M) g x
            (fun q : Fin 2 => if q = 0 then basis i else basis j) =
          metricRicciAt (I := I) (M := M) g x
            (fun q : Fin 2 => if q = 0 then basis j else basis i) := by
      intro i j
      exact metricRicciSymm (I := I) (M := M) g basis gInv hinv i j
    exact DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
      (I := I) basis (metricRicciAt (I := I) (M := M) g x) hcomp U V
  calc
    roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X)
        = metricTraceFirstTwo0SAt (I := I) g (nabla2Alpha x) (fun _ : Fin 1 => X) :=
          roughLap0STensor_apply (I := I) g (nabla2Alpha x) (fun _ : Fin 1 => X)
    _ = metricTrace0S2InBasis (I := I) basis gInv (nabla2Alpha x)
          (fun _ : Fin 1 => X) :=
          metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
            (nabla2Alpha x) (fun _ : Fin 1 => X)
    _ = roughLap1FormAt (I := I) basis gInv (nabla2Alpha x) X := rfl
    _ = traceNablaOneFormAt (I := I) basis gInv (nabla2Alpha x) X +
          metricRicci (I := I) (M := M) g x
            (vec2 (I := I) X (cotangentSharp (I := I) g x (α x))) := hassemble X
    _ = metricRicci (I := I) (M := M) g x
          (vec2 (I := I) X (cotangentSharp (I := I) g x (α x))) := by
          rw [h3, zero_add]
    _ = metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (cotangentSharp (I := I) g x (α x)) X) := by
          rw [metricRicci_apply]
          exact hswap X (cotangentSharp (I := I) g x (α x))


theorem isHarmonicOneForm_einstein_roughLap_eigen
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (κ : Real)
    (hEin : IsEinsteinMetric (I := I) g κ)
    (hHarm : IsHarmonicOneForm (I := I) g α nablaAlpha)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha x
        (nabla2Alpha x)) :
    ∀ (x : M) (X : TangentSpace I x),
      roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X) =
        κ * α x (fun _ : Fin 1 => X) := by
  intro x X
  rw [isHarmonicOneForm_roughLap_eq_ricciSharp (I := I) g α nablaAlpha nabla2Alpha
    hHarm hRealizes2 x X]
  rw [hEin x (cotangentSharp (I := I) g x (α x)) X]
  have hval : g.inner x (cotangentSharp (I := I) g x (α x)) X =
      α x (fun _ : Fin 1 => X) := by
    rw [cotangentSharp_inner (I := I) g x (α x) X]
    rw [cotangentToDual_apply]
  rw [hval]

end DifferentialGeometry.Integral.Connection
