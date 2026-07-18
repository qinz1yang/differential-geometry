import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Curvature.EinsteinMetric
import DifferentialGeometry.Analysis.Parabolic.OneFormHeat
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Analysis.Integration.Measure.VolumeVariation
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic
open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



def einsteinScalingFactor (κ t : Real) : Real :=
  1 - 2 * κ * t

@[simp] theorem einsteinScalingFactor_zero (κ : Real) :
    einsteinScalingFactor κ 0 = 1 := by
  simp [einsteinScalingFactor]



def einsteinFlowInterval (κ : Real) :
    DifferentialGeometry.Integral.Connection.RealTimeInterval where
  carrier := {t : Real | 0 < einsteinScalingFactor κ t}
  regular := {t : Real | 0 < einsteinScalingFactor κ t}
  initial := 0
  initial_mem := by
    norm_num [Set.mem_setOf_eq, einsteinScalingFactor]
  regular_subset := fun _ h => h
  regular_isOpen := by
    have hcont : Continuous (fun t : Real => einsteinScalingFactor κ t) := by
      unfold einsteinScalingFactor
      fun_prop
    exact isOpen_lt continuous_const hcont
  regular_mem_nhds := by
    intro t ht
    have hcont : Continuous (fun t : Real => einsteinScalingFactor κ t) := by
      unfold einsteinScalingFactor
      fun_prop
    exact (isOpen_lt continuous_const hcont).mem_nhds ht

@[simp] theorem einsteinFlowInterval_carrier (κ : Real) :
    (einsteinFlowInterval κ).carrier = {t : Real | 0 < einsteinScalingFactor κ t} :=
  rfl

@[simp] theorem einsteinFlowInterval_regular (κ : Real) :
    (einsteinFlowInterval κ).regular = {t : Real | 0 < einsteinScalingFactor κ t} :=
  rfl

@[simp] theorem mem_einsteinFlowInterval_carrier (κ t : Real) :
    t ∈ (einsteinFlowInterval κ).carrier ↔ 0 < einsteinScalingFactor κ t :=
  Iff.rfl

@[simp] theorem mem_einsteinFlowInterval_regular (κ t : Real) :
    t ∈ (einsteinFlowInterval κ).regular ↔ 0 < einsteinScalingFactor κ t :=
  Iff.rfl



def einsteinScaledFamily (g₀ : SmoothRiemannianMetric I M) (κ : Real) :
    SolutionFamily (I := I) (M := M) where
  metric t :=
    if h : 0 < einsteinScalingFactor κ t then
      scaleMetric (I := I) (einsteinScalingFactor κ t) h g₀
    else g₀

def einsteinScaledSolution (g₀ : SmoothRiemannianMetric I M) (κ : Real) :
    SolutionOn (I := I) (M := M) (einsteinFlowInterval κ) where
  base := einsteinScaledFamily g₀ κ

theorem einsteinScaledFamily_metric_of_mem
    (g₀ : SmoothRiemannianMetric I M) (κ : Real) {t : Real}
    (ht : t ∈ (einsteinFlowInterval κ).carrier) :
    (einsteinScaledFamily g₀ κ).metric t =
      scaleMetric (I := I) (einsteinScalingFactor κ t) ht g₀ :=
  dif_pos ht

theorem einsteinScaledFamily_metric_inner_of_pos
    (g₀ : SmoothRiemannianMetric I M) (κ : Real) {t : Real}
    (h : 0 < einsteinScalingFactor κ t) (x : M) (v w : TangentSpace I x) :
    ((einsteinScaledFamily g₀ κ).metric t).inner x v w =
      einsteinScalingFactor κ t * g₀.inner x v w := by
  rw [show (einsteinScaledFamily g₀ κ).metric t
        = scaleMetric (I := I) (einsteinScalingFactor κ t) h g₀ from dif_pos h,
    scaleMetric_inner]

theorem einsteinScaledFamily_metric_zero_inner
    (g₀ : SmoothRiemannianMetric I M) (κ : Real) :
    ((einsteinScaledFamily g₀ κ).metric 0).inner = g₀.inner := by
  funext x
  ext v w
  rw [einsteinScaledFamily_metric_inner_of_pos g₀ κ (t := 0)
    (by rw [einsteinScalingFactor_zero]; exact one_pos) x v w]
  simp [einsteinScalingFactor_zero]

@[simp] theorem einsteinScaledFamily_connection
    (g₀ : SmoothRiemannianMetric I M) (κ : Real) (t : Real) :
    (einsteinScaledFamily g₀ κ).connection t =
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g₀ := by
  simp only [SolutionFamily.connection]
  by_cases h : 0 < einsteinScalingFactor κ t
  · rw [show (einsteinScaledFamily g₀ κ).metric t
          = scaleMetric (I := I) (einsteinScalingFactor κ t) h g₀ from dif_pos h,
      DifferentialGeometry.Integral.Connection.lcConn_scaleMetric]
  · rw [show (einsteinScaledFamily g₀ κ).metric t = g₀ from dif_neg h]

theorem einsteinScaledSolution_ricci_genuine
    (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (t : Real) (x : M) (v w : TangentSpace I x) :
    (einsteinScaledSolution g₀ κ).toRealizedCandidate.ricci t x v w =
      metricRicciAt (I := I) ((einsteinScaledFamily g₀ κ).metric t) x
        (DifferentialGeometry.Integral.Connection.vec2 v w) :=
  rfl



def einsteinScaledProbe (κ : Real)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M)) :
    Real → DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M) :=
  fun t =>
    tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s := 1)
      (fun _ : M => Real.rpow (einsteinScalingFactor κ t) (-(1 / 2 : Real)))
      contMDiff_const alpha

def einsteinScaledProbeNabla (κ : Real)
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M)) :
    Real → DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M) :=
  fun t =>
    tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s := 2)
      (fun _ : M => Real.rpow (einsteinScalingFactor κ t) (-(1 / 2 : Real)))
      contMDiff_const nablaOmega

def einsteinScaledProbeNabla2 (κ : Real)
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Real → (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  fun t x => (Real.rpow (einsteinScalingFactor κ t) (-(1 / 2 : Real))) • nabla2Omega x



theorem einsteinScaled_isSolutionOn
    (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀ κ) :
    IsSolutionOn (I := I) (einsteinScaledSolution g₀ κ) := sorry

theorem einsteinScaled_isRealizedRicciFlowSolutionOn
    (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀ κ) :
    DifferentialGeometry.Integral.Connection.IsRealizedRicciFlowSolutionOn (I := I)
      (einsteinScaledSolution g₀ κ).toRealizedCandidate := sorry

theorem einsteinScaled_isHeatOneFormOn
    (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀ κ)
    (hRealizes : ∀ x : M,
      DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) g₀) alpha nablaOmega x (nabla2Omega x))
    (hEigen : ∀ (x : M) (X : TangentSpace I x),
      DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) g₀ (s := 1)
          (nabla2Omega x) (fun _ : Fin 1 => X)
        = κ * alpha x (fun _ : Fin 1 => X)) :
    IsHeatOneFormOn (I := I) (einsteinScaledSolution g₀ κ).family
      (einsteinScaledProbe κ alpha) (einsteinScaledProbeNabla κ nablaOmega)
      (einsteinScaledProbeNabla2 κ nabla2Omega) := sorry

theorem einsteinScaled_gradEnergy_hasDerivAt [CompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀ κ)
    (hRealizes : ∀ x : M,
      DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) g₀) alpha nablaOmega x (nabla2Omega x))
    (hEigen : ∀ (x : M) (X : TangentSpace I x),
      DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) g₀ (s := 1)
          (nabla2Omega x) (fun _ : Fin 1 => X)
        = κ * alpha x (fun _ : Fin 1 => X)) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I) ((einsteinScaledSolution g₀ κ).family.metric s) x 2
            (einsteinScaledProbeNabla κ nablaOmega s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) (einsteinScaledSolution g₀ κ).family s))
      (κ ^ 2 * ((Module.finrank Real E : Real) - 6) *
        ∫ x, normSq0S (I := I) g₀ x 1 (alpha x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
      0 := sorry

theorem hyperbolicScaled_gradEnergy_hasDerivAt [CompactSpace M]
    (g₀ : SmoothRiemannianMetric I M)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hn : 7 ≤ Module.finrank Real E)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀
      (-((Module.finrank Real E : Real) - 1)))
    (hRealizes : ∀ x : M,
      DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) g₀) alpha nablaOmega x (nabla2Omega x))
    (hEigen : ∀ (x : M) (X : TangentSpace I x),
      DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) g₀ (s := 1)
          (nabla2Omega x) (fun _ : Fin 1 => X)
        = (-((Module.finrank Real E : Real) - 1)) * alpha x (fun _ : Fin 1 => X)) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I)
            ((einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family.metric s) x 2
            (einsteinScaledProbeNabla (-((Module.finrank Real E : Real) - 1)) nablaOmega s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M)
              (einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family s))
      (((Module.finrank Real E : Real) - 1) ^ 2 * ((Module.finrank Real E : Real) - 6) *
        ∫ x, normSq0S (I := I) g₀ x 1 (alpha x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
      0 := sorry

theorem einsteinScaled_gradEnergy_hasDerivAt_dimSix [CompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hdim : Module.finrank Real E = 6)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀ κ)
    (hRealizes : ∀ x : M,
      DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) g₀) alpha nablaOmega x (nabla2Omega x))
    (hEigen : ∀ (x : M) (X : TangentSpace I x),
      DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) g₀ (s := 1)
          (nabla2Omega x) (fun _ : Fin 1 => X)
        = κ * alpha x (fun _ : Fin 1 => X)) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I) ((einsteinScaledSolution g₀ κ).family.metric s) x 2
            (einsteinScaledProbeNabla κ nablaOmega s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) (einsteinScaledSolution g₀ κ).family s))
      0 0 := sorry

theorem hyperbolicScaled_isSolutionOn
    (g₀ : SmoothRiemannianMetric I M)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀
      (-((Module.finrank Real E : Real) - 1))) :
    IsSolutionOn (I := I)
      (einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))) := sorry

theorem hyperbolicScaled_isHeatOneFormOn
    (g₀ : SmoothRiemannianMetric I M)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀
      (-((Module.finrank Real E : Real) - 1)))
    (hRealizes : ∀ x : M,
      DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) g₀) alpha nablaOmega x (nabla2Omega x))
    (hEigen : ∀ (x : M) (X : TangentSpace I x),
      DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) g₀ (s := 1)
          (nabla2Omega x) (fun _ : Fin 1 => X)
        = (-((Module.finrank Real E : Real) - 1)) * alpha x (fun _ : Fin 1 => X)) :
    IsHeatOneFormOn (I := I)
      (einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family
      (einsteinScaledProbe (-((Module.finrank Real E : Real) - 1)) alpha)
      (einsteinScaledProbeNabla (-((Module.finrank Real E : Real) - 1)) nablaOmega)
      (einsteinScaledProbeNabla2 (-((Module.finrank Real E : Real) - 1)) nabla2Omega) := sorry

theorem hyperbolicScaled_gradEnergy_deriv_pos [CompactSpace M]
    (g₀ : SmoothRiemannianMetric I M)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (hn : 7 ≤ Module.finrank Real E)
    (halpha : ∃ x : M, alpha x ≠ 0) :
    0 < ((Module.finrank Real E : Real) - 1) ^ 2 * ((Module.finrank Real E : Real) - 6) *
      ∫ x, normSq0S (I := I) g₀ x 1 (alpha x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := sorry

theorem hyperbolicScaled_gradEnergy_hasDerivAt_dimSix [CompactSpace M]
    (g₀ : SmoothRiemannianMetric I M)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hdim : Module.finrank Real E = 6)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀
      (-((Module.finrank Real E : Real) - 1)))
    (hRealizes : ∀ x : M,
      DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) g₀) alpha nablaOmega x (nabla2Omega x))
    (hEigen : ∀ (x : M) (X : TangentSpace I x),
      DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) g₀ (s := 1)
          (nabla2Omega x) (fun _ : Fin 1 => X)
        = (-((Module.finrank Real E : Real) - 1)) * alpha x (fun _ : Fin 1 => X)) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I)
            ((einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family.metric s) x 2
            (einsteinScaledProbeNabla (-((Module.finrank Real E : Real) - 1)) nablaOmega s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M)
              (einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family s))
      0 0 := sorry

end DifferentialGeometry.PDE.RicciFlow
