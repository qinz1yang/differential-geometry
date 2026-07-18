import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Curvature.EinsteinMetric
import DifferentialGeometry.Analysis.Parabolic.OneFormHeat
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Analysis.Integration.Measure.VolumeVariation
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Geometry.Curvature.Scaling
import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal
import DifferentialGeometry.Analysis.Integration.Measure.Scaling
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.OneFormEigenIBP
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.NormSqPositivity
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.FrameEval
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



private theorem lcConnSmooth (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) ∞ :=
  ⟨DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
    (I := I) g (u := Set.univ) isOpen_univ⟩

private theorem normSq0S_metricTensorField_eq_finrank
    (g : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g x 2 (metricTensorField (I := I) g x) = (Module.finrank Real E : Real) := by
  classical
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x k l (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x
  have hcard := DifferentialGeometry.Integral.Connection.normSq0S_metricTensor0S_eq_card
    (I := I) g basis gInv hinv
  have hbridge : metricTensorField (I := I) g x =
      DifferentialGeometry.Integral.Connection.metricTensor0S (I := I) g x := by
    ext v
    rw [metricTensorField_apply, DifferentialGeometry.Integral.Connection.metricTensor0S_apply]
  rw [hbridge, hcard]
  simp [DifferentialGeometry.Tensor.Coordinates.CoordinateIdx]

private theorem einsteinRicci_tensor (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀ κ) (x : M) :
    DifferentialGeometry.Integral.Connection.metricRicciAt (I := I) (M := M) g₀ x
      = κ • metricTensorField (I := I) g₀ x := by
  ext v
  have hv : v = DifferentialGeometry.Integral.Connection.vec2 (I := I) (v 0) (v 1) := by
    funext i
    fin_cases i <;> simp [DifferentialGeometry.Integral.Connection.vec2]
  have hL : DifferentialGeometry.Integral.Connection.metricRicciAt (I := I) (M := M) g₀ x v
      = κ * g₀.inner x (v 0) (v 1) := by
    have hE := hEin x (v 0) (v 1)
    rwa [← hv] at hE
  rw [hL]
  simp [metricTensorField_apply, smul_eq_mul]

private theorem metricTensorField_scaleMetric_local (c : Real) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorField (I := I) (scaleMetric (I := I) c hc g) x
      = c • metricTensorField (I := I) g x := by
  ext v
  simp [metricTensorField_apply, scaleMetric_inner, smul_eq_mul]

private theorem frameEval_contMDiffOn (g : SmoothRiemannianMetric I M)
    {Idx : Type} [Fintype Idx] (frame : Idx -> (x : M) -> TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn I 𝓘(Real, Real) ∞ (fun x : M => g.inner x (frame i x) (frame j x)) u := by
  classical
  have hg : ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun b : M => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun y : M => TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
        b (g.inner b)) u :=
    g.contMDiff.contMDiffOn
  have happ : ContMDiffOn I (I.prod 𝓘(Real, Real)) ∞
      (fun m : M => (⟨m, g.inner m (frame i m) (frame j m)⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) u :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := Real)
      (b := id) hg (hframe.contMDiffOn i) (hframe.contMDiffOn j)
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

set_option backward.isDefEq.respectTransparency false in
private theorem metricTensorField_const_cont (K : Set Real) (g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun _ x => metricTensorField (I := I) g x) := by
  unfold DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet
  exact ((metricTensorField (I := I) g).contMDiff.continuous).comp
    (continuous_snd (X := {t : Real // t ∈ K}) (Y := M))

set_option backward.isDefEq.respectTransparency false in
private theorem metricRicci_const_cont (K : Set Real) (g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun _ x => DifferentialGeometry.Integral.Connection.metricRicciAt (I := I) (M := M) g x) := by
  unfold DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet
  refine (((metricRicci (I := I) (M := M) g).contMDiff.continuous).comp
    (continuous_snd (X := {t : Real // t ∈ K}) (Y := M))).congr (fun q => ?_)
  simp only [Function.comp_apply, metricRicci_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem metricRm04_const_cont (K : Set Real) (g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 K
      (fun _ x => DifferentialGeometry.Integral.Connection.metricRm04At (I := I) (M := M) g x) := by
  unfold DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet
  refine (((metricRm04 (I := I) (M := M) g).contMDiff.continuous).comp
    (continuous_snd (X := {t : Real // t ∈ K}) (Y := M))).congr (fun q => ?_)
  simp only [Function.comp_apply, metricRm04_apply]

private theorem einsteinScaled_scalar_eq (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    {s : Real} (hs : s ∈ (einsteinFlowInterval κ).carrier) (x : M) :
    (einsteinScaledSolution g₀ κ).scalar s x
      = (einsteinScalingFactor κ s)⁻¹ * metricScalarAt (I := I) (M := M) g₀ x := by
  have hmetric : (einsteinScaledSolution g₀ κ).base.metric s
      = scaleMetric (I := I) (einsteinScalingFactor κ s) hs g₀ :=
    einsteinScaledFamily_metric_of_mem g₀ κ hs
  have h1 : (einsteinScaledSolution g₀ κ).scalar s x
      = metricScalarAt (I := I) (M := M) ((einsteinScaledSolution g₀ κ).base.metric s) x := by
    simp [SolutionOn.scalar, SolutionFamily.scalar]
  rw [h1, hmetric]
  exact DifferentialGeometry.Integral.Connection.metricScalarAt_scaleMetric
    (einsteinScalingFactor κ s) hs g₀ x

private theorem einsteinScaled_ricciNorm_const (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀ κ)
    {t : Real} (ht : t ∈ (einsteinFlowInterval κ).carrier) :
    ricciNorm (I := I) (einsteinScaledSolution g₀ κ) t
      = fun _ : M => (einsteinScalingFactor κ t)⁻¹ * (einsteinScalingFactor κ t)⁻¹ *
          (κ ^ 2 * (Module.finrank Real E : Real)) := by
  funext y
  have hmetricB : (einsteinScaledSolution g₀ κ).base.metric t
      = scaleMetric (I := I) (einsteinScalingFactor κ t) ht g₀ :=
    einsteinScaledFamily_metric_of_mem g₀ κ ht
  have hmetricF : (einsteinScaledSolution g₀ κ).family.metric t
      = scaleMetric (I := I) (einsteinScalingFactor κ t) ht g₀ :=
    einsteinScaledFamily_metric_of_mem g₀ κ ht
  have hricci : (einsteinScaledSolution g₀ κ).ricci t y = κ • metricTensorField (I := I) g₀ y := by
    have h1 : (einsteinScaledSolution g₀ κ).ricci t y
        = DifferentialGeometry.Integral.Connection.metricRicciAt (I := I) (M := M)
            ((einsteinScaledSolution g₀ κ).base.metric t) y := by
      simp [SolutionOn.ricci, SolutionFamily.ricci]
    rw [h1, hmetricB, DifferentialGeometry.Integral.Connection.metricRicciAt_scaleMetric]
    exact einsteinRicci_tensor g₀ κ hEin y
  unfold ricciNorm
  rw [hricci, hmetricF, normSq0S_two_scale, normSq0S_smul,
    normSq0S_metricTensorField_eq_finrank]

theorem einsteinScaled_isSolutionOn
    (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀ κ) :
    IsSolutionOn (I := I) (einsteinScaledSolution g₀ κ) where
  smoothMetric := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x X Y
      have hpoly : ContDiff Real ∞ (fun t : Real => einsteinScalingFactor κ t * g₀.inner x X Y) := by
        unfold einsteinScalingFactor
        fun_prop
      refine (hpoly.contDiffOn).congr (fun t ht => ?_)
      exact einsteinScaledFamily_metric_inner_of_pos g₀ κ ht x X Y
    · intro x X Y
      have hpoly : Continuous (fun t : Real => einsteinScalingFactor κ t * g₀.inner x X Y) := by
        unfold einsteinScalingFactor
        fun_prop
      refine (hpoly.continuousOn).congr (fun t ht => ?_)
      exact einsteinScaledFamily_metric_inner_of_pos g₀ κ ht x X Y
    · have hf : Continuous (fun q : {t : Real // t ∈ (einsteinFlowInterval κ).carrier} × M =>
          einsteinScalingFactor κ q.1.1) :=
        (by unfold einsteinScalingFactor; fun_prop : Continuous (einsteinScalingFactor κ)).comp
          (continuous_subtype_val.comp continuous_fst)
      refine (DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.smul
        (f := fun (t : Real) (_ : M) => einsteinScalingFactor κ t) hf
        (metricTensorField_const_cont (einsteinFlowInterval κ).carrier g₀)).congr
        (fun t ht x => ?_)
      have hmetric : (einsteinScaledSolution g₀ κ).family.metric t
          = scaleMetric (I := I) (einsteinScalingFactor κ t) ht g₀ :=
        einsteinScaledFamily_metric_of_mem g₀ κ ht
      rw [hmetric, metricTensorField_scaleMetric_local]
    · intro Idx _ frame u hframe i j
      have hstatic : ContMDiffOn I 𝓘(Real, Real) ∞
          (fun x : M => g₀.inner x (frame i x) (frame j x)) u :=
        frameEval_contMDiffOn g₀ frame hframe i j
      have hstaticP : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M => g₀.inner p.2 (frame i p.2) (frame j p.2))
          ((einsteinFlowInterval κ).regular ×ˢ u) := by
        refine hstatic.comp (contMDiff_snd.contMDiffOn) ?_
        intro p hp
        exact hp.2
      have htime : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M => einsteinScalingFactor κ p.1)
          ((einsteinFlowInterval κ).regular ×ˢ u) := by
        have hcm : ContMDiff (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
            (fun p : Real × M => einsteinScalingFactor κ p.1) := by
          unfold einsteinScalingFactor
          exact contMDiff_const.sub (contMDiff_const.mul contMDiff_fst)
        exact hcm.contMDiffOn
      refine (htime.mul hstaticP).congr (fun p hp => ?_)
      exact einsteinScaledFamily_metric_inner_of_pos g₀ κ hp.1 p.2 (frame i p.2) (frame j p.2)
  smoothConnection := by
    intro t
    have h : (einsteinScaledSolution g₀ κ).family.connectionAt t
        = DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g₀ := by
      rw [DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.connectionAt]
      exact einsteinScaledFamily_connection g₀ κ (t : Real)
    rw [h]
    exact lcConnSmooth g₀
  equation := by
    intro t x X Y
    have hpos : 0 < einsteinScalingFactor κ (t : Real) := t.2
    have hmemc : (t : Real) ∈ (einsteinFlowInterval κ).carrier :=
      (einsteinFlowInterval κ).regular_subset t.2
    have hmetric : (einsteinScaledSolution g₀ κ).base.metric (t : Real)
        = scaleMetric (I := I) (einsteinScalingFactor κ (t : Real)) hpos g₀ :=
      einsteinScaledFamily_metric_of_mem g₀ κ hmemc
    have hRic : RicciAtFamily.toTensorField (I := I)
        (einsteinScaledSolution g₀ κ).ricciAt (t : Real) x X Y = κ * g₀.inner x X Y := by
      have h1 : RicciAtFamily.toTensorField (I := I) (einsteinScaledSolution g₀ κ).ricciAt
          (t : Real) x X Y
          = DifferentialGeometry.Integral.Connection.metricRicciAt (I := I) (M := M)
              ((einsteinScaledSolution g₀ κ).base.metric (t : Real)) x
              (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Y) := by
        simp [RicciAtFamily.toTensorField, SolutionOn.ricciAt, SolutionFamily.ricciAt]
      rw [h1, hmetric, DifferentialGeometry.Integral.Connection.metricRicciAt_scaleMetric]
      exact hEin x X Y
    have hpoly : HasDerivWithinAt (fun s : Real => einsteinScalingFactor κ s * g₀.inner x X Y)
        (-(2 * κ) * g₀.inner x X Y) (einsteinFlowInterval κ).carrier (t : Real) := by
      have h1 : HasDerivWithinAt (fun s : Real => einsteinScalingFactor κ s) (-(2 * κ))
          (einsteinFlowInterval κ).carrier (t : Real) := by
        simpa [einsteinScalingFactor] using
          (((hasDerivWithinAt_id (t : Real) (einsteinFlowInterval κ).carrier).const_mul
            (2 * κ)).const_sub 1)
      simpa using h1.mul_const (g₀.inner x X Y)
    have hval : (-2 : Real) * RicciAtFamily.toTensorField (I := I)
        (einsteinScaledSolution g₀ κ).ricciAt (t : Real) x X Y
        = -(2 * κ) * g₀.inner x X Y := by
      rw [hRic]; ring
    rw [hval]
    exact hpoly.congr_of_mem
      (fun s hs => einsteinScaledFamily_metric_inner_of_pos g₀ κ hs x X Y) hmemc
  scalarCont := by
    have hein : Continuous (einsteinScalingFactor κ) := by
      unfold einsteinScalingFactor; fun_prop
    have hcinv : ContinuousOn (fun q : Real × M => (einsteinScalingFactor κ q.1)⁻¹)
        ((einsteinFlowInterval κ).carrier ×ˢ (Set.univ : Set M)) := by
      refine (hein.comp continuous_fst).continuousOn.inv₀ (fun q hq => ?_)
      exact ne_of_gt hq.1
    have hscal : Continuous (fun q : Real × M => metricScalarAt (I := I) (M := M) g₀ q.2) :=
      (metricScalar_smooth (I := I) (M := M) g₀).continuous.comp continuous_snd
    have hprod : ContinuousOn
        (fun q : Real × M => (einsteinScalingFactor κ q.1)⁻¹ * metricScalarAt (I := I) (M := M) g₀ q.2)
        ((einsteinFlowInterval κ).carrier ×ˢ (Set.univ : Set M)) :=
      hcinv.mul hscal.continuousOn
    refine hprod.congr (fun q hq => ?_)
    exact (einsteinScaled_scalar_eq g₀ κ hq.1 q.2)
  scalarTime := by
    intro K t ht hK x
    have hct : 0 < einsteinScalingFactor κ t := hK ht
    have hdiff : DifferentiableWithinAt Real
        (fun s : Real => (einsteinScalingFactor κ s)⁻¹ * metricScalarAt (I := I) (M := M) g₀ x) K t := by
      refine DifferentiableWithinAt.mul ?_ (differentiableWithinAt_const _)
      refine DifferentiableWithinAt.inv ?_ (ne_of_gt hct)
      unfold einsteinScalingFactor
      fun_prop
    refine hdiff.congr (fun s hs => einsteinScaled_scalar_eq g₀ κ (hK hs) x)
      (einsteinScaled_scalar_eq g₀ κ (hK ht) x)
  ricciCont := by
    refine (metricRicci_const_cont (einsteinFlowInterval κ).carrier g₀).congr (fun t ht x => ?_)
    have hmetric : (einsteinScaledSolution g₀ κ).base.metric t
        = scaleMetric (I := I) (einsteinScalingFactor κ t) ht g₀ :=
      einsteinScaledFamily_metric_of_mem g₀ κ ht
    have h1 : (einsteinScaledSolution g₀ κ).ricci t x
        = DifferentialGeometry.Integral.Connection.metricRicciAt (I := I) (M := M)
            ((einsteinScaledSolution g₀ κ).base.metric t) x := by
      simp [SolutionOn.ricci, SolutionFamily.ricci]
    rw [h1, hmetric, DifferentialGeometry.Integral.Connection.metricRicciAt_scaleMetric]
  rm04Cont := by
    have hf : Continuous (fun q : {t : Real // t ∈ (einsteinFlowInterval κ).carrier} × M =>
        einsteinScalingFactor κ q.1.1) :=
      (by unfold einsteinScalingFactor; fun_prop : Continuous (einsteinScalingFactor κ)).comp
        (continuous_subtype_val.comp continuous_fst)
    refine (DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.smul
      (f := fun (t : Real) (_ : M) => einsteinScalingFactor κ t) hf
      (metricRm04_const_cont (einsteinFlowInterval κ).carrier g₀)).congr (fun t ht x => ?_)
    have hmetric : (einsteinScaledSolution g₀ κ).base.metric t
        = scaleMetric (I := I) (einsteinScalingFactor κ t) ht g₀ :=
      einsteinScaledFamily_metric_of_mem g₀ κ ht
    have h1 : (einsteinScaledSolution g₀ κ).base.rm04 t x
        = DifferentialGeometry.Integral.Connection.metricRm04At (I := I) (M := M)
            ((einsteinScaledSolution g₀ κ).base.metric t) x := by
      simp [SolutionFamily.rm04]
    rw [h1, hmetric, DifferentialGeometry.Integral.Connection.metricRm04At_scaleMetric]
  ricciNormSpace := by
    intro t ht x
    rw [einsteinScaled_ricciNorm_const g₀ κ hEin ht]
    exact mdifferentiableAt_const
  ricciNormGrad := by
    intro t ht x
    rw [einsteinScaled_ricciNorm_const g₀ κ hEin ht]
    simp only [DifferentialGeometry.Integral.Connection.gradientFun_const]
    exact mdifferentiableAt_zeroSection (𝕜 := Real) (E := fun y : M => TangentSpace I y) (F := E)

theorem einsteinScaled_isRealizedRicciFlowSolutionOn
    (g₀ : SmoothRiemannianMetric I M) (κ : Real)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀ κ) :
    DifferentialGeometry.Integral.Connection.IsRealizedRicciFlowSolutionOn (I := I)
      (einsteinScaledSolution g₀ κ).toRealizedCandidate :=
  isRealizedRicciFlowSolutionOn_of_isSolutionOn (I := I)
    (einsteinScaled_isSolutionOn g₀ κ hEin)

private theorem nabla2OneFormRealizesAt_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaAlpha : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (c : Real)
    (h : DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
      cov alpha nablaAlpha x nabla2Alpha) :
    DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
      cov (c • alpha) (c • nablaAlpha) x (c • nabla2Alpha) := by
  refine ⟨?_, ?_⟩
  · intro y X Y
    have h1 := h.1 y X Y
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
      nabla0SFun_smul, h1]
  · intro X Y Z
    have h2 := h.2 X Y Z
    simp only [Tensor0SSpace.smul_apply, nabla0SFun_smul, h2]

private theorem roughLap0STensor_smul_arg {x : M} {s : ℕ}
    (g : SmoothRiemannianMetric I M) (c : Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) g (c • T) tail
      = c * DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) g T tail := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x k l (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x
  rw [DifferentialGeometry.Integral.Connection.roughLap0STensor_apply,
    DifferentialGeometry.Integral.Connection.roughLap0STensor_apply,
    DifferentialGeometry.Integral.Connection.metricTraceFirstTwo0SAt,
    DifferentialGeometry.Integral.Connection.metricTraceFirstTwo0SAt,
    DifferentialGeometry.Integral.Connection.metricTracePair0SAt_eq_sum_basis
      (I := I) g basis gInv hinv,
    DifferentialGeometry.Integral.Connection.metricTracePair0SAt_eq_sum_basis
      (I := I) g basis gInv hinv, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.freezeFirstTwo0S_apply,
    DifferentialGeometry.Integral.Connection.freezeFirstTwo0S_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  ring

private theorem einsteinScaledProbe_eq_smul (κ : Real)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (t : Real) :
    einsteinScaledProbe κ alpha t
      = (Real.rpow (einsteinScalingFactor κ t) (-(1 / 2 : Real))) • alpha := by
  refine DFunLike.coe_injective (funext (fun x => ?_))
  simp only [einsteinScaledProbe, tensor0SField_smulByFun_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply]

private theorem einsteinScaledProbeNabla_eq_smul (κ : Real)
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (t : Real) :
    einsteinScaledProbeNabla κ nablaOmega t
      = (Real.rpow (einsteinScalingFactor κ t) (-(1 / 2 : Real))) • nablaOmega := by
  refine DFunLike.coe_injective (funext (fun x => ?_))
  simp only [einsteinScaledProbeNabla, tensor0SField_smulByFun_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply]

private theorem einsteinScalingFactor_hasDerivAt (κ s0 : Real) :
    HasDerivAt (fun s : Real => einsteinScalingFactor κ s) (-(2 * κ)) s0 := by
  unfold einsteinScalingFactor
  simpa using ((hasDerivAt_id s0).const_mul (2 * κ)).const_sub 1

private theorem einsteinScaledProbe_time_smooth (κ : Real) {u : Set M} :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => Real.rpow (einsteinScalingFactor κ p.1) (-(1 / 2 : Real)))
      ((einsteinFlowInterval κ).regular ×ˢ u) := by
  have hcd : ContDiff Real ∞ (fun t : Real => einsteinScalingFactor κ t) := by
    unfold einsteinScalingFactor; fun_prop
  have hφ : ContDiffOn Real ∞ (fun t : Real => (einsteinScalingFactor κ t) ^ (-(1 / 2 : Real)))
      (einsteinFlowInterval κ).regular :=
    ContDiffOn.rpow_const_of_ne hcd.contDiffOn (fun t ht => ne_of_gt ht)
  exact ((contMDiffOn_iff_contDiffOn).mpr hφ).comp contMDiff_fst.contMDiffOn (fun p hp => hp.1)

set_option linter.unusedVariables false in
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
      (einsteinScaledProbeNabla2 κ nabla2Omega) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x
    have hconn : (einsteinScaledSolution g₀ κ).family.connection (t : Real)
        = metricCov (I := I) (M := M) g₀ := by
      rw [SolutionOn.family_connection]
      exact einsteinScaledFamily_connection g₀ κ (t : Real)
    rw [hconn, einsteinScaledProbe_eq_smul, einsteinScaledProbeNabla_eq_smul]
    exact nabla2OneFormRealizesAt_smul (metricCov (I := I) (M := M) g₀) alpha nablaOmega x
      (nabla2Omega x) (Real.rpow (einsteinScalingFactor κ (t : Real)) (-(1 / 2 : Real)))
      (hRealizes x)
  · intro t x X
    set s0 : Real := (t : Real) with hs0def
    have hs0 : 0 < einsteinScalingFactor κ s0 := t.2
    have hmemc : s0 ∈ (einsteinFlowInterval κ).carrier :=
      (einsteinFlowInterval κ).regular_subset t.2
    have hfun : (fun s : Real => einsteinScaledProbe κ alpha s x (fun _ : Fin 1 => X))
        = fun s : Real =>
            Real.rpow (einsteinScalingFactor κ s) (-(1 / 2 : Real))
              * (alpha x (fun _ : Fin 1 => X)) := by
      funext s
      simp only [einsteinScaledProbe, tensor0SField_smulByFun_apply,
        Tensor0SSpace.smul_apply, smul_eq_mul]
    have hbase : HasDerivAt
        (fun s : Real => (einsteinScalingFactor κ s) ^ (-(1 / 2 : Real)))
        (-(2 * κ) * (-(1 / 2 : Real))
          * (einsteinScalingFactor κ s0) ^ ((-(1 / 2 : Real)) - 1)) s0 :=
      (einsteinScalingFactor_hasDerivAt κ s0).rpow_const (Or.inl (ne_of_gt hs0))
    have htarget : DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I)
          ((einsteinScaledSolution g₀ κ).family.metric s0)
          (s := 1) (einsteinScaledProbeNabla2 κ nabla2Omega s0 x) (fun _ : Fin 1 => X)
        = (-(2 * κ) * (-(1 / 2 : Real))
            * (einsteinScalingFactor κ s0) ^ ((-(1 / 2 : Real)) - 1))
              * (alpha x (fun _ : Fin 1 => X)) := by
      have hms : (einsteinScaledSolution g₀ κ).family.metric s0
          = scaleMetric (I := I) (einsteinScalingFactor κ s0) hs0 g₀ :=
        einsteinScaledFamily_metric_of_mem g₀ κ hmemc
      have hprobe2 : einsteinScaledProbeNabla2 κ nabla2Omega s0 x
          = (Real.rpow (einsteinScalingFactor κ s0) (-(1 / 2 : Real))) • nabla2Omega x := rfl
      rw [hms, hprobe2, DifferentialGeometry.Integral.Connection.roughLap0STensor_scaleMetric,
        roughLap0STensor_smul_arg, hEigen x X,
        show Real.rpow (einsteinScalingFactor κ s0) (-(1 / 2 : Real))
            = (einsteinScalingFactor κ s0) ^ (-(1 / 2 : Real)) from rfl]
      have hpow : (einsteinScalingFactor κ s0)⁻¹
            * (einsteinScalingFactor κ s0) ^ (-(1 / 2 : Real))
          = (einsteinScalingFactor κ s0) ^ ((-(1 / 2 : Real)) - 1) := by
        rw [← Real.rpow_neg_one (einsteinScalingFactor κ s0), ← Real.rpow_add hs0]
        congr 1
        norm_num
      rw [show (einsteinScalingFactor κ s0)⁻¹
            * ((einsteinScalingFactor κ s0) ^ (-(1 / 2 : Real))
              * (κ * (alpha x (fun _ : Fin 1 => X))))
          = ((einsteinScalingFactor κ s0)⁻¹
              * (einsteinScalingFactor κ s0) ^ (-(1 / 2 : Real)))
            * (κ * (alpha x (fun _ : Fin 1 => X))) from by ring, hpow]
      ring
    rw [hfun, htarget]
    exact hbase.mul_const (alpha x (fun _ : Fin 1 => X))
  · intro Idx _ frame u hframe i
    have hA : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => alpha p.2 (fun _ : Fin 1 => frame i p.2))
        ((einsteinFlowInterval κ).regular ×ˢ u) :=
      (Tensor0SBundle.contMDiffOn_tensor0SField_eval_localFrame_of_isLocalFrameOn
        alpha frame hframe (fun _ : Fin 1 => i)).comp contMDiff_snd.contMDiffOn
        (fun p hp => hp.2)
    refine ((einsteinScaledProbe_time_smooth κ).mul hA).congr (fun p hp => ?_)
    simp only [Pi.mul_apply, einsteinScaledProbe, tensor0SField_smulByFun_apply,
      Tensor0SSpace.smul_apply, smul_eq_mul]
  · intro Idx _ frame u hframe i j
    have hAspace : ContMDiffOn I 𝓘(Real, Real) ∞
        (fun y : M => nablaOmega y
          (DifferentialGeometry.Integral.Connection.vec2 (frame i y) (frame j y))) u := by
      refine (Tensor0SBundle.contMDiffOn_tensor0SField_eval_localFrame_of_isLocalFrameOn
        nablaOmega frame hframe ![i, j]).congr (fun y _ => ?_)
      congr 1
      funext a
      fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2]
    have hA : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => nablaOmega p.2
          (DifferentialGeometry.Integral.Connection.vec2 (frame i p.2) (frame j p.2)))
        ((einsteinFlowInterval κ).regular ×ˢ u) :=
      hAspace.comp contMDiff_snd.contMDiffOn (fun p hp => hp.2)
    refine ((einsteinScaledProbe_time_smooth κ).mul hA).congr (fun p hp => ?_)
    simp only [Pi.mul_apply, einsteinScaledProbeNabla, tensor0SField_smulByFun_apply,
      Tensor0SSpace.smul_apply, smul_eq_mul]

private theorem einsteinScalingFactor_hasDerivAt_zero (κ : Real) :
    HasDerivAt (fun s : Real => einsteinScalingFactor κ s) (-(2 * κ)) 0 := by
  unfold einsteinScalingFactor
  simpa using ((hasDerivAt_id (0 : Real)).const_mul (2 * κ)).const_sub 1

private theorem einsteinScaling_rpow_sq {κ s : Real}
    (hs : 0 < einsteinScalingFactor κ s) :
    (Real.rpow (einsteinScalingFactor κ s) (-(1 / 2 : Real))) ^ 2
      = (einsteinScalingFactor κ s)⁻¹ := by
  have hsum : (-(1 / 2 : Real)) + (-(1 / 2 : Real)) = -1 := by norm_num
  change (einsteinScalingFactor κ s ^ (-(1 / 2 : Real))) ^ 2 = (einsteinScalingFactor κ s)⁻¹
  rw [pow_two, ← Real.rpow_add hs, hsum, Real.rpow_neg hs.le, Real.rpow_one]

private theorem einsteinScaling_cinv3_hasDerivAt (κ : Real) :
    HasDerivAt (fun s : Real => (einsteinScalingFactor κ s)⁻¹ ^ 3) (6 * κ) 0 := by
  have hu0 : einsteinScalingFactor κ 0 ≠ 0 := by rw [einsteinScalingFactor_zero]; norm_num
  have hinv : HasDerivAt (fun s : Real => (einsteinScalingFactor κ s)⁻¹) (2 * κ) 0 := by
    have h := (einsteinScalingFactor_hasDerivAt_zero κ).inv hu0
    rw [einsteinScalingFactor_zero] at h
    simpa using h
  have h3 := hinv.pow 3
  rw [einsteinScalingFactor_zero] at h3
  have hvaleq : (3 : ℕ) * (1 : Real)⁻¹ ^ (3 - 1) * (2 * κ) = 6 * κ := by
    rw [inv_one, one_pow]; push_cast; ring
  rw [hvaleq] at h3
  exact h3

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
      0 := by
  classical
  set G := (einsteinScaledSolution g₀ κ).family with hGdef
  set f : Real → M → Real :=
    fun s x => normSq0S (I := I) (G.metric s) x 2 (einsteinScaledProbeNabla κ nablaOmega s x)
    with hfdef
  have hc0 : (0 : Real) < einsteinScalingFactor κ 0 := by
    rw [einsteinScalingFactor_zero]; norm_num
  have hU : IsOpen ((einsteinFlowInterval κ).regular) := (einsteinFlowInterval κ).regular_isOpen
  have h0U : (0 : Real) ∈ (einsteinFlowInterval κ).regular := hc0
  have h0mem : (0 : Real) ∈ (einsteinFlowInterval κ).carrier := hc0
  have hpt : ∀ (s : Real), 0 < einsteinScalingFactor κ s → ∀ x : M,
      normSq0S (I := I) (G.metric s) x 2 (einsteinScaledProbeNabla κ nablaOmega s x)
        = (einsteinScalingFactor κ s)⁻¹ ^ 3 * normSq0S (I := I) g₀ x 2 (nablaOmega x) := by
    intro s hs x
    have hmem : s ∈ (einsteinFlowInterval κ).carrier := hs
    have hms : G.metric s = scaleMetric (I := I) (einsteinScalingFactor κ s) hs g₀ :=
      einsteinScaledFamily_metric_of_mem g₀ κ hmem
    have hprobe : einsteinScaledProbeNabla κ nablaOmega s x
        = (Real.rpow (einsteinScalingFactor κ s) (-(1 / 2 : Real))) • nablaOmega x := by
      simp only [einsteinScaledProbeNabla, tensor0SField_smulByFun_apply]
    rw [hms, hprobe, normSq0S_two_scale, normSq0S_smul, einsteinScaling_rpow_sq hs]
    ring
  have hS := einsteinScaled_isSolutionOn g₀ κ hEin
  have hg : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
        ((einsteinFlowInterval κ).regular ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j =>
      chartGram_jointContMDiffOn_of_metricFamilySmoothOn (I := I) (M := M) G hS.smoothMetric x₀ i j
  have hN : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => normSq0S (I := I) g₀ p.2 2 (nablaOmega p.2))
      ((einsteinFlowInterval κ).regular ×ˢ (Set.univ : Set M)) :=
    ((DifferentialGeometry.Integral.Connection.normSq0S_smooth (I := I) g₀ nablaOmega).comp
      contMDiff_snd).contMDiffOn
  have hθ : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => (einsteinScalingFactor κ p.1)⁻¹ ^ 3)
      ((einsteinFlowInterval κ).regular ×ˢ (Set.univ : Set M)) := by
    have hφ : ContDiffOn Real ∞ (fun t : Real => (einsteinScalingFactor κ t)⁻¹ ^ 3)
        (einsteinFlowInterval κ).regular := by
      have hpoly : ContDiff Real ∞ (fun t : Real => einsteinScalingFactor κ t) := by
        unfold einsteinScalingFactor; fun_prop
      exact (hpoly.contDiffOn.inv (fun t ht => ne_of_gt ht)).pow 3
    exact ((contMDiffOn_iff_contDiffOn).mpr hφ).comp contMDiff_fst.contMDiffOn (fun p hp => hp.1)
  have hf : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        normSq0S (I := I) (G.metric p.1) p.2 2 (einsteinScaledProbeNabla κ nablaOmega p.1 p.2))
      ((einsteinFlowInterval κ).regular ×ˢ (Set.univ : Set M)) :=
    (hθ.mul hN).congr (fun p hp => hpt p.1 hp.1 p.2)
  have hmet0 : G.metric 0 = scaleMetric (I := I) (einsteinScalingFactor κ 0) hc0 g₀ :=
    einsteinScaledFamily_metric_of_mem g₀ κ h0mem
  have hμ0 : riemannianMeasureFamily (I := I) (M := M) (fun t => G.metric t) 0
      = riemannianVolumeMeasure (I := I) (M := M) g₀ := by
    rw [riemannianMeasureFamily_def]
    change riemannianVolumeMeasure (I := I) (M := M) (G.metric 0) = _
    rw [hmet0, volume_scaleMetric, einsteinScalingFactor_zero]
    simp [Real.sqrt_one]
  have hf0 : ∀ x : M, f 0 x = normSq0S (I := I) g₀ x 2 (nablaOmega x) := by
    intro x
    change normSq0S (I := I) (G.metric 0) x 2 (einsteinScaledProbeNabla κ nablaOmega 0 x)
        = normSq0S (I := I) g₀ x 2 (nablaOmega x)
    rw [hpt 0 hc0 x, einsteinScalingFactor_zero]
    norm_num
  have hderivf : ∀ x : M,
      deriv (fun s => f s x) 0 = 6 * κ * normSq0S (I := I) g₀ x 2 (nablaOmega x) := by
    intro x
    have heq : (fun s => f s x) =ᶠ[nhds (0 : Real)]
        (fun s => (einsteinScalingFactor κ s)⁻¹ ^ 3 * normSq0S (I := I) g₀ x 2 (nablaOmega x)) := by
      refine Filter.eventually_of_mem (hU.mem_nhds h0U) (fun s hs => ?_)
      change normSq0S (I := I) (G.metric s) x 2 (einsteinScaledProbeNabla κ nablaOmega s x)
          = (einsteinScalingFactor κ s)⁻¹ ^ 3 * normSq0S (I := I) g₀ x 2 (nablaOmega x)
      exact hpt s hs x
    have hbase : HasDerivAt
        (fun s : Real => (einsteinScalingFactor κ s)⁻¹ ^ 3 * normSq0S (I := I) g₀ x 2 (nablaOmega x))
        (6 * κ * normSq0S (I := I) g₀ x 2 (nablaOmega x)) 0 :=
      (einsteinScaling_cinv3_hasDerivAt κ).mul_const _
    rw [heq.deriv_eq, hbase.deriv]
  have htrace : ∀ x : M, traceTimeDerivMetric (I := I) (fun t => G.metric t) 0 x
      = -(2 * κ) * (Module.finrank Real E : Real) := by
    intro x
    have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x
    have hdet_unit : IsUnit (chartGramMatrix (I := I) g₀ x x).det :=
      isUnit_iff_ne_zero.mpr (chartGramMatrix_det_pos (I := I) g₀ x hx).ne'
    have hGram0 : chartGramMatrix (I := I) (G.metric 0) x x = chartGramMatrix (I := I) g₀ x x := by
      rw [hmet0, chartGram_scale, einsteinScalingFactor_zero, one_smul]
    have hderivGram : ∀ i j : Fin (Module.finrank Real E),
        deriv (fun s => chartGramMatrix (I := I) (G.metric s) x x i j) 0
          = -(2 * κ) * chartGramMatrix (I := I) g₀ x x i j := by
      intro i j
      have heqe : (fun s => chartGramMatrix (I := I) (G.metric s) x x i j) =ᶠ[nhds (0 : Real)]
          (fun s => einsteinScalingFactor κ s * chartGramMatrix (I := I) g₀ x x i j) := by
        refine Filter.eventually_of_mem (hU.mem_nhds h0U) (fun s hs => ?_)
        change chartGramMatrix (I := I) (G.metric s) x x i j
            = einsteinScalingFactor κ s * chartGramMatrix (I := I) g₀ x x i j
        have hms : G.metric s = scaleMetric (I := I) (einsteinScalingFactor κ s) hs g₀ :=
          einsteinScaledFamily_metric_of_mem g₀ κ hs
        rw [hms, chartGram_scale, Matrix.smul_apply, smul_eq_mul]
      have hbase :=
        (einsteinScalingFactor_hasDerivAt_zero κ).mul_const (chartGramMatrix (I := I) g₀ x x i j)
      rw [heqe.deriv_eq, hbase.deriv]
    simp only [traceTimeDerivMetric_eq]
    rw [hGram0]
    have hMof : (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          deriv (fun s => chartGramMatrix (I := I) (G.metric s) x x i j) 0)
        = (-(2 * κ)) • chartGramMatrix (I := I) g₀ x x := by
      ext i j
      rw [Matrix.of_apply, hderivGram i j, Matrix.smul_apply, smul_eq_mul]
    rw [hMof, mul_smul_comm, Matrix.trace_smul, Matrix.nonsing_inv_mul _ hdet_unit,
      Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  have hval : (∫ x, (deriv (fun s => f s x) 0
        + 1 / 2 * traceTimeDerivMetric (I := I) (fun t => G.metric t) 0 x * f 0 x)
        ∂(riemannianMeasureFamily (I := I) (M := M) (fun t => G.metric t) 0))
      = κ ^ 2 * ((Module.finrank Real E : Real) - 6)
          * ∫ x, normSq0S (I := I) g₀ x 1 (alpha x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have hintegrand : ∀ x : M,
        deriv (fun s => f s x) 0
            + 1 / 2 * traceTimeDerivMetric (I := I) (fun t => G.metric t) 0 x * f 0 x
          = (-κ * ((Module.finrank Real E : Real) - 6)) * normSq0S (I := I) g₀ x 2 (nablaOmega x) := by
      intro x
      rw [hderivf x, htrace x, hf0 x]
      ring
    rw [hμ0, integral_congr_ae (Filter.Eventually.of_forall hintegrand), integral_const_mul,
      DifferentialGeometry.Integral.Connection.oneForm_gradNormSq_integral_eq_neg_eigen g₀ κ alpha nablaOmega nabla2Omega hRealizes hEigen]
    ring
  have hmain := first_var_joint (g_fam := fun t => G.metric t) (f := f) hU h0U hg hf
  rw [hval] at hmain
  exact hmain

set_option linter.unusedVariables false in
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
      0 := by
  have h := einsteinScaled_gradEnergy_hasDerivAt g₀ (-((Module.finrank Real E : Real) - 1))
    alpha nablaOmega nabla2Omega hEin hRealizes hEigen
  rw [neg_sq] at h
  exact h

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
      0 0 := by
  have h := einsteinScaled_gradEnergy_hasDerivAt g₀ κ alpha nablaOmega nabla2Omega
    hEin hRealizes hEigen
  have hval0 : κ ^ 2 * ((Module.finrank Real E : Real) - 6)
      * (∫ x, normSq0S (I := I) g₀ x 1 (alpha x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) = 0 := by
    have h6 : (Module.finrank Real E : Real) = 6 := by exact_mod_cast hdim
    rw [h6]; ring
  rw [hval0] at h
  exact h

theorem hyperbolicScaled_isSolutionOn
    (g₀ : SmoothRiemannianMetric I M)
    (hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀
      (-((Module.finrank Real E : Real) - 1))) :
    IsSolutionOn (I := I)
      (einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))) :=
  einsteinScaled_isSolutionOn g₀ (-((Module.finrank Real E : Real) - 1)) hEin

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
      (einsteinScaledProbeNabla2 (-((Module.finrank Real E : Real) - 1)) nabla2Omega) :=
  einsteinScaled_isHeatOneFormOn g₀ (-((Module.finrank Real E : Real) - 1))
    alpha nablaOmega nabla2Omega hEin hRealizes hEigen

theorem hyperbolicScaled_gradEnergy_deriv_pos [CompactSpace M]
    (g₀ : SmoothRiemannianMetric I M)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (hn : 7 ≤ Module.finrank Real E)
    (halpha : ∃ x : M, alpha x ≠ 0) :
    0 < ((Module.finrank Real E : Real) - 1) ^ 2 * ((Module.finrank Real E : Real) - 6) *
      ∫ x, normSq0S (I := I) g₀ x 1 (alpha x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
  obtain ⟨x₀, hx⟩ := halpha
  have hn' : (7 : Real) ≤ (Module.finrank Real E : Real) := by exact_mod_cast hn
  have hA : (0 : Real) < (Module.finrank Real E : Real) - 1 := by linarith
  have hB : (0 : Real) < (Module.finrank Real E : Real) - 6 := by linarith
  have hInt : 0 < ∫ x, normSq0S (I := I) g₀ x 1 (alpha x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.L2.integral_normSq0S_pos g₀ (s := 1) alpha x₀ hx
  exact mul_pos (mul_pos (pow_pos hA 2) hB) hInt

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
      0 0 := by
  have h := einsteinScaled_gradEnergy_hasDerivAt g₀ (-((Module.finrank Real E : Real) - 1))
    alpha nablaOmega nabla2Omega hEin hRealizes hEigen
  have hval0 : (-((Module.finrank Real E : Real) - 1)) ^ 2 * ((Module.finrank Real E : Real) - 6)
      * (∫ x, normSq0S (I := I) g₀ x 1 (alpha x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) = 0 := by
    have h6 : (Module.finrank Real E : Real) = 6 := by exact_mod_cast hdim
    rw [h6]; ring
  rw [hval0] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow
