import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.First
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Reparametrization
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
import DifferentialGeometry.Bundle.TangentSpace
import DifferentialGeometry.Geometry.Comparison.Variation.Field.ChartConstruction
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Geodesic.Flow.ChartPhase
import DifferentialGeometry.Geometry.Metric.Family.DifferentialOperatorRegularity
import DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.JointRegularity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Bundle
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

def HasLEquationAt
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (tau : Real) : Prop :=
  MDifferentiableAt 𝓘(Real, Real) I gamma tau ∧
    DifferentiableAt Real
      (chartRepAt (I := I) gamma
        (fun s : Real => lVelocity (I := I) gamma s) tau) tau ∧
    ∀ Y : TangentSpace I (gamma tau), lEulerPair S T gamma tau Y = 0

def IsLGeodesic
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (s : Set Real) : Prop :=
  (∀ tau ∈ s, 0 < tau ∧ T - tau ∈ D.regular) ∧
    ∀ tau ∈ s, HasLEquationAt S T gamma tau

def IsLCritical
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (a b : Real) : Prop :=
  ContMDiff 𝓘(Real, Real) I (8 : Nat) gamma ∧
    ∀ f : Real → Real → M,
      IsSmoothVariation (I := I) f →
      f 0 = gamma →
      (∀ u, f u a = gamma a) →
      (∀ u, f u b = gamma b) →
      HasDerivAt
        (fun u : Real => lLength S T (fun tau : Real => f u tau) a b)
        0 0

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem IsLGeodesic.at
    {S : SolutionOn (I := I) (M := M) D} {T : Real} {gamma : Real → M}
    {s : Set Real} (hgamma : IsLGeodesic S T gamma s)
    {tau : Real} (htau : tau ∈ s) :
    HasLEquationAt S T gamma tau :=
  hgamma.2 tau htau

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem IsLGeodesic.pos
    {S : SolutionOn (I := I) (M := M) D} {T : Real} {gamma : Real → M}
    {s : Set Real} (hgamma : IsLGeodesic S T gamma s)
    {tau : Real} (htau : tau ∈ s) :
    0 < tau :=
  (hgamma.1 tau htau).1

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem IsLGeodesic.regular
    {S : SolutionOn (I := I) (M := M) D} {T : Real} {gamma : Real → M}
    {s : Set Real} (hgamma : IsLGeodesic S T gamma s)
    {tau : Real} (htau : tau ∈ s) :
    T - tau ∈ D.regular :=
  (hgamma.1 tau htau).2

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem IsLGeodesic.mdiffAt
    {S : SolutionOn (I := I) (M := M) D} {T : Real} {gamma : Real → M}
    {s : Set Real} (hgamma : IsLGeodesic S T gamma s)
    {tau : Real} (htau : tau ∈ s) :
    MDifferentiableAt 𝓘(Real, Real) I gamma tau :=
  (hgamma.at htau).1

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem IsLGeodesic.velDiffAt
    {S : SolutionOn (I := I) (M := M) D} {T : Real} {gamma : Real → M}
    {s : Set Real} (hgamma : IsLGeodesic S T gamma s)
    {tau : Real} (htau : tau ∈ s) :
    DifferentiableAt Real
      (chartRepAt (I := I) gamma
        (fun r : Real => lVelocity (I := I) gamma r) tau) tau :=
  (hgamma.at htau).2.1

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem IsLGeodesic.euler
    {S : SolutionOn (I := I) (M := M) D} {T : Real} {gamma : Real → M}
    {s : Set Real} (hgamma : IsLGeodesic S T gamma s)
    {tau : Real} (htau : tau ∈ s) (Y : TangentSpace I (gamma tau)) :
    lEulerPair S T gamma tau Y = 0 :=
  (hgamma.at htau).2.2 Y

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem IsLGeodesic.mono
    {S : SolutionOn (I := I) (M := M) D} {T : Real} {gamma : Real → M}
    {s s' : Set Real} (hgamma : IsLGeodesic S T gamma s)
    (hsub : s' ⊆ s) :
    IsLGeodesic S T gamma s' :=
  ⟨fun tau htau => hgamma.1 tau (hsub htau),
    fun tau htau => hgamma.2 tau (hsub htau)⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lFirst_var_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (hgeo : IsLGeodesic S T (f 0) (Set.uIcc a b))
    (hYa : lVelocity (I := I) (fun u : Real => f u a) 0 = 0)
    (hYb : lVelocity (I := I) (fun u : Real => f u b) 0 = 0) :
    HasDerivAt
      (fun u : Real => lLength S T (fun tau : Real => f u tau) a b)
      0 0 := by
  have hpos : 0 < min a b :=
    lt_min (hgeo.pos Set.left_mem_uIcc) (hgeo.pos Set.right_mem_uIcc)
  have ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular :=
    fun tau htau => hgeo.regular htau
  have hres : (∫ tau in a..b,
      (-2 * Real.sqrt tau) *
        lEulerPair S T (f 0) tau
          (lVelocity (I := I) (fun u : Real => f u tau) 0)) = 0 := by
    rw [intervalIntegral.integral_congr (fun tau htau => by
      rw [hgeo.euler htau])]
    simp
  apply (lLength_euler S hS T f hf a b hpos ht).congr_deriv
  rw [hres, hYa, hYb]
  simp

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem IsLGeodesic.critical
    {S : SolutionOn (I := I) (M := M) D}
    {T : Real} {gamma : Real → M} {a b : Real}
    (hgeo : IsLGeodesic S T gamma (Set.uIcc a b))
    (hS : IsSolutionOn (I := I) S)
    (hgamma : ContMDiff 𝓘(Real, Real) I (8 : Nat) gamma) :
    IsLCritical S T gamma a b := by
  refine ⟨hgamma, ?_⟩
  intro f hf hcentral hfixa hfixb
  have hgeo' : IsLGeodesic S T (f 0) (Set.uIcc a b) := by
    rw [hcentral]
    exact hgeo
  have hYa : lVelocity (I := I) (fun u : Real => f u a) 0 = 0 := by
    have hconst : (fun u : Real => f u a) = fun _ : Real => gamma a := by
      funext u
      exact hfixa u
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hYb : lVelocity (I := I) (fun u : Real => f u b) 0 = 0 := by
    have hconst : (fun u : Real => f u b) = fun _ : Real => gamma b := by
      funext u
      exact hfixb u
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  exact lFirst_var_zero S hS T f hf a b hgeo' hYa hYb

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem IsLCritical.isLGeo
    {S : SolutionOn (I := I) (M := M) D}
    {T : Real} {gamma : Real → M} {a b : Real}
    (hcrit : IsLCritical S T gamma a b)
    (hS : IsSolutionOn (I := I) S)
    (ha : 0 < a) (hab : a < b)
    (ht : ∀ tau ∈ Set.Icc a b, T - tau ∈ D.regular) :
    IsLGeodesic S T gamma (Set.Ioo a b) := by
  rcases hcrit with ⟨hgamma, hstationary⟩
  have hpos : 0 < min a b := by
    rw [min_eq_left hab.le]
    exact ha
  have htU : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular := by
    simpa only [Set.uIcc_of_le hab.le] using ht
  have hIooU : Set.Ioo a b ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le]
    exact Set.Ioo_subset_Icc_self
  have hfconst : IsSmoothVariation (I := I) (fun _ : Real => gamma) := by
    change ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
      (fun p : Real × Real => gamma p.2)
    exact hgamma.comp contMDiff_snd
  refine ⟨?_, ?_⟩
  · intro tau htau
    exact ⟨ha.trans htau.1, ht tau (Set.Ioo_subset_Icc_self htau)⟩
  · intro tau0 htau0
    have hmd : MDifferentiableAt 𝓘(Real, Real) I gamma tau0 :=
      hgamma.contMDiffAt.mdifferentiableAt (by norm_num)
    have hvel : DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun r : Real => lVelocity (I := I) gamma r) tau0) tau0 := by
      simpa only [lVelocity] using
        velocityField_chartRep_differentiableAt
          (I := I) (fun _ : Real => gamma) hfconst tau0
    refine ⟨hmd, hvel, ?_⟩
    intro Y
    let c : M := gamma tau0
    let e := trivializationAt E (TangentSpace I) c
    let w : E := e.continuousLinearMapAt Real c Y
    have hw : e.symmL Real c w = Y := by
      simpa only [w] using
        e.symmL_continuousLinearMapAt (R := Real)
          (FiberBundle.mem_baseSet_trivializationAt' c) Y
    let U : Set Real := gamma ⁻¹' (chartAt H c).source
    have hUopen : IsOpen U :=
      (chartAt H c).open_source.preimage hgamma.continuous
    have htauU : tau0 ∈ U := by
      change gamma tau0 ∈ (chartAt H c).source
      simpa only [c] using (mem_chart_source H (gamma tau0))
    obtain ⟨beta, hbetasub, hbetac, hbetasm, _hbetarange, hbetaone⟩ :=
      exists_contDiff_tsupport_subset
        (E := Real) (n := (⊤ : ℕ∞)) (x := tau0)
        (hUopen.mem_nhds htauU)
    let V0 : Real → E := fun tau => beta tau • w
    have hV0sm : ContDiff Real (8 : Nat) V0 := by
      change ContDiff Real (8 : Nat) (beta • fun _ : Real => w)
      exact (hbetasm.of_le
        (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ ⊤))).smul
          contDiff_const
    have hV0c : HasCompactSupport V0 := by
      change HasCompactSupport (beta • fun _ : Real => w)
      exact hbetac.smul_right
    have hV0src : ∀ tau ∈ tsupport V0,
        gamma tau ∈ (chartAt H c).source := by
      intro tau htau
      have htau' : tau ∈ tsupport beta :=
        (tsupport_smul_subset_left beta (fun _ : Real => w)) htau
      exact hbetasub htau'
    obtain ⟨f0, hf0, hf0central, hf0vel, _hf0fix⟩ :=
      exists_chartVar (I := I) c gamma V0 hgamma hV0sm hV0c hV0src
    have hcenter0 : f0 0 = gamma := funext hf0central
    let F : Real → Real := fun tau =>
      (-2 * Real.sqrt tau) *
        lEulerPair S T gamma tau
          (lVelocity (I := I) (fun u : Real => f0 u tau) 0)
    have hFcont : ContinuousOn F (Set.Ioo a b) := by
      have hraw :=
        (lEuler_contOn S hS T f0 hf0 a b hpos htU).mono hIooU
      rw [hcenter0] at hraw
      simpa only [F] using hraw
    have hFloc : MeasureTheory.LocallyIntegrableOn F (Set.Ioo a b)
        (MeasureTheory.volume : MeasureTheory.Measure Real) :=
      hFcont.locallyIntegrableOn measurableSet_Ioo
    have htest : ∀ g : Real → Real,
        ContDiff Real ∞ g → HasCompactSupport g →
        tsupport g ⊆ Set.Ioo a b →
        (∫ tau, g tau • F tau ∂MeasureTheory.volume) = 0 := by
      intro g hg hgc hgsub
      let Vg : Real → E := fun tau => g tau • V0 tau
      have hVgsm : ContDiff Real (8 : Nat) Vg := by
        change ContDiff Real (8 : Nat) (g • V0)
        exact (hg.of_le
          (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ ⊤))).smul
            hV0sm
      have hVgc : HasCompactSupport Vg := by
        change HasCompactSupport (g • V0)
        exact hV0c.smul_left
      have hVgsrc : ∀ tau ∈ tsupport Vg,
          gamma tau ∈ (chartAt H c).source := by
        intro tau htau
        exact hV0src tau ((tsupport_smul_subset_right g V0) htau)
      obtain ⟨fg, hfg, hfgcentral, hfgvel, hfgfix⟩ :=
        exists_chartVar (I := I) c gamma Vg hgamma hVgsm hVgc hVgsrc
      have hcenterg : fg 0 = gamma := funext hfgcentral
      have hfield : ∀ tau,
          lVelocity (I := I) (fun u : Real => fg u tau) 0 =
            g tau • lVelocity (I := I) (fun u : Real => f0 u tau) 0 := by
        intro tau
        change ((mfderiv 𝓘(Real, Real) I
            (fun u : Real => fg u tau) 0 (1 : Real)) : E) =
          g tau • ((mfderiv 𝓘(Real, Real) I
            (fun u : Real => f0 u tau) 0 (1 : Real)) : E)
        rw [hfgvel tau, hf0vel tau]
        simp only [Vg, ContinuousLinearMap.map_smul]
        rfl
      have hga : g a = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ha_mem =>
          (lt_irrefl a) (hgsub ha_mem).1)
      have hgb : g b = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hb_mem =>
          (lt_irrefl b) (hgsub hb_mem).2)
      have hfixa : ∀ u, fg u a = gamma a := by
        intro u
        apply hfgfix u a
        simp only [Vg, hga, zero_smul]
      have hfixb : ∀ u, fg u b = gamma b := by
        intro u
        apply hfgfix u b
        simp only [Vg, hgb, zero_smul]
      have hstat := hstationary fg hfg hcenterg hfixa hfixb
      have hYa : lVelocity (I := I) (fun u : Real => fg u a) 0 = 0 := by
        have hconst : (fun u : Real => fg u a) = fun _ : Real => gamma a := by
          funext u
          exact hfixa u
        rw [hconst]
        simp only [lVelocity, mfderiv_const]
        rfl
      have hYb : lVelocity (I := I) (fun u : Real => fg u b) 0 = 0 := by
        have hconst : (fun u : Real => fg u b) = fun _ : Real => gamma b := by
          funext u
          exact hfixb u
        rw [hconst]
        simp only [lVelocity, mfderiv_const]
        rfl
      have hvalue :=
        (lLength_euler S hS T fg hfg a b hpos htU).unique hstat
      have hint : (∫ tau in a..b,
          (-2 * Real.sqrt tau) *
            lEulerPair S T (fg 0) tau
              (lVelocity (I := I) (fun u : Real => fg u tau) 0)) = 0 := by
        rw [hYa, hYb] at hvalue
        simpa using hvalue
      have hpoint : ∀ tau,
          (-2 * Real.sqrt tau) *
              lEulerPair S T (fg 0) tau
                (lVelocity (I := I) (fun u : Real => fg u tau) 0) =
            g tau * F tau := by
        intro tau
        rw [hcenterg, hfield tau]
        have hlin := lEulerPair_smul (I := I) S T gamma tau (g tau)
          (lVelocity (I := I) (fun u : Real => f0 u tau) 0 :
            TangentSpace I (gamma tau))
        calc
          (-2 * Real.sqrt tau) *
                lEulerPair S T gamma tau
                  (g tau • lVelocity (I := I)
                    (fun u : Real => f0 u tau) 0) =
              (-2 * Real.sqrt tau) *
                (g tau * lEulerPair S T gamma tau
                  (lVelocity (I := I) (fun u : Real => f0 u tau) 0)) :=
            congrArg (fun z : Real => (-2 * Real.sqrt tau) * z) hlin
          _ = g tau * F tau := by
            simp only [F]
            ring
      have hinterval : (∫ tau in a..b, g tau * F tau) = 0 := by
        calc
          (∫ tau in a..b, g tau * F tau) =
              ∫ tau in a..b,
                (-2 * Real.sqrt tau) *
                  lEulerPair S T (fg 0) tau
                    (lVelocity (I := I) (fun u : Real => fg u tau) 0) := by
            apply intervalIntegral.integral_congr
            intro tau _
            exact (hpoint tau).symm
          _ = 0 := hint
      have hsupp : Function.support (fun tau : Real => g tau * F tau) ⊆
          Set.Ioc a b := by
        intro tau htau
        exact Set.Ioo_subset_Ioc_self
          (hgsub (subset_tsupport g (left_ne_zero_of_mul htau)))
      have hwhole : (∫ tau, g tau * F tau ∂MeasureTheory.volume) = 0 := by
        rw [← intervalIntegral.integral_eq_integral_of_support_subset
          (μ := MeasureTheory.volume) hsupp]
        exact hinterval
      simpa only [smul_eq_mul] using hwhole
    have hae : ∀ᵐ tau ∂(MeasureTheory.volume : MeasureTheory.Measure Real),
        tau ∈ Set.Ioo a b → F tau = 0 :=
      isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (f := F) (μ := (MeasureTheory.volume : MeasureTheory.Measure Real))
        hFloc htest
    have hzero : Set.EqOn F (fun _ : Real => 0) (Set.Ioo a b) :=
      MeasureTheory.Measure.eqOn_open_of_ae_eq
        (μ := (MeasureTheory.volume : MeasureTheory.Measure Real))
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr hae)
        isOpen_Ioo hFcont continuousOn_const
    have hfield0 :
        lVelocity (I := I) (fun u : Real => f0 u tau0) 0 = Y := by
      rw [hf0central tau0]
      simpa only [lVelocity, hf0vel, V0, hbetaone, one_smul, e, c] using hw
    have hFzero : F tau0 = 0 := hzero htau0
    have hpairzero :
        (-2 * Real.sqrt tau0) * lEulerPair S T gamma tau0 Y = 0 := by
      simpa only [F, hfield0] using hFzero
    have hfactor : -2 * Real.sqrt tau0 ≠ 0 :=
      mul_ne_zero (by norm_num)
        (Real.sqrt_ne_zero'.2 (ha.trans htau0.1))
    exact (mul_eq_zero.mp hpairzero).resolve_left hfactor

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def lRegAccel
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (A : TangentSpace I x) : TangentSpace I x :=
  let g := S.base.metric (T - s ^ 2)
  (2 * s ^ 2) • gradientFun (I := I) g (S.scalar (T - s ^ 2)) x -
    (4 * s) • metricSharp (I := I) g x
      ((ricciTensor (I := I) g x A).toLinearMap)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
@[simp] theorem lRegAccel_zero
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (A : TangentSpace I x) :
    lRegAccel S T 0 x A = 0 := by
  simp [lRegAccel]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def lPhaseField
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x0 : M)
    (s : Real) (z : E × E) : E × E :=
  let x := (extChartAt I x0).symm z.1
  let A := trivFromE (I := I) x0 x z.2
  (z.2,
    -DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction
        (I := I) (S.base.metric (T - s ^ 2)) x0 z.2 z.2 z.1 +
      trivToE (I := I) x0 x (lRegAccel S T s x A))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
noncomputable def lPhaseCurve (x0 : M) (z : Real → E × E) : Real → M :=
  fun s => (extChartAt I x0).symm (z s).1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E]
  [SigmaCompactSpace M] in
noncomputable def lPhaseVel (x0 : M) (z : Real → E × E) :
    ∀ s, TangentSpace I (lPhaseCurve (I := I) x0 z s) :=
  fun s => trivFromE (I := I) x0 (lPhaseCurve (I := I) x0 z s) (z s).2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
@[simp] theorem lPhaseField_zero
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x0 : M)
    (z : E × E) :
    lPhaseField S T x0 0 z =
      DifferentialGeometry.Geometry.Riemannian.Geodesic.chartPhaseVF
        (I := I) (S.base.metric T) x0 z := by
  simp only [lPhaseField, pow_two, zero_mul, sub_zero, lRegAccel_zero,
    map_zero, add_zero,
    DifferentialGeometry.Geometry.Riemannian.Geodesic.chartPhaseVF_apply]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lPhaseField_smoothAt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x0 : M) {s : Real} {z : E × E}
    (ht : T - s ^ 2 ∈ D.regular)
    (hz : z.1 ∈ interior (extChartAt I x0).target) :
    ContDiffAt Real ∞
      (Function.uncurry (lPhaseField S T x0)) (s, z) := by
  classical
  let U : Set (Real × E) :=
    D.regular ×ˢ interior (extChartAt I x0).target
  let base : Real × (E × E) → Real × E := fun p =>
    (T - p.1 ^ 2, p.2.1)
  let christ : Real × (E × E) → E := fun p =>
    ∑ k : Fin (Module.finrank Real E),
      (∑ i : Fin (Module.finrank Real E),
        ∑ j : Fin (Module.finrank Real E),
          chartChristoffel (I := I) (S.family.metric (T - p.1 ^ 2))
              x0 i j k p.2.1 *
            chartCoord (E := E) i p.2.2 * chartCoord (E := E) j p.2.2) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k
  let gradC : Real × (E × E) → E := fun p =>
    ∑ i : Fin (Module.finrank Real E),
      (∑ j : Fin (Module.finrank Real E),
        chartInvGramOnE (I := I) (S.family.metric (T - p.1 ^ 2))
            x0 i j p.2.1 *
          (let x := (extChartAt I x0).symm p.2.1
           mvfderiv (I := I) (S.scalar (T - p.1 ^ 2)) x
             (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x))) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i
  let ricC : Real × (E × E) → E := fun p =>
    ∑ i : Fin (Module.finrank Real E),
      (∑ j : Fin (Module.finrank Real E),
        chartInvGramOnE (I := I) (S.family.metric (T - p.1 ^ 2))
            x0 i j p.2.1 *
          ∑ k : Fin (Module.finrank Real E),
            chartCoord (E := E) k p.2.2 *
              (let x := (extChartAt I x0).symm p.2.1
               S.ricciAt (T - p.1 ^ 2) x
                 (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
                   (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x)))) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i
  let rhs : Real × (E × E) → E × E := fun p =>
    (p.2.2,
      -christ p +
        ((2 * p.1 ^ 2) • gradC p - (4 * p.1) • ricC p))
  have hbase : ContDiffAt Real ∞ base (s, z) := by
    exact (contDiffAt_const.sub (contDiffAt_fst.pow 2)).prodMk
      contDiffAt_snd.fst
  have hUopen : IsOpen U := D.regular_isOpen.prod isOpen_interior
  have hbase_mem : base (s, z) ∈ U := by
    exact ⟨ht, hz⟩
  have hinv (i j : Fin (Module.finrank Real E)) :
      ContDiffAt Real ∞
        (fun p : Real × (E × E) =>
          chartInvGramOnE (I := I) (S.family.metric (T - p.1 ^ 2))
            x0 i j p.2.1) (s, z) := by
    have h := (MetricFamilySmoothOn.chartInvGramOnE_contDiffOn
      (I := I) (g_fam := S.family.metric) hS.smoothMetric
      (J := D.regular) (fun _ h => h) x0 i j).contDiffAt
        (hUopen.mem_nhds hbase_mem)
    simpa only [base, Function.comp_def] using h.comp (s, z) hbase
  have hchrist (i j k : Fin (Module.finrank Real E)) :
      ContDiffAt Real ∞
        (fun p : Real × (E × E) =>
          chartChristoffel (I := I) (S.family.metric (T - p.1 ^ 2))
            x0 i j k p.2.1) (s, z) := by
    have h := (MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn
      (I := I) (g_fam := S.family.metric) hS.smoothMetric
      (J := D.regular) (fun _ h => h) D.regular_isOpen.uniqueDiffOn
      x0 i j k).contDiffAt (hUopen.mem_nhds hbase_mem)
    simpa only [base, Function.comp_def] using h.comp (s, z) hbase
  have hcoord (i : Fin (Module.finrank Real E)) :
      ContDiffAt Real ∞
        (fun p : Real × (E × E) => chartCoord (E := E) i p.2.2)
        (s, z) := by
    simpa only [chartCoordCLM_apply, Function.comp_def] using
      ((chartCoordCLM (E := E) i).contDiff.comp
        (contDiff_snd.snd : ContDiff Real ∞
          (fun p : Real × (E × E) => p.2.2))).contDiffAt
  have hscalar (j : Fin (Module.finrank Real E)) :
      ContDiffAt Real ∞
        (fun p : Real × (E × E) =>
          let x := (extChartAt I x0).symm p.2.1
          mvfderiv (I := I) (S.scalar (T - p.1 ^ 2)) x
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x)) (s, z) := by
    have h := (chartScalarDeriv (I := I) S hS x0 j).contDiffAt
      (hUopen.mem_nhds hbase_mem)
    simpa only [base, Function.comp_def] using h.comp (s, z) hbase
  have hric (k j : Fin (Module.finrank Real E)) :
      ContDiffAt Real ∞
        (fun p : Real × (E × E) =>
          let x := (extChartAt I x0).symm p.2.1
          S.ricciAt (T - p.1 ^ 2) x
            (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x))) (s, z) := by
    have h := (chartRicci_joint (I := I) S hS x0 k j).contDiffAt
      (hUopen.mem_nhds hbase_mem)
    simpa only [base, Function.comp_def] using h.comp (s, z) hbase
  have hchristC : ContDiffAt Real ∞ christ (s, z) := by
    refine ContDiffAt.sum fun k _ => ?_
    refine (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
      ((hchrist i j k).mul (hcoord i)).mul (hcoord j)).smul
        contDiffAt_const
  have hgradC : ContDiffAt Real ∞ gradC (s, z) := by
    refine ContDiffAt.sum fun i _ => ?_
    exact (ContDiffAt.sum fun j _ => (hinv i j).mul (hscalar j)).smul
      contDiffAt_const
  have hricC : ContDiffAt Real ∞ ricC (s, z) := by
    refine ContDiffAt.sum fun i _ => ?_
    refine (ContDiffAt.sum fun j _ => (hinv i j).mul
      (ContDiffAt.sum fun k _ => (hcoord k).mul (hric k j))).smul
        contDiffAt_const
  have hrhs : ContDiffAt Real ∞ rhs (s, z) := by
    have hs : ContDiffAt Real ∞ (fun p : Real × (E × E) => p.1) (s, z) :=
      contDiffAt_fst
    have hforce : ContDiffAt Real ∞
        (fun p : Real × (E × E) =>
          (2 * p.1 ^ 2) • gradC p - (4 * p.1) • ricC p) (s, z) :=
      (((contDiffAt_const (c := (2 : Real))).mul (hs.pow 2)).smul hgradC).sub
        (((contDiffAt_const (c := (4 : Real))).mul hs).smul hricC)
    exact contDiffAt_snd.snd.prodMk (hchristC.neg.add hforce)
  refine hrhs.congr_of_eventuallyEq ?_
  have hnear : ∀ᶠ p in 𝓝 (s, z), base p ∈ U :=
    hbase.continuousAt.eventually (hUopen.mem_nhds hbase_mem)
  filter_upwards [hnear] with p hp
  let t := T - p.1 ^ 2
  let x := (extChartAt I x0).symm p.2.1
  let g := S.family.metric t
  let A := trivFromE (I := I) x0 x p.2.2
  have hxtarget : p.2.1 ∈ (extChartAt I x0).target := interior_subset hp.2
  have hxsrc : x ∈ (chartAt H x0).source := by
    have hxext : x ∈ (extChartAt I x0).source :=
      (extChartAt I x0).map_target hxtarget
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hxext
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hchrist_eq :
      chartChristoffelContraction (I := I) g x0 p.2.2 p.2.2 p.2.1 =
        christ p := by
    rfl
  have hgrad_eq :
      trivToE (I := I) x0 x
          (gradientFun (I := I) g (S.scalar t) x) = gradC p := by
    let cv : ∀ y : M, TangentSpace I y →ₗ[Real] Real := fun y =>
      (mfderiv I 𝓘(Real, Real) (S.scalar t) y).toLinearMap
    have hsharp := trivToE_metricSharp (I := I) g x0 cv hxbase
    change trivToE (I := I) x0 x (metricSharp (I := I) g x (cv x)) = _
    rw [hsharp]
    simp only [gradC, cv, t, g, x, chartInvGramOnE_def,
      DifferentialGeometry.mvfderiv_real_eq_mfderiv]
    refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
  have hric_comp (j : Fin (Module.finrank Real E)) :
      ricciTensor (I := I) g x A
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x) =
        ∑ k : Fin (Module.finrank Real E),
          chartCoord (E := E) k p.2.2 *
            S.ricciAt t x
              (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x)) := by
    have hA : A = ∑ k : Fin (Module.finrank Real E),
        chartCoord (E := E) k p.2.2 •
          DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x := by
      have hcoordA : trivToE (I := I) x0 x A = p.2.2 := by
        exact trivToE_trivFromE (I := I) x0 hxbase p.2.2
      have hrec := chartBasisVecFiber_recompose (I := I) x0 hxbase A
      rw [hcoordA] at hrec
      simpa only [chartCoord_def] using hrec
    rw [hA, map_sum, sum_apply]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul, smul_apply, smul_eq_mul]
    congr 1
    exact (metricRicciAt_apply_eq_ricciTensor (I := I) g x
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x)).symm
  have hric_eq :
      trivToE (I := I) x0 x
          (metricSharp (I := I) g x
            ((ricciTensor (I := I) g x A).toLinearMap)) = ricC p := by
    let cv : ∀ y : M, TangentSpace I y →ₗ[Real] Real := fun y =>
      (ricciTensor (I := I) g y
        (trivFromE (I := I) x0 y p.2.2)).toLinearMap
    have hsharp := trivToE_metricSharp (I := I) g x0 cv hxbase
    change trivToE (I := I) x0 x (metricSharp (I := I) g x (cv x)) = _
    rw [hsharp]
    simp only [ricC, cv, t, g, x, chartInvGramOnE_def]
    refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j _
    change chartInvGramMatrix (I := I) g x0 x i j *
        ricciTensor (I := I) g x A
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x) =
      chartInvGramMatrix (I := I) g x0 x i j *
        ∑ k : Fin (Module.finrank Real E),
          chartCoord (E := E) k p.2.2 *
            S.ricciAt t x
              (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 k x)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x0 j x))
    rw [hric_comp j]
  have haccel_eq :
      trivToE (I := I) x0 x (lRegAccel S T p.1 x A) =
        (2 * p.1 ^ 2) • gradC p - (4 * p.1) • ricC p := by
    change trivToE (I := I) x0 x
      ((2 * p.1 ^ 2) • gradientFun (I := I) g (S.scalar t) x -
        (4 * p.1) • metricSharp (I := I) g x
          ((ricciTensor (I := I) g x A).toLinearMap)) = _
    rw [map_sub, map_smul, map_smul, hgrad_eq, hric_eq]
  change lPhaseField S T x0 p.1 p.2 = rhs p
  simp only [lPhaseField, rhs]
  apply Prod.ext
  · rfl
  change
    -chartChristoffelContraction (I := I)
        (S.base.metric (T - p.1 ^ 2)) x0 p.2.2 p.2.2 p.2.1 +
        trivToE (I := I) x0 x (lRegAccel S T p.1 x A) =
      -christ p + ((2 * p.1 ^ 2) • gradC p - (4 * p.1) • ricC p)
  rw [show chartChristoffelContraction (I := I)
      (S.base.metric (T - p.1 ^ 2)) x0 p.2.2 p.2.2 p.2.1 = christ p by
        simpa only [SolutionOn.family_metric, t, g] using hchrist_eq]
  rw [haccel_eq]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lPhaseCurve
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x0 : M) (z0 : E × E)
    (hT : T ∈ D.regular)
    (hz : z0.1 ∈ interior (extChartAt I x0).target) :
    ∃ c : Real → Real × (E × E),
      c 0 = (0, z0) ∧
        IsMIntegralCurveAt (I := (modelWithCornersSelf Real (Real × (E × E)))) c
          (fun p : Real × (E × E) =>
            (tangentSpaceModelContinuousLinearEquiv
              (I := modelWithCornersSelf Real (Real × (E × E))) p).symm
              ((1 : Real), lPhaseField S T x0 p.1 p.2)) 0 := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let vf0 : Real × (E × E) → Real × (E × E) := fun p =>
    ((1 : Real), lPhaseField S T x0 p.1 p.2)
  let vf : (p : Real × (E × E)) →
      TangentSpace (modelWithCornersSelf Real (Real × (E × E))) p := fun p =>
    (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real (Real × (E × E))) p).symm (vf0 p)
  have hphase : ContDiffAt Real 1
      (Function.uncurry (lPhaseField S T x0)) (0, z0) := by
    exact (lPhaseField_smoothAt S hS T x0
      (by simpa using hT) hz).of_le (by norm_num)
  have hvf : ContDiffAt Real 1 vf0 (0, z0) := by
    exact contDiffAt_const.prodMk hphase
  have hsection :
      ContMDiffAt (modelWithCornersSelf Real (Real × (E × E)))
        ((modelWithCornersSelf Real (Real × (E × E))).prod (modelWithCornersSelf Real (Real × (E × E)))) 1
        (fun p : Real × (E × E) =>
          (⟨p, vf p⟩ : TangentBundle (modelWithCornersSelf Real (Real × (E × E)))
            (Real × (E × E)))) (0, z0) := by
    rw [Bundle.contMDiffAt_section]
    simpa only [vf, tangentSpaceModelContinuousLinearEquiv_symm_apply,
      trivializationAt_model_space_apply] using hvf.contMDiffAt
  exact exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (v := vf) (x₀ := (0, z0)) (t₀ := (0 : Real)) hsection

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lPhaseSol
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x0 : M) (z0 : E × E)
    (hT : T ∈ D.regular)
    (hz : z0.1 ∈ interior (extChartAt I x0).target) :
    ∃ (epsilon : Real) (_ : 0 < epsilon) (z : Real → E × E),
      z 0 = z0 ∧
        ∀ s ∈ Set.Ioo (-epsilon) epsilon,
          HasDerivAt z (lPhaseField S T x0 s (z s)) s := by
  let X : Real → ∀ z : E × E,
      TangentSpace (modelWithCornersSelf Real (E × E)) z := fun s z =>
    (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real (E × E)) z).symm
      (lPhaseField S T x0 s z)
  obtain ⟨c, hc0, hcurve⟩ := exists_lPhaseCurve S hS T x0 z0 hT hz
  rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at hcurve
  obtain ⟨U, hU, hcurveU⟩ := hcurve
  have hcurveX : ∀ s ∈ U,
      HasMFDerivAt (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real (E × E))) c s
        ((1 : Real →L[Real] Real).smulRight
          (DifferentialGeometry.Analysis.ODE.autonomizedFlowVF X (c s))) := by
    intro s hs
    refine (hcurveU s hs).congr_mfderiv ?_
    congr 1
  rw [Metric.mem_nhds_iff] at hU
  obtain ⟨epsilon, hepsilon, hball⟩ := hU
  refine ⟨epsilon, hepsilon, fun s => (c s).2, ?_, ?_⟩
  · change (c 0).2 = z0
    rw [hc0]
  · intro s hs
    have hsU : s ∈ U := by
      apply hball
      rw [Real.ball_eq_Ioo]
      constructor
      · simpa using hs.1
      · simpa using hs.2
    have hcderiv :
        HasMFDerivAt 𝓘(Real, Real)
          ((modelWithCornersSelf Real Real).prod (modelWithCornersSelf Real (E × E))) c s
          ((1 : Real →L[Real] Real).smulRight
            (DifferentialGeometry.Analysis.ODE.autonomizedFlowVF X (c s))) := by
      exact hcurveX s hsU
    have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
      constructor <;> simpa using hepsilon
    have htime : ∀ r ∈ Set.Ioo (-epsilon) epsilon, (c r).1 = r := by
      apply DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
        (fun r => (c r).1) hzero
      · intro r hr
        have hrU : r ∈ U := by
          apply hball
          rw [Real.ball_eq_Ioo]
          constructor
          · simpa using hr.1
          · simpa using hr.2
        apply DifferentialGeometry.Analysis.ODE.autonomizedFlow_fst_hasDerivAt
          (I := (modelWithCornersSelf Real (E × E))) X c r
        exact hcurveX r hrU
      · rw [hc0]
    have hsnd :=
      DifferentialGeometry.Analysis.ODE.autonomizedFlow_snd_hasMFDerivAt
        (I := (modelWithCornersSelf Real (E × E))) X c s hcderiv
    rw [htime s hs] at hsnd
    have hsnd' := hasMFDerivAt_iff_hasFDerivAt.mp hsnd
    change HasFDerivAt (fun s => (c s).2)
      (ContinuousLinearMap.toSpanSingleton Real
        (lPhaseField S T x0 s (c s).2)) s
    refine hsnd'.congr_fderiv ?_
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
    congr 1

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lPhaseSol_unique_at
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x0 : M) (s0 : Real) (z0 : E × E)
    (hT : T - s0 ^ 2 ∈ D.regular)
    (hz : z0.1 ∈ interior (extChartAt I x0).target)
    {z z' : Real → E × E}
    (hz0 : z s0 = z0) (hz0' : z' s0 = z0)
    (hzsol : ∀ᶠ s in 𝓝 s0,
      HasDerivAt z (lPhaseField S T x0 s (z s)) s)
    (hzsol' : ∀ᶠ s in 𝓝 s0,
      HasDerivAt z' (lPhaseField S T x0 s (z' s)) s) :
    z =ᶠ[𝓝 s0] z' := by
  let vf0 : Real × (E × E) → Real × (E × E) := fun p =>
    ((1 : Real), lPhaseField S T x0 p.1 p.2)
  let vf : (p : Real × (E × E)) →
      TangentSpace (modelWithCornersSelf Real (Real × (E × E))) p := fun p =>
    (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real (Real × (E × E))) p).symm (vf0 p)
  have hphase : ContDiffAt Real 1
      (Function.uncurry (lPhaseField S T x0)) (s0, z0) := by
    exact (lPhaseField_smoothAt S hS T x0
      hT hz).of_le (by norm_num)
  have hvf : ContDiffAt Real 1 vf0 (s0, z0) := by
    exact contDiffAt_const.prodMk hphase
  have hsection :
      ContMDiffAt (modelWithCornersSelf Real (Real × (E × E)))
        ((modelWithCornersSelf Real (Real × (E × E))).prod (modelWithCornersSelf Real (Real × (E × E)))) 1
        (fun p : Real × (E × E) =>
          (⟨p, vf p⟩ : TangentBundle (modelWithCornersSelf Real (Real × (E × E)))
        (Real × (E × E)))) (s0, z0) := by
    rw [Bundle.contMDiffAt_section]
    simpa only [vf, tangentSpaceModelContinuousLinearEquiv_symm_apply,
      trivializationAt_model_space_apply] using hvf.contMDiffAt
  let c : Real → Real × (E × E) := fun s => (s, z s)
  let c' : Real → Real × (E × E) := fun s => (s, z' s)
  have hc : IsMIntegralCurveAt
      (I := (modelWithCornersSelf Real (Real × (E × E)))) c vf s0 := by
    filter_upwards [hzsol] with s hs
    have h := (hasDerivAt_id s).prodMk hs |>.hasFDerivAt.hasMFDerivAt
    refine h.congr_mfderiv ?_
    rw [← ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
    congr 1
  have hc' : IsMIntegralCurveAt
      (I := (modelWithCornersSelf Real (Real × (E × E)))) c' vf s0 := by
    filter_upwards [hzsol'] with s hs
    have h := (hasDerivAt_id s).prodMk hs |>.hasFDerivAt.hasMFDerivAt
    refine h.congr_mfderiv ?_
    rw [← ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
    congr 1
  have hc0 : c s0 = c' s0 := by
    simp only [c, c', hz0, hz0']
  have hcseed : c s0 = (s0, z0) := by
    simp only [c, hz0]
  have hsection_c :
      ContMDiffAt (modelWithCornersSelf Real (Real × (E × E)))
        ((modelWithCornersSelf Real (Real × (E × E))).prod (modelWithCornersSelf Real (Real × (E × E)))) 1
        (fun p : Real × (E × E) =>
          (⟨p, vf p⟩ : TangentBundle (modelWithCornersSelf Real (Real × (E × E)))
        (Real × (E × E)))) (c s0) := by
    rw [hcseed]
    exact hsection
  have heq :=
    isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      (I := (modelWithCornersSelf Real (Real × (E × E)))) hsection_c hc hc' hc0
  filter_upwards [heq] with s hs
  exact congrArg Prod.snd hs

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lPhaseSol_unique
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x0 : M) (z0 : E × E)
    (hT : T ∈ D.regular)
    (hz : z0.1 ∈ interior (extChartAt I x0).target)
    {z z' : Real → E × E}
    (hz0 : z 0 = z0) (hz0' : z' 0 = z0)
    (hzsol : ∀ᶠ s in 𝓝 (0 : Real),
      HasDerivAt z (lPhaseField S T x0 s (z s)) s)
    (hzsol' : ∀ᶠ s in 𝓝 (0 : Real),
      HasDerivAt z' (lPhaseField S T x0 s (z' s)) s) :
    z =ᶠ[𝓝 (0 : Real)] z' := by
  exact lPhaseSol_unique_at S hS T x0 0 z0 (by simpa using hT) hz
    hz0 hz0' hzsol hzsol'

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [FiniteDimensional Real E] [T2Space M] [SigmaCompactSpace M] in
theorem lPhaseCurve_mdiff
    (x0 : M) (z : Real → E × E) (s : Real)
    (hz : DifferentiableAt Real (fun r : Real => (z r).1) s)
    (hpos : (z s).1 ∈ interior (extChartAt I x0).target) :
    MDifferentiableAt 𝓘(Real, Real) I
      (lPhaseCurve (I := I) x0 z) s := by
  have hsymm :=
    (contMDiffOn_extChartAt_symm (I := I) (n := (1 : Nat)) x0).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x0).mem_nhds (interior_subset hpos))
  exact (hsymm.mdifferentiableAt (by norm_num)).comp s
    (mdifferentiableAt_iff_differentiableAt.mpr hz)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [FiniteDimensional Real E] [T2Space M] [SigmaCompactSpace M] in
theorem lPhase_velocity
    (x0 : M) (z : Real → E × E) (s : Real)
    (hz : HasDerivAt (fun r : Real => (z r).1) (z s).2 s)
    (hpos : (z s).1 ∈ interior (extChartAt I x0).target) :
    lVelocity (I := I) (lPhaseCurve (I := I) x0 z) s =
      lPhaseVel (I := I) x0 z s := by
  let alpha : Real → M := lPhaseCurve (I := I) x0 z
  let q : Real → E := fun r => (z r).1
  have hq : HasDerivAt q (z s).2 s := by
    simpa only [q] using hz
  have htarget : ∀ᶠ r in 𝓝 s, q r ∈ (extChartAt I x0).target :=
    hq.continuousAt.eventually
      ((isOpen_extChartAt_target (I := I) x0).mem_nhds (interior_subset hpos))
  have hsource : alpha s ∈ (chartAt H x0).source := by
    have hext : alpha s ∈ (extChartAt I x0).source := by
      exact (extChartAt I x0).map_target (interior_subset hpos)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hext
  have halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s := by
    simpa only [alpha] using
      lPhaseCurve_mdiff (I := I) x0 z s hq.differentiableAt hpos
  have hbridge :=
    DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
      (I := I) (M := M) halpha x0 hsource
  change ((mfderiv 𝓘(Real, Real) I alpha s : Real →L[Real] _) (1 : Real) : E) = _
  rw [hbridge]
  change trivFromE (I := I) x0 (alpha s)
      (fderiv Real ((extChartAt I x0) ∘ alpha) s (1 : Real)) =
    trivFromE (I := I) x0 (alpha s) (z s).2
  congr 1
  have heq : (extChartAt I x0) ∘ alpha =ᶠ[𝓝 s] q := by
    filter_upwards [htarget] with r hr
    simp only [Function.comp_apply, alpha, lPhaseCurve, q]
    exact (extChartAt I x0).right_inv hr
  rw [fderiv_apply_one_eq_deriv, heq.deriv_eq, hq.deriv]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [FiniteDimensional Real E] [T2Space M] [SigmaCompactSpace M] in
theorem lPhaseVel_diff
    (x0 : M) (z : Real → E × E) (s : Real)
    (hq : DifferentiableAt Real (fun r : Real => (z r).1) s)
    (hv : DifferentiableAt Real (fun r : Real => (z r).2) s)
    (hpos : (z s).1 ∈ interior (extChartAt I x0).target) :
    DifferentiableAt Real
      (chartRepAt (I := I) (lPhaseCurve (I := I) x0 z)
        (lPhaseVel (I := I) x0 z) s) s := by
  let alpha : Real → M := lPhaseCurve (I := I) x0 z
  let A : ∀ r, TangentSpace I (alpha r) := lPhaseVel (I := I) x0 z
  let q : Real → E := fun r => (z r).1
  let v : Real → E := fun r => (z r).2
  have htarget : ∀ᶠ r in 𝓝 s, q r ∈ (extChartAt I x0).target :=
    hq.continuousAt.eventually
      ((isOpen_extChartAt_target (I := I) x0).mem_nhds (interior_subset hpos))
  have hsource : alpha s ∈ (chartAt H x0).source := by
    have hext : alpha s ∈ (extChartAt I x0).source := by
      exact (extChartAt I x0).map_target (interior_subset hpos)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hext
  have halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s := by
    simpa only [alpha] using lPhaseCurve_mdiff (I := I) x0 z s hq hpos
  have hrep_eq :
      chartRepAtBase (I := I) x0 alpha A =ᶠ[𝓝 s] v := by
    filter_upwards [htarget] with r hr
    have hrsrc : alpha r ∈ (chartAt H x0).source := by
      have hrext : alpha r ∈ (extChartAt I x0).source := by
        exact (extChartAt I x0).map_target hr
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hrext
    have hrbase :
        alpha r ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hrsrc
    simp only [chartRepAtBase_apply, A, lPhaseVel, v]
    exact trivToE_trivFromE (I := I) x0 hrbase (z r).2
  have hrep_diff :
      DifferentiableAt Real (chartRepAtBase (I := I) x0 alpha A) s :=
    hv.congr_of_eventuallyEq hrep_eq
  simpa only [alpha, A] using
    chartRep_diff_base (I := I) alpha A s x0 halpha hsource hrep_diff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lPhase_accel
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (x0 : M) (z : Real → E × E) (s : Real)
    (hz : HasDerivAt z (lPhaseField S T x0 s (z s)) s)
    (hpos : (z s).1 ∈ interior (extChartAt I x0).target) :
    covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
        (lPhaseCurve (I := I) x0 z) (lPhaseVel (I := I) x0 z) s =
      lRegAccel S T s (lPhaseCurve (I := I) x0 z s)
        (lPhaseVel (I := I) x0 z s) := by
  let alpha : Real → M := lPhaseCurve (I := I) x0 z
  let A : ∀ r, TangentSpace I (alpha r) := lPhaseVel (I := I) x0 z
  let q : Real → E := fun r => (z r).1
  let v : Real → E := fun r => (z r).2
  let g := S.base.metric (T - s ^ 2)
  have hq : HasDerivAt q (z s).2 s := by
    have h := hasFDerivAt_fst.comp_hasDerivAt s hz
    simpa [q, lPhaseField, Function.comp_def] using h
  have hv : HasDerivAt v (lPhaseField S T x0 s (z s)).2 s := by
    simpa [v, Function.comp_def] using hasFDerivAt_snd.comp_hasDerivAt s hz
  have htarget : ∀ᶠ r in 𝓝 s, q r ∈ (extChartAt I x0).target :=
    hq.continuousAt.eventually
      ((isOpen_extChartAt_target (I := I) x0).mem_nhds (interior_subset hpos))
  have hsource : alpha s ∈ (chartAt H x0).source := by
    have hext : alpha s ∈ (extChartAt I x0).source := by
      exact (extChartAt I x0).map_target (interior_subset hpos)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hext
  have hbase :
      alpha s ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsource
  have halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s := by
    have hsymm :=
      (contMDiffOn_extChartAt_symm (I := I) (n := (1 : Nat)) x0).contMDiffAt
        ((isOpen_extChartAt_target (I := I) x0).mem_nhds (interior_subset hpos))
    exact (hsymm.mdifferentiableAt (by norm_num)).comp s
      (mdifferentiableAt_iff_differentiableAt.mpr hq.differentiableAt)
  have hcurve_eq : chartCurve (I := I) x0 alpha =ᶠ[𝓝 s] q := by
    filter_upwards [htarget] with r hr
    simp only [chartCurve, alpha, lPhaseCurve, q]
    exact (extChartAt I x0).right_inv hr
  have hrep_eq :
      chartRepAtBase (I := I) x0 alpha A =ᶠ[𝓝 s] v := by
    filter_upwards [htarget] with r hr
    have hrsrc : alpha r ∈ (chartAt H x0).source := by
      have hrext : alpha r ∈ (extChartAt I x0).source := by
        exact (extChartAt I x0).map_target hr
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hrext
    have hrbase :
        alpha r ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hrsrc
    simp only [chartRepAtBase_apply, A, lPhaseVel, v]
    exact trivToE_trivFromE (I := I) x0 hrbase (z r).2
  have hrep_diff :
      DifferentiableAt Real (chartRepAtBase (I := I) x0 alpha A) s :=
    hv.differentiableAt.congr_of_eventuallyEq hrep_eq
  have hA_diff :
      DifferentiableAt Real (chartRepAt (I := I) alpha A s) s :=
    by
      simpa only [alpha, A] using lPhaseVel_diff (I := I) x0 z s
        hq.differentiableAt hv.differentiableAt hpos
  have hcurve_deriv :
      deriv (chartCurve (I := I) x0 alpha) s = (z s).2 := by
    rw [hcurve_eq.deriv_eq, hq.deriv]
  have hrep_deriv :
      deriv (chartRepAtBase (I := I) x0 alpha A) s =
        (lPhaseField S T x0 s (z s)).2 := by
    rw [hrep_eq.deriv_eq, hv.deriv]
  have hcurve_s : chartCurve (I := I) x0 alpha s = (z s).1 :=
    hcurve_eq.eq_of_nhds
  have hrep_s : chartRepAtBase (I := I) x0 alpha A s = (z s).2 :=
    hrep_eq.eq_of_nhds
  have hchart :
      chartCovDerivAlong (I := I) g x0 alpha
          (chartRepAtBase (I := I) x0 alpha A) s =
        trivToE (I := I) x0 (alpha s)
          (lRegAccel S T s (alpha s) (A s)) := by
    rw [chartCovDerivAlong_def, hrep_deriv, hcurve_deriv, hrep_s, hcurve_s]
    simp only [lPhaseField, alpha, A, lPhaseCurve, lPhaseVel, g]
    abel
  have hinv :=
    covDeriv_chartAt (I := I) g alpha A s x0 halpha hsource hA_diff
  calc
    covDerivAlong (I := I) g alpha A s =
        trivFromE (I := I) x0 (alpha s)
          (chartCovDerivAlong (I := I) g x0 alpha
            (chartRepAtBase (I := I) x0 alpha A) s) := by
              exact hinv.symm
    _ = trivFromE (I := I) x0 (alpha s)
          (trivToE (I := I) x0 (alpha s)
            (lRegAccel S T s (alpha s) (A s))) := by rw [hchart]
    _ = lRegAccel S T s (alpha s) (A s) :=
      trivFromE_trivToE (I := I) x0 hbase _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_phase
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (x0 : M) (gamma : Real → M) (s : Real)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma s)
    (hsrc : gamma s ∈ (chartAt H x0).source)
    (hvel : DifferentiableAt Real
      (chartRepAt (I := I) gamma
        (fun r : Real => lVelocity (I := I) gamma r) s) s)
    (hacc : covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
        (fun r : Real => lVelocity (I := I) gamma r) s =
      lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s)) :
    HasDerivAt
      (fun r : Real =>
        (chartCurve (I := I) x0 gamma r,
          chartRepAtBase (I := I) x0 gamma
            (fun u : Real => lVelocity (I := I) gamma u) r))
      (lPhaseField S T x0 s
        (chartCurve (I := I) x0 gamma s,
          chartRepAtBase (I := I) x0 gamma
            (fun u : Real => lVelocity (I := I) gamma u) s)) s := by
  let X : ∀ r, TangentSpace I (gamma r) :=
    fun r => lVelocity (I := I) gamma r
  let q : Real → E := chartCurve (I := I) x0 gamma
  let v : Real → E := chartRepAtBase (I := I) x0 gamma X
  let g := S.base.metric (T - s ^ 2)
  have hqdiff : DifferentiableAt Real q s := by
    have hcomp := (mdifferentiableAt_extChartAt (I := I) hsrc).comp s hgamma
    rw [mdifferentiableAt_iff_differentiableAt] at hcomp
    change DifferentiableAt Real ((extChartAt I x0) ∘ gamma) s
    exact hcomp
  have hvdiff : DifferentiableAt Real v s := by
    simpa only [v, X] using
      chartRep_base_diff (I := I) gamma X s x0 hgamma hsrc hvel
  have hqcoord : deriv q s = v s := by
    have hcoord :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) hgamma x0 hsrc
    rw [fderiv_apply_one_eq_deriv] at hcoord
    change deriv ((extChartAt I x0) ∘ gamma) s =
      trivToE (I := I) x0 (gamma s) (lVelocity (I := I) gamma s)
    exact hcoord.symm
  have hbase :
      gamma s ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsrc
  have hcovcoord :
      chartCovDerivAlong (I := I) g x0 gamma v s =
        trivToE (I := I) x0 (gamma s)
          (lRegAccel S T s (gamma s) (X s)) := by
    have hinv := covDeriv_chartAt (I := I) g gamma X s x0
      hgamma hsrc hvel
    have hcoord := congrArg
      (fun A : TangentSpace I (gamma s) => trivToE (I := I) x0 (gamma s) A)
      hinv
    change trivToE (I := I) x0 (gamma s)
        (trivFromE (I := I) x0 (gamma s)
          (chartCovDerivAlong (I := I) g x0 gamma
            (chartRepAtBase (I := I) x0 gamma X) s)) =
      trivToE (I := I) x0 (gamma s)
        (covDerivAlong (I := I) g gamma X s) at hcoord
    rw [trivToE_trivFromE (I := I) x0 hbase] at hcoord
    rw [hacc] at hcoord
    simpa only [v, X] using hcoord
  have hvcoord : deriv v s =
      -chartChristoffelContraction (I := I) g x0 (v s) (v s) (q s) +
        trivToE (I := I) x0 (gamma s)
          (lRegAccel S T s (gamma s) (X s)) := by
    rw [chartCovDerivAlong_def, hqcoord] at hcovcoord
    rw [← hcovcoord]
    abel
  have hqderiv : HasDerivAt q (v s) s :=
    hqdiff.hasDerivAt.congr_deriv hqcoord
  have hvderiv : HasDerivAt v
      (-chartChristoffelContraction (I := I) g x0 (v s) (v s) (q s) +
        trivToE (I := I) x0 (gamma s)
          (lRegAccel S T s (gamma s) (X s))) s :=
    hvdiff.hasDerivAt.congr_deriv hvcoord
  have hleft : (extChartAt I x0).symm (q s) = gamma s := by
    simpa only [q, chartCurve] using (extChartAt I x0).left_inv
      (by rwa [extChartAt_source_eq_chartAt_source (I := I)])
  have hround : trivFromE (I := I) x0 (gamma s) (v s) = X s := by
    simpa only [v, chartRepAtBase_apply] using
      trivFromE_trivToE (I := I) x0 hbase (X s)
  have hpair := hqderiv.prodMk hvderiv
  have hphase :
      (v s,
        -chartChristoffelContraction (I := I) g x0 (v s) (v s) (q s) +
          trivToE (I := I) x0 (gamma s)
            (lRegAccel S T s (gamma s) (X s))) =
        lPhaseField S T x0 s (q s, v s) := by
    simp only [lPhaseField]
    rw [hleft, hround]
  simpa only [q, v, X] using hpair.congr_deriv hphase

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lRegCurve
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x)
    (hT : T ∈ D.regular) :
    ∃ (epsilon : Real) (_ : 0 < epsilon) (alpha : Real → M),
      alpha 0 = x ∧
        lVelocity (I := I) alpha 0 = 2 • Z ∧
        ∀ s ∈ Set.Ioo (-epsilon) epsilon,
          T - s ^ 2 ∈ D.regular ∧
            MDifferentiableAt 𝓘(Real, Real) I alpha s ∧
            DifferentiableAt Real
              (chartRepAt (I := I) alpha
                (fun r : Real => lVelocity (I := I) alpha r) s) s ∧
            covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
                (fun r : Real => lVelocity (I := I) alpha r) s =
              lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s) := by
  let z0 : E × E :=
    (extChartAt I x x, trivToE (I := I) x x (2 • Z))
  have hz0pos : z0.1 ∈ interior (extChartAt I x).target := by
    apply mem_interior_iff_mem_nhds.mpr
    simpa only [z0] using extChartAt_target_mem_nhds (I := I) x
  obtain ⟨epsilon0, hepsilon0, z, hz0, hsol⟩ :=
    exists_lPhaseSol S hS T x z0 hT hz0pos
  have hzero0 : (0 : Real) ∈ Set.Ioo (-epsilon0) epsilon0 := by
    constructor <;> simpa using hepsilon0
  have hzder0 := hsol 0 hzero0
  have hpos0 : (z 0).1 ∈ interior (extChartAt I x).target := by
    rw [hz0]
    exact hz0pos
  have hinterval : ∀ᶠ s in 𝓝 (0 : Real),
      s ∈ Set.Ioo (-epsilon0) epsilon0 :=
    isOpen_Ioo.mem_nhds hzero0
  have hpos : ∀ᶠ s in 𝓝 (0 : Real),
      (z s).1 ∈ interior (extChartAt I x).target :=
    hzder0.continuousAt.fst.eventually (isOpen_interior.mem_nhds hpos0)
  have htime : ContinuousAt (fun s : Real => T - s ^ 2) 0 :=
    continuousAt_const.sub (continuousAt_id.pow 2)
  have hreg0 : T - (0 : Real) ^ 2 ∈ D.regular := by
    simpa using hT
  have hreg : ∀ᶠ s in 𝓝 (0 : Real), T - s ^ 2 ∈ D.regular :=
    htime.eventually (D.regular_isOpen.mem_nhds hreg0)
  have hgood : ∀ᶠ s in 𝓝 (0 : Real),
      s ∈ Set.Ioo (-epsilon0) epsilon0 ∧
        (z s).1 ∈ interior (extChartAt I x).target ∧
        T - s ^ 2 ∈ D.regular := by
    filter_upwards [hinterval, hpos, hreg] with s hs hsp hsr
    exact ⟨hs, hsp, hsr⟩
  obtain ⟨epsilon, hepsilon, hsmall⟩ :=
    Metric.eventually_nhds_iff.mp hgood
  let alpha : Real → M := lPhaseCurve (I := I) x z
  let A : ∀ s, TangentSpace I (alpha s) := lPhaseVel (I := I) x z
  have hdata : ∀ s ∈ Set.Ioo (-epsilon) epsilon,
      s ∈ Set.Ioo (-epsilon0) epsilon0 ∧
        (z s).1 ∈ interior (extChartAt I x).target ∧
        T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hsmall
    simpa only [Real.dist_eq, sub_zero] using (abs_lt.mpr hs)
  have hvel : Set.EqOn (fun s => lVelocity (I := I) alpha s) A
      (Set.Ioo (-epsilon) epsilon) := by
    intro s hs
    have hsdata := hdata s hs
    have hzs := hsol s hsdata.1
    have hq : HasDerivAt (fun r : Real => (z r).1) (z s).2 s := by
      have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
      simpa [lPhaseField, Function.comp_def] using h
    exact lPhase_velocity (I := I) x z s hq hsdata.2.1
  have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
    constructor <;> simpa using hepsilon
  have halpha0 : alpha 0 = x := by
    simp only [alpha, lPhaseCurve, hz0, z0]
    exact (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  refine ⟨epsilon, hepsilon, alpha, halpha0, ?_, ?_⟩
  · have hvel0 : lVelocity (I := I) alpha 0 = A 0 := hvel hzero
    rw [hvel0]
    change trivFromE (I := I) x (alpha 0) (z 0).2 = 2 • Z
    rw [halpha0, hz0]
    simp only [z0]
    exact trivFromE_trivToE (I := I) x
      (FiberBundle.mem_baseSet_trivializationAt' x) (2 • Z)
  · intro s hs
    have hsdata := hdata s hs
    have hzs := hsol s hsdata.1
    have hq : HasDerivAt (fun r : Real => (z r).1) (z s).2 s := by
      have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
      simpa [lPhaseField, Function.comp_def] using h
    have hv : HasDerivAt (fun r : Real => (z r).2)
        (lPhaseField S T x s (z s)).2 s := by
      simpa [Function.comp_def] using
        hasFDerivAt_snd.comp_hasDerivAt s hzs
    have hfield : (fun r => lVelocity (I := I) alpha r) =ᶠ[𝓝 s] A :=
      hvel.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
    have halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s := by
      simpa only [alpha] using
        lPhaseCurve_mdiff (I := I) x z s hq.differentiableAt hsdata.2.1
    have hAdiff : DifferentiableAt Real
        (chartRepAt (I := I) alpha A s) s := by
      simpa only [alpha, A] using lPhaseVel_diff (I := I) x z s
        hq.differentiableAt hv.differentiableAt hsdata.2.1
    have hveldiff : DifferentiableAt Real
        (chartRepAt (I := I) alpha
          (fun r : Real => lVelocity (I := I) alpha r) s) s :=
      hAdiff.congr_of_eventuallyEq
        (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) alpha hfield)
    refine ⟨hsdata.2.2, halpha, hveldiff, ?_⟩
    calc
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
          (fun r : Real => lVelocity (I := I) alpha r) s =
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha A s :=
          covDerivAlong_congr_of_eventuallyEq
            (I := I) (S.base.metric (T - s ^ 2)) alpha hfield
      _ = lRegAccel S T s (alpha s) (A s) := by
        simpa only [alpha, A] using
          lPhase_accel S T x z s hzs hsdata.2.1
      _ = lRegAccel S T s (alpha s)
          (lVelocity (I := I) alpha s) := by
        rw [hfield.eq_of_nhds]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_unique_at
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T s0 : Real) (hT : T - s0 ^ 2 ∈ D.regular)
    {gamma eta : Real → M}
    (hpos0 : gamma s0 = eta s0)
    (hvel0 : lVelocity (I := I) gamma s0 = lVelocity (I := I) eta s0)
    (hgamma : ∀ᶠ s in 𝓝 s0,
      MDifferentiableAt 𝓘(Real, Real) I gamma s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun r : Real => lVelocity (I := I) gamma r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (fun r : Real => lVelocity (I := I) gamma r) s =
          lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s))
    (heta : ∀ᶠ s in 𝓝 s0,
      MDifferentiableAt 𝓘(Real, Real) I eta s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) eta
            (fun r : Real => lVelocity (I := I) eta r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) eta
            (fun r : Real => lVelocity (I := I) eta r) s =
          lRegAccel S T s (eta s) (lVelocity (I := I) eta s)) :
    gamma =ᶠ[𝓝 s0] eta := by
  let x := gamma s0
  let Xgamma : ∀ s, TangentSpace I (gamma s) :=
    fun s => lVelocity (I := I) gamma s
  let Xeta : ∀ s, TangentSpace I (eta s) :=
    fun s => lVelocity (I := I) eta s
  let z0 : E × E :=
    (extChartAt I x x, trivToE (I := I) x x (Xgamma s0))
  let zgamma : Real → E × E := fun s =>
    (chartCurve (I := I) x gamma s,
      chartRepAtBase (I := I) x gamma Xgamma s)
  let zeta : Real → E × E := fun s =>
    (chartCurve (I := I) x eta s,
      chartRepAtBase (I := I) x eta Xeta s)
  have hz0pos : z0.1 ∈ interior (extChartAt I x).target := by
    apply mem_interior_iff_mem_nhds.mpr
    simpa only [z0] using extChartAt_target_mem_nhds (I := I) x
  have hzgamma0 : zgamma s0 = z0 := by
    rfl
  have hzeta0 : zeta s0 = z0 := by
    change
      (extChartAt I x (eta s0),
        trivToE (I := I) x (eta s0) (lVelocity (I := I) eta s0)) =
      (extChartAt I x x,
        trivToE (I := I) x x (lVelocity (I := I) gamma s0))
    rw [← hpos0, ← hvel0]
  have hgamma0 := hgamma.self_of_nhds
  have heta0 := heta.self_of_nhds
  have hgamma_src : ∀ᶠ s in 𝓝 s0,
      gamma s ∈ (chartAt H x).source :=
    hgamma0.1.continuousAt.eventually
      ((chartAt H x).open_source.mem_nhds (by
        exact mem_chart_source H (gamma s0)))
  have heta_src : ∀ᶠ s in 𝓝 s0,
      eta s ∈ (chartAt H x).source :=
    heta0.1.continuousAt.eventually
      ((chartAt H x).open_source.mem_nhds (by
        rw [← hpos0]
        exact mem_chart_source H (gamma s0)))
  have hzgamma : ∀ᶠ s in 𝓝 s0,
      HasDerivAt zgamma (lPhaseField S T x s (zgamma s)) s := by
    filter_upwards [hgamma, hgamma_src] with s hs hsrc
    simpa only [zgamma, Xgamma] using
      lRegCurve_phase S T x gamma s hs.1 hsrc hs.2.1 hs.2.2
  have hzeta : ∀ᶠ s in 𝓝 s0,
      HasDerivAt zeta (lPhaseField S T x s (zeta s)) s := by
    filter_upwards [heta, heta_src] with s hs hsrc
    simpa only [zeta, Xeta] using
      lRegCurve_phase S T x eta s hs.1 hsrc hs.2.1 hs.2.2
  have hphase := lPhaseSol_unique_at S hS T x s0 z0 hT hz0pos
    hzgamma0 hzeta0 hzgamma hzeta
  filter_upwards [hphase, hgamma_src, heta_src] with s hs hgs hes
  apply (extChartAt I x).injOn
  · rwa [extChartAt_source_eq_chartAt_source (I := I)]
  · rwa [extChartAt_source_eq_chartAt_source (I := I)]
  · have hfst := congrArg Prod.fst hs
    simpa only [zgamma, zeta, chartCurve] using hfst

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_unique
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (hT : T ∈ D.regular)
    {gamma eta : Real → M}
    (hpos0 : gamma 0 = eta 0)
    (hvel0 : lVelocity (I := I) gamma 0 = lVelocity (I := I) eta 0)
    (hgamma : ∀ᶠ s in 𝓝 (0 : Real),
      MDifferentiableAt 𝓘(Real, Real) I gamma s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun r : Real => lVelocity (I := I) gamma r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (fun r : Real => lVelocity (I := I) gamma r) s =
          lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s))
    (heta : ∀ᶠ s in 𝓝 (0 : Real),
      MDifferentiableAt 𝓘(Real, Real) I eta s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) eta
            (fun r : Real => lVelocity (I := I) eta r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) eta
            (fun r : Real => lVelocity (I := I) eta r) s =
          lRegAccel S T s (eta s) (lVelocity (I := I) eta s)) :
    gamma =ᶠ[𝓝 (0 : Real)] eta := by
  exact lRegCurve_unique_at S hS T 0 (by simpa using hT)
    hpos0 hvel0 hgamma heta

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegAccel_inner
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (A Y : TangentSpace I x) :
    (S.base.metric (T - s ^ 2)).inner x Y (lRegAccel S T s x A) =
      2 * s ^ 2 *
          (S.base.metric (T - s ^ 2)).inner x
            (gradientFun (I := I) (S.base.metric (T - s ^ 2))
              (S.scalar (T - s ^ 2)) x) Y -
        4 * s * S.ricciAt (T - s ^ 2) x (vec2 Y A) := by
  let g := S.base.metric (T - s ^ 2)
  let grad := gradientFun (I := I) g (S.scalar (T - s ^ 2)) x
  let sharpRic := metricSharp (I := I) g x
    ((ricciTensor (I := I) g x A).toLinearMap)
  have hRic : ricciTensor (I := I) g x A Y =
      S.ricciAt (T - s ^ 2) x (vec2 Y A) := by
    calc
      ricciTensor (I := I) g x A Y = ricciTensor (I := I) g x Y A :=
        ricciTensor_symm (I := I) g x A Y
      _ = metricRicciAt (I := I) g x (vec2 Y A) :=
        (metricRicciAt_apply_eq_ricciTensor (I := I) g x Y A).symm
      _ = S.ricciAt (T - s ^ 2) x (vec2 Y A) := by rfl
  have hgrad : g.inner x Y ((2 * s ^ 2) • grad) =
      2 * s ^ 2 * g.inner x grad Y := by
    rw [(g.inner x Y).map_smul]
    simp only [smul_eq_mul]
    rw [g.symm x Y grad]
  have hric : g.inner x Y ((4 * s) • sharpRic) =
      4 * s * S.ricciAt (T - s ^ 2) x (vec2 Y A) := by
    rw [(g.inner x Y).map_smul]
    simp only [smul_eq_mul, sharpRic]
    rw [inner_metricSharp_right]
    change 4 * s * ricciTensor (I := I) g x A Y = _
    rw [hRic]
  change g.inner x Y ((2 * s ^ 2) • grad - (4 * s) • sharpRic) = _
  rw [(g.inner x Y).map_sub, hgrad, hric]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lEuler_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (s : Real) (Y : TangentSpace I (gamma (s ^ 2)))
    (hs : 0 < s)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2))
    (hvel : DifferentiableAt Real
      (chartRepAt (I := I) gamma
        (fun tau : Real => lVelocity (I := I) gamma tau) (s ^ 2)) (s ^ 2)) :
    4 * s ^ 2 * lEulerPair S T gamma (s ^ 2) Y =
      (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2)) Y
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (squareReparametrization gamma)
            (fun r : Real => lVelocity (I := I) (squareReparametrization gamma) r) s) -
        2 * s ^ 2 *
          (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
            (gradientFun (I := I) (S.base.metric (T - s ^ 2))
              (S.scalar (T - s ^ 2)) (gamma (s ^ 2))) Y +
        4 * s * S.ricciAt (T - s ^ 2) (gamma (s ^ 2))
          (vec2 Y (lVelocity (I := I) (squareReparametrization gamma) s)) := by
  let g := S.base.metric (T - s ^ 2)
  let X : ∀ tau, TangentSpace I (gamma tau) :=
    fun tau => lVelocity (I := I) gamma tau
  let alpha : Real → M := fun r => gamma (r ^ 2)
  let B : ∀ r, TangentSpace I (alpha r) := fun r => X (r ^ 2)
  have hsqdiff : DifferentiableAt Real (fun r : Real => r ^ 2) s :=
    differentiableAt_id.pow 2
  have hsqderiv : deriv (fun r : Real => r ^ 2) s = 2 * s := by
    rw [deriv_pow_field]
    norm_num
  have hBdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha B s) s := by
    have hvelX : DifferentiableAt Real
        (chartRepAt (I := I) gamma X (s ^ 2)) (s ^ 2) := by
      simpa only [X] using hvel
    change DifferentiableAt Real
      (chartRepAt (I := I) gamma X (s ^ 2) ∘ fun r : Real => r ^ 2) s
    exact DifferentiableAt.comp (f := fun r : Real => r ^ 2) s hvelX hsqdiff
  have hBcov :
      covDerivAlong (I := I) g alpha B s =
        (2 * s) • covDerivAlong (I := I) g gamma X (s ^ 2) := by
    have hcomp := covDerivAlong_comp (I := I) g gamma X
      (fun r : Real => r ^ 2) s hgamma hvel hsqdiff
    rw [hsqderiv] at hcomp
    exact hcomp
  have hlindiff : DifferentiableAt Real (fun r : Real => 2 * r) s := by
    fun_prop
  have hlinderiv : deriv (fun r : Real => 2 * r) s = 2 := by
    simp
  have hAeq :
      (fun r : Real => lVelocity (I := I) alpha r) =ᶠ[𝓝 s]
        fun r : Real => (2 * r) • B r := by
    filter_upwards [eventually_gt_nhds hs] with r hr
    rw [show alpha = squareReparametrization gamma by rfl]
    exact lVelocity_squareReparametrization_of_pos (I := I) gamma r hr
  have hAcov :
      covDerivAlong (I := I) g alpha
          (fun r : Real => lVelocity (I := I) alpha r) s =
        (2 : Real) • X (s ^ 2) +
          (2 * s) • ((2 * s) •
            covDerivAlong (I := I) g gamma X (s ^ 2)) := by
    rw [covDerivAlong_congr_of_eventuallyEq (I := I) g alpha hAeq]
    have hprod := covDerivAlong_smulFun (I := I) g alpha
      (fun r : Real => 2 * r) B s hlindiff hBdiff
    rw [hlinderiv, hBcov] at hprod
    exact hprod
  have hinner :
      g.inner (gamma (s ^ 2)) Y
          (covDerivAlong (I := I) g alpha
            (fun r : Real => lVelocity (I := I) alpha r) s) =
        2 * g.inner (gamma (s ^ 2)) Y (X (s ^ 2)) +
          4 * s ^ 2 * g.inner (gamma (s ^ 2)) Y
            (covDerivAlong (I := I) g gamma X (s ^ 2)) := by
    rw [hAcov]
    let DX := covDerivAlong (I := I) g gamma X (s ^ 2)
    have hadd :
        g.inner (gamma (s ^ 2)) Y
            ((2 : Real) • X (s ^ 2) + (2 * s) • ((2 * s) • DX)) =
          g.inner (gamma (s ^ 2)) Y ((2 : Real) • X (s ^ 2)) +
            g.inner (gamma (s ^ 2)) Y ((2 * s) • ((2 * s) • DX)) :=
      (g.inner (gamma (s ^ 2)) Y).map_add _ _
    have htwo :
        g.inner (gamma (s ^ 2)) Y ((2 : Real) • X (s ^ 2)) =
          2 * g.inner (gamma (s ^ 2)) Y (X (s ^ 2)) := by
      simpa only [smul_eq_mul] using
        (g.inner (gamma (s ^ 2)) Y).map_smul (2 : Real) (X (s ^ 2))
    have hnested :
        g.inner (gamma (s ^ 2)) Y ((2 * s) • ((2 * s) • DX)) =
          (2 * s) * ((2 * s) * g.inner (gamma (s ^ 2)) Y DX) := by
      calc
        _ = (2 * s) * g.inner (gamma (s ^ 2)) Y ((2 * s) • DX) := by
          simpa only [smul_eq_mul] using
            (g.inner (gamma (s ^ 2)) Y).map_smul (2 * s) ((2 * s) • DX)
        _ = _ := by
          rw [(g.inner (gamma (s ^ 2)) Y).map_smul (2 * s) DX]
          simp only [smul_eq_mul]
    change g.inner (gamma (s ^ 2)) Y
        ((2 : Real) • X (s ^ 2) + (2 * s) • ((2 * s) • DX)) = _
    rw [hadd, htwo, hnested]
    ring
  have hric :
      S.ricciAt (T - s ^ 2) (gamma (s ^ 2))
          (vec2 Y (lVelocity (I := I) alpha s)) =
        (2 * s) * S.ricciAt (T - s ^ 2) (gamma (s ^ 2))
          (vec2 Y (X (s ^ 2))) := by
    have hAs : lVelocity (I := I) alpha s = (2 * s) • X (s ^ 2) := by
      exact hAeq.self_of_nhds
    rw [hAs]
    have hleft : Function.update (vec2 Y (X (s ^ 2))) (1 : Fin 2)
        ((2 * s) • X (s ^ 2)) = vec2 Y ((2 * s) • X (s ^ 2)) := by
      funext i
      fin_cases i <;> simp [vec2]
    have hright : Function.update (vec2 Y (X (s ^ 2))) (1 : Fin 2)
        (X (s ^ 2)) = vec2 Y (X (s ^ 2)) := by
      funext i
      fin_cases i <;> simp [vec2]
    have hmap :=
      (S.ricciAt (T - s ^ 2) (gamma (s ^ 2))).map_update_smul
        (vec2 Y (X (s ^ 2))) (1 : Fin 2) (2 * s) (X (s ^ 2))
    rw [hleft, hright] at hmap
    simpa only [smul_eq_mul] using hmap
  change 4 * s ^ 2 * lEulerPair S T gamma (s ^ 2) Y =
    g.inner (gamma (s ^ 2)) Y
        (covDerivAlong (I := I) g alpha
          (fun r : Real => lVelocity (I := I) alpha r) s) -
      2 * s ^ 2 * g.inner (gamma (s ^ 2))
        (gradientFun (I := I) g (S.scalar (T - s ^ 2)) (gamma (s ^ 2))) Y +
      4 * s * S.ricciAt (T - s ^ 2) (gamma (s ^ 2))
        (vec2 Y (lVelocity (I := I) alpha s))
  rw [hinner, hric]
  simp only [lEulerPair, g, X]
  field_simp [ne_of_gt hs]
  ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem HasLEquationAt.accel_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (s : Real) (hs : 0 < s) (hEq : HasLEquationAt S T gamma (s ^ 2)) :
    covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
        (squareReparametrization gamma)
        (fun r : Real => lVelocity (I := I) (squareReparametrization gamma) r) s =
      lRegAccel S T s (gamma (s ^ 2))
        (lVelocity (I := I) (squareReparametrization gamma) s) := by
  rw [show gamma (s ^ 2) = squareReparametrization gamma s by rfl]
  let g := S.base.metric (T - s ^ 2)
  let alpha := squareReparametrization gamma
  let A := lVelocity (I := I) alpha s
  apply metricFlatLinear_injective (I := I) g (alpha s)
  ext Y
  simp only [metricFlatLinear_apply]
  rw [g.symm (alpha s)
    (covDerivAlong (I := I) g alpha
      (fun r : Real => lVelocity (I := I) alpha r) s) Y]
  rw [g.symm (alpha s) (lRegAccel S T s (alpha s) A) Y]
  have hsq := lEuler_sq S T gamma s Y hs hEq.1 hEq.2.1
  rw [hEq.2.2 Y, mul_zero] at hsq
  calc
    g.inner (gamma (s ^ 2)) Y
        (covDerivAlong (I := I) g alpha
          (fun r : Real => lVelocity (I := I) alpha r) s) =
      2 * s ^ 2 * g.inner (gamma (s ^ 2))
          (gradientFun (I := I) g (S.scalar (T - s ^ 2))
            (gamma (s ^ 2))) Y -
        4 * s * S.ricciAt (T - s ^ 2) (gamma (s ^ 2)) (vec2 Y A) := by
          dsimp only [g, alpha, A]
          linarith [hsq]
    _ = g.inner (gamma (s ^ 2)) Y
        (lRegAccel S T s (gamma (s ^ 2)) A) :=
      (lRegAccel_inner S T s (gamma (s ^ 2)) A Y).symm

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
