import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ForceC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.MovingMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Basic
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramInv
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramChristoffel

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lGramPair_deriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (p : M)
    (u q : Real → E) (r : Real) (q' z : E)
    (ht : T - r ^ 2 ∈ D.regular)
    (hy : u r ∈ interior (extChartAt I p).target)
    (hu : HasDerivAt u (q r) r) (hq : HasDerivAt q q' r) :
    HasDerivAt
      (fun s ↦ inner Real
        (chartGramOp (I := I) S.family p (T - s ^ 2, u s) (q s)) z)
      (inner Real
          (chartGramOp (I := I) S.family p (T - r ^ 2, u r)
            (q' + chartChristoffelContraction (I := I)
              (S.base.metric (T - r ^ 2)) p (q r) (q r) (u r))) z +
        inner Real
          (chartGramOp (I := I) S.family p (T - r ^ 2, u r) (q r))
          (chartChristoffelContraction (I := I)
            (S.base.metric (T - r ^ 2)) p (q r) z (u r)) +
        4 * r * S.ricciAt (T - r ^ 2)
          ((extChartAt I p).symm (u r))
          (vec2 (trivFromE (I := I) p ((extChartAt I p).symm (u r)) (q r))
            (trivFromE (I := I) p ((extChartAt I p).symm (u r)) z))) r := by
  let w : Real → E × E := fun s ↦ (u s, q s)
  let wz : Real → E × E := fun s ↦ (u s, z)
  let alpha : Real → M := lPhaseCurve (I := I) p w
  let A : ∀ s, TangentSpace I (alpha s) := lPhaseVel (I := I) p w
  let Z : ∀ s, TangentSpace I (alpha s) := lPhaseVel (I := I) p wz
  let g := S.base.metric (T - r ^ 2)
  have htarget : ∀ᶠ s in nhds r, u s ∈ (extChartAt I p).target :=
    hu.continuousAt.eventually
      ((isOpen_extChartAt_target (I := I) p).mem_nhds (interior_subset hy))
  have hsource : alpha r ∈ (chartAt H p).source := by
    have hext : alpha r ∈ (extChartAt I p).source :=
      (extChartAt I p).map_target (interior_subset hy)
    simpa only [extChartAt_source] using hext
  have hbase : alpha r ∈
      (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsource
  have halpha : MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    simpa only [alpha, w] using
      lPhaseCurve_mdiff (I := I) p w r hu.differentiableAt hy
  have hAdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha A r) r := by
    simpa only [alpha, A, w] using
      lPhaseVel_diff (I := I) p w r hu.differentiableAt hq.differentiableAt hy
  have hconst : HasDerivAt (fun _ : Real ↦ z) 0 r := hasDerivAt_const r z
  have hZdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha Z r) r := by
    have hz :=
      lPhaseVel_diff (I := I) p wz r hu.differentiableAt hconst.differentiableAt hy
    refine hz.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ ?_)
    rfl
  have hcurve_eq : chartCurve (I := I) p alpha =ᶠ[nhds r] u := by
    filter_upwards [htarget] with s hs
    exact (extChartAt I p).right_inv hs
  have hA_eq : chartRepAtBase (I := I) p alpha A =ᶠ[nhds r] q := by
    filter_upwards [htarget] with s hs
    have hssrc : alpha s ∈ (chartAt H p).source := by
      have hext : alpha s ∈ (extChartAt I p).source :=
        (extChartAt I p).map_target hs
      simpa only [extChartAt_source] using hext
    have hsbase : alpha s ∈
        (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hssrc
    exact trivToE_trivFromE (I := I) p hsbase (q s)
  have hZ_eq : chartRepAtBase (I := I) p alpha Z =ᶠ[nhds r]
      (fun _ : Real ↦ z) := by
    filter_upwards [htarget] with s hs
    have hssrc : alpha s ∈ (chartAt H p).source := by
      have hext : alpha s ∈ (extChartAt I p).source :=
        (extChartAt I p).map_target hs
      simpa only [extChartAt_source] using hext
    have hsbase : alpha s ∈
        (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hssrc
    exact trivToE_trivFromE (I := I) p hsbase z
  have hcovA : covDerivAlong (I := I) g alpha A r =
      trivFromE (I := I) p (alpha r)
        (q' + chartChristoffelContraction (I := I) g p
          (q r) (q r) (u r)) := by
    have hinv := covDeriv_chartAt (I := I) g alpha A r p
      halpha hsource hAdiff
    rw [chartCovDerivAlong_def, hA_eq.deriv_eq, hq.deriv,
      hcurve_eq.deriv_eq, hu.deriv, hA_eq.eq_of_nhds,
      hcurve_eq.eq_of_nhds] at hinv
    exact hinv.symm
  have hcovZ : covDerivAlong (I := I) g alpha Z r =
      trivFromE (I := I) p (alpha r)
        (chartChristoffelContraction (I := I) g p
          (q r) z (u r)) := by
    have hinv := covDeriv_chartAt (I := I) g alpha Z r p
      halpha hsource hZdiff
    rw [chartCovDerivAlong_def, hZ_eq.deriv_eq, hconst.deriv,
      hcurve_eq.deriv_eq, hu.deriv, hZ_eq.eq_of_nhds,
      hcurve_eq.eq_of_nhds, zero_add] at hinv
    exact hinv.symm
  have hmove := lRegInner_deriv (I := I) S hS T alpha A Z r ht
    halpha hAdiff hZdiff
  refine (hmove.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [htarget] with s hs
    rw [chartGramOp_inner]
    rfl
  · rw [hcovA, hcovZ]
    rw [show alpha r = (extChartAt I p).symm (u r) from rfl]
    simp only [A, Z, w, wz, lPhaseVel, lPhaseCurve]
    have hgramA :
        (S.base.metric (T - r ^ 2)).inner ((extChartAt I p).symm (u r))
            (trivFromE (I := I) p ((extChartAt I p).symm (u r))
              (q' + chartChristoffelContraction (I := I) g p
                (q r) (q r) (u r)))
            (trivFromE (I := I) p ((extChartAt I p).symm (u r)) z) =
          inner Real
            (chartGramOp (I := I) S.family p (T - r ^ 2, u r)
              (q' + chartChristoffelContraction (I := I) g p
                (q r) (q r) (u r))) z := by
      exact (chartGramOp_inner (I := I) S.family p (T - r ^ 2, u r)
        (q' + chartChristoffelContraction (I := I) g p
          (q r) (q r) (u r)) z).symm
    have hgramZ :
        (S.base.metric (T - r ^ 2)).inner ((extChartAt I p).symm (u r))
            (trivFromE (I := I) p ((extChartAt I p).symm (u r)) (q r))
            (trivFromE (I := I) p ((extChartAt I p).symm (u r))
              (chartChristoffelContraction (I := I) g p (q r) z (u r))) =
          inner Real (chartGramOp (I := I) S.family p
            (T - r ^ 2, u r) (q r))
            (chartChristoffelContraction (I := I) g p (q r) z (u r)) := by
      exact (chartGramOp_inner (I := I) S.family p (T - r ^ 2, u r) (q r)
        (chartChristoffelContraction (I := I) g p (q r) z (u r))).symm
    dsimp only [g] at hgramA hgramZ
    dsimp only [g]
    congr 1
    congr 1

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lGramPair_shift
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a : Real) (p : M) (u q : Real → E) (r : Real) (q' z : E)
    (ht : T - (a + r) ^ 2 ∈ D.regular)
    (hy : u r ∈ interior (extChartAt I p).target)
    (hu : HasDerivAt u (q r) r) (hq : HasDerivAt q q' r) :
    HasDerivAt
      (fun x => inner Real
        (chartGramOp (I := I) S.family p
          (T - (a + x) ^ 2, u x) (q x)) z)
      (inner Real
          (chartGramOp (I := I) S.family p
            (T - (a + r) ^ 2, u r)
            (q' + chartChristoffelContraction (I := I)
              (S.base.metric (T - (a + r) ^ 2)) p
              (q r) (q r) (u r))) z +
        inner Real
          (chartGramOp (I := I) S.family p
            (T - (a + r) ^ 2, u r) (q r))
          (chartChristoffelContraction (I := I)
            (S.base.metric (T - (a + r) ^ 2)) p
            (q r) z (u r)) +
        4 * (a + r) * S.ricciAt (T - (a + r) ^ 2)
          ((extChartAt I p).symm (u r))
          (vec2 (trivFromE (I := I) p ((extChartAt I p).symm (u r)) (q r))
            (trivFromE (I := I) p ((extChartAt I p).symm (u r)) z))) r := by
  let U : Real → E := fun s => u (s - a)
  let Q : Real → E := fun s => q (s - a)
  have hshift : HasDerivAt (fun s : Real => s - a) 1 (a + r) := by
    simpa using (hasDerivAt_id (x := a + r)).sub_const a
  have har : a + r - a = r := by ring
  have hu' : HasDerivAt u (q r) (a + r - a) := by simpa only [har] using hu
  have hq' : HasDerivAt q q' (a + r - a) := by simpa only [har] using hq
  have hU : HasDerivAt U (Q (a + r)) (a + r) := by
    dsimp only [U, Q]
    rw [har]
    have h := hu'.scomp (a + r) hshift
    rw [one_smul] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  have hQ : HasDerivAt Q q' (a + r) := by
    dsimp only [Q]
    have h := hq'.scomp (a + r) hshift
    rw [one_smul] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  have habs := lGramPair_deriv (I := I) S hS T p U Q (a + r) q' z
    (by simpa only [U, Q, add_sub_cancel_left] using ht)
    (by simpa only [U, Q, add_sub_cancel_left] using hy) hU hQ
  have hplus : HasDerivAt (fun x : Real => a + x) 1 r := by
    exact (hasDerivAt_id (𝕜 := Real) (x := r)).const_add a
  dsimp only [U, Q] at habs
  simp only [har] at habs
  have hcomp := habs.comp r hplus
  refine (hcomp.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
  · change inner Real
        (chartGramOp (I := I) S.family p (T - (a + x) ^ 2, u x) (q x)) z =
      inner Real
        (chartGramOp (I := I) S.family p
          (T - (a + x) ^ 2, u (a + x - a)) (q (a + x - a))) z
    have hax : a + x - a = x := by ring
    rw [hax]
  · rw [har, mul_one]
    rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private theorem lPosRep_apply
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E) (r : Real) (w : E) :
    lChartPosRep (I := I) S T a p u q r w =
      (1 / 2 : Real) *
          inner Real
            (((fderiv Real (chartGramOp (I := I) S.family p)
              (T - (a + r) ^ 2, u.toFun r)) (0, w)) (q r)) (q r) +
        2 * (a + r) ^ 2 *
          chartScalCov (I := I) S p
            (T - (a + r) ^ 2, u.toFun r) w := by
  classical
  have hcoord (i : Fin (Module.finrank Real E)) :
      chartCoordCLM E i w = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w i := rfl
  have hkin :
      (∑ i : Fin (Module.finrank Real E),
        inner Real
            (((1 / 2 : Real) •
              (fderiv Real (chartGramOp (I := I) S.family p)
                (T - (a + r) ^ 2, u.toFun r))
                (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (q r)) (q r) *
          chartCoordCLM E i w) =
        (1 / 2 : Real) *
          inner Real
            (((fderiv Real (chartGramOp (I := I) S.family p)
              (T - (a + r) ^ 2, u.toFun r)) (0, w)) (q r)) (q r) := by
    simp_rw [hcoord]
    conv_rhs => rw [← (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr w]
    simp only [smul_apply, real_inner_smul_left]
    change (∑ i : Fin (Module.finrank Real E),
        (1 / 2 : Real) *
          inner Real
            ((((fderiv Real (chartGramOp (I := I) S.family p)
              (T - (a + r) ^ 2, u.toFun r)).comp
                (ContinuousLinearMap.inr Real Real E))
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (q r)) (q r) *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w i) =
      (1 / 2 : Real) * inner Real
        ((((fderiv Real (chartGramOp (I := I) S.family p)
          (T - (a + r) ^ 2, u.toFun r)).comp
            (ContinuousLinearMap.inr Real Real E))
          (∑ i, ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w i) • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i))
          (q r)) (q r)
    rw [map_sum, sum_apply, sum_inner]
    simp only [map_smul, smul_apply,
      real_inner_smul_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inr_apply]
    ring
  have hscal :
      (∑ i : Fin (Module.finrank Real E),
        2 * (a + r) ^ 2 *
            chartScalCov (I := I) S p
              (T - (a + r) ^ 2, u.toFun r) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) *
          chartCoordCLM E i w) =
        2 * (a + r) ^ 2 *
          chartScalCov (I := I) S p
            (T - (a + r) ^ 2, u.toFun r) w := by
    simp_rw [hcoord]
    conv_rhs => rw [← (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr w]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [lChartPosRep]
  simp only [sum_apply, smul_apply,
    smul_eq_mul]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  exact congrArg₂ (fun x y : Real => x + y) hkin hscal

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem lForcePair
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a : Real) (p : M) {L : Real} (u : timeH1 E L)
    (q : Real → E) (r : Real)
    (ht : T - (a + r) ^ 2 ∈ D.regular)
    (hy : u.toFun r ∈ interior (extChartAt I p).target) (w : E) :
    inner Real (lChartForceRep (I := I) S T a p u q r) w =
      inner Real
          (chartGramOp (I := I) S.family p
            (T - (a + r) ^ 2, u.toFun r) (q r))
          (chartChristoffelContraction (I := I)
            (S.base.metric (T - (a + r) ^ 2)) p
            (q r) w (u.toFun r)) +
        2 * (a + r) ^ 2 *
          chartScalCov (I := I) S p
            (T - (a + r) ^ 2, u.toFun r) w := by
  rw [lChartForceRep, ContinuousLinearMap.adjoint_inner_left]
  have hone (x : Real) : inner Real 1 x = x := by
    rw [real_inner_eq_re_inner, RCLike.inner_apply]
    simp
  rw [hone, lPosRep_apply]
  rw [chartGram_spatial (I := I) hS.smoothMetric p ht hy (q r) w]
  congr 1

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem lScalPair
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (p : M) {t : Real} {y : E} (ht : t ∈ D.regular)
    (hy : y ∈ interior (extChartAt I p).target) (w : E) :
    chartScalCov (I := I) S p (t, y) w =
      let x := (extChartAt I p).symm y
      (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (S.scalar t) x)
        (trivFromE (I := I) p x w) := by
  let x : M := (extChartAt I p).symm y
  let Y : TangentSpace I x := trivFromE (I := I) p x w
  have hyt : y ∈ (extChartAt I p).target := interior_subset hy
  have hxsrc : x ∈ (chartAt H p).source := by
    have hxext : x ∈ (extChartAt I p).source :=
      (extChartAt I p).map_target hyt
    simpa only [extChartAt_source] using hxext
  have hright : extChartAt I p x = y := (extChartAt I p).right_inv hyt
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hxsrc
  have hf : MDifferentiableAt I 𝓘(Real, Real) (S.scalar t) x :=
    (scalarSmoothOfSol (I := I) S t).mdifferentiableAt (by simp)
  rw [chartScalCov_apply (I := I) S hS p ht hy]
  change _ = (S.base.metric t).inner x
    (gradientFun (I := I) (S.base.metric t) (S.scalar t) x) Y
  rw [inner_gradientFun]
  have hmf := mfderiv_scalar_eq_chart_fderiv (I := I) p
    (S.scalar t) hxsrc (by simpa only [hright] using hy) hf Y
  rw [trivToE_trivFromE (I := I) p hxbase w, hright] at hmf
  exact hmf.symm

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
private theorem lAccelPair
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T s : Real) (p : M) {y : E}
    (ht : T - s ^ 2 ∈ D.regular)
    (hy : y ∈ interior (extChartAt I p).target) (q w : E) :
    let x := (extChartAt I p).symm y
    let A := trivFromE (I := I) p x q
    let Y := trivFromE (I := I) p x w
    inner Real
        (chartGramOp (I := I) S.family p (T - s ^ 2, y)
          (trivToE (I := I) p x (lRegAccel S T s x A))) w =
      2 * s ^ 2 * chartScalCov (I := I) S p (T - s ^ 2, y) w -
        4 * s * S.ricciAt (T - s ^ 2) x (vec2 A Y) := by
  let x : M := (extChartAt I p).symm y
  let A : TangentSpace I x := trivFromE (I := I) p x q
  let Y : TangentSpace I x := trivFromE (I := I) p x w
  have hyt : y ∈ (extChartAt I p).target := interior_subset hy
  have hxsrc : x ∈ (chartAt H p).source := by
    have hxext : x ∈ (extChartAt I p).source :=
      (extChartAt I p).map_target hyt
    simpa only [extChartAt_source] using hxext
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hxsrc
  have hright : (extChartAt I p).symm y = x := rfl
  dsimp only
  rw [chartGramOp_inner]
  change (S.base.metric (T - s ^ 2)).inner x
      (trivFromE (I := I) p x
        (trivToE (I := I) p x (lRegAccel S T s x A))) Y = _
  rw [trivFromE_trivToE (I := I) p hxbase]
  rw [(S.base.metric (T - s ^ 2)).symm x]
  rw [lRegAccel_inner]
  rw [← lScalPair (I := I) S hS p ht hy w]
  have hric : S.ricciAt (T - s ^ 2) x (vec2 Y A) =
      S.ricciAt (T - s ^ 2) x (vec2 A Y) := by
    change metricRicciAt (I := I) (S.base.metric (T - s ^ 2)) x (vec2 Y A) =
      metricRicciAt (I := I) (S.base.metric (T - s ^ 2)) x (vec2 A Y)
    rw [metricRicciAt_apply_eq_ricciTensor,
      metricRicciAt_apply_eq_ricciTensor, ricciTensor_symm]
  rw [hric]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lChartEuler_iff
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a : Real) (p : M) {L : Real} (u : timeH1 E L)
    (q : Real → E) (r : Real)
    (ht : T - (a + r) ^ 2 ∈ D.regular)
    (hy : u.toFun r ∈ interior (extChartAt I p).target)
    (hu : HasDerivAt u.toFun (q r) r)
    (hq : DifferentiableAt Real q r) :
    deriv (fun z => chartGramOp (I := I) S.family p
      (T - (a + z) ^ 2, u.toFun z) (q z)) r =
        lChartForceRep (I := I) S T a p u q r ↔
      deriv q r =
        (lPhaseField S T p (a + r) (u.toFun r, q r)).2 := by
  let mom : Real → E := fun z => chartGramOp (I := I) S.family p
    (T - (a + z) ^ 2, u.toFun z) (q z)
  let G : E →L[Real] E := chartGramOp (I := I) S.family p
    (T - (a + r) ^ 2, u.toFun r)
  let christ : E := chartChristoffelContraction (I := I)
    (S.base.metric (T - (a + r) ^ 2)) p (q r) (q r) (u.toFun r)
  let x : M := (extChartAt I p).symm (u.toFun r)
  let A : TangentSpace I x := trivFromE (I := I) p x (q r)
  let accel : E := trivToE (I := I) p x
    (lRegAccel S T (a + r) x A)
  have harg : DifferentiableAt Real
      (fun z : Real => (T - (a + z) ^ 2, u.toFun z)) r := by
    exact (((differentiableAt_const (c := T)).sub
      (((differentiableAt_const (c := a)).add differentiableAt_id).pow 2)).prodMk
        hu.differentiableAt)
  have hGram : DifferentiableAt Real
      (chartGramOp (I := I) S.family p)
      (T - (a + r) ^ 2, u.toFun r) := by
    have hs := chartGramOp_smooth (I := I) hS.smoothMetric p
      (K := interior (extChartAt I p).target) Subset.rfl
    exact (hs.contDiffAt
      ((D.regular_isOpen.prod isOpen_interior).mem_nhds ⟨ht, hy⟩)).differentiableAt
        (by simp)
  have hmom : DifferentiableAt Real mom r := by
    exact (hGram.comp r harg).clm_apply hq
  have hpair (z : E) :
      inner Real (deriv mom r) z =
        inner Real (G (deriv q r + christ)) z +
          inner Real (G (q r))
            (chartChristoffelContraction (I := I)
              (S.base.metric (T - (a + r) ^ 2)) p
              (q r) z (u.toFun r)) +
          4 * (a + r) * S.ricciAt (T - (a + r) ^ 2) x
            (vec2 A (trivFromE (I := I) p x z)) := by
    have hinner : HasDerivAt (fun s => inner Real (mom s) z)
        (inner Real (deriv mom r) z) r := by
      simpa only [inner_zero_right, zero_add] using
        hmom.hasDerivAt.inner Real (hasDerivAt_const r z)
    have hmove := lGramPair_shift (I := I) S hS T a p u.toFun q r
      (deriv q r) z ht hy hu hq.hasDerivAt
    exact hinner.unique hmove
  have hunit : IsUnit G := by
    exact chartGramOp_unit (I := I) hS.smoothMetric
      (J := {T - (a + r) ^ 2})
      (by simpa only [singleton_subset_iff] using ht) p
      (K := {u.toFun r})
      (by simpa only [singleton_subset_iff] using hy)
      (T - (a + r) ^ 2, u.toFun r) (by simp)
  have hinj : Function.Injective G :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  change deriv mom r = lChartForceRep (I := I) S T a p u q r ↔ _
  constructor
  · intro heuler
    have hGramEq : G (deriv q r + christ) = G accel := by
      apply ext_inner_right Real
      intro z
      have hp := hpair z
      rw [heuler, lForcePair (I := I) S hS T a p u q r ht hy z] at hp
      have ha := lAccelPair (I := I) S hS T (a + r) p ht hy (q r) z
      change inner Real (G accel) z =
        2 * (a + r) ^ 2 *
            chartScalCov (I := I) S p
              (T - (a + r) ^ 2, u.toFun r) z -
          4 * (a + r) * S.ricciAt (T - (a + r) ^ 2) x
            (vec2 A (trivFromE (I := I) p x z)) at ha
      linarith
    have hsum : deriv q r + christ = accel := hinj hGramEq
    have hphase : deriv q r = -christ + accel := by
      rw [← hsum]
      abel
    simpa only [lPhaseField, christ, accel, x, A] using hphase
  · intro hphase
    have hphase' : deriv q r = -christ + accel := by
      simpa only [lPhaseField, christ, accel, x, A] using hphase
    have hsum : deriv q r + christ = accel := by
      rw [hphase']
      abel
    apply ext_inner_right Real
    intro z
    have hp := hpair z
    rw [hsum] at hp
    have ha := lAccelPair (I := I) S hS T (a + r) p ht hy (q r) z
    change inner Real (G accel) z =
      2 * (a + r) ^ 2 *
          chartScalCov (I := I) S p
            (T - (a + r) ^ 2, u.toFun r) z -
        4 * (a + r) * S.ricciAt (T - (a + r) ^ 2) x
          (vec2 A (trivFromE (I := I) p x z)) at ha
    rw [lForcePair (I := I) S hS T a p u q r ht hy z]
    linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
