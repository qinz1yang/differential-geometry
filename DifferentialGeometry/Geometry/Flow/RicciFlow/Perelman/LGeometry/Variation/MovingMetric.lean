import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Operator

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private lemma tangentCurve_diff
    (gamma : Real → M) (V : ∀ s, TangentSpace I (gamma s)) (s : Real)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma s)
    (hV : DifferentiableAt Real (chartRepAt (I := I) gamma V s) s) :
    MDifferentiableAt 𝓘(Real, Real) (I.prod 𝓘(Real, E))
      (fun r : Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (gamma r) (V r) :
          TangentBundle I M)) s := by
  rw [mdifferentiableAt_totalSpace]
  refine ⟨?_, ?_⟩
  · simpa only using hgamma
  · let e := trivializationAt E (TangentSpace I : M → Type _) (gamma s)
    have hbase : {r : Real | gamma r ∈ e.baseSet} ∈ 𝓝 s := by
      have hs : gamma s ∈ e.baseSet := by simp [e]
      exact hgamma.continuousAt (e.open_baseSet.mem_nhds hs)
    have hrep : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E)
        (chartRepAt (I := I) gamma V s) s := hV.mdifferentiableAt
    apply hrep.congr_of_eventuallyEq
    filter_upwards [hbase] with r hr
    rw [chartRepAt_apply,
      Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hr]

private lemma hasDerivAt_diag
    (F : Real × Real → Real) (t : Real)
    (hF : DifferentiableAt Real F (t, t))
    {a b : Real}
    (ha : HasDerivAt (fun s : Real => F (s, t)) a t)
    (hb : HasDerivAt (fun s : Real => F (t, s)) b t) :
    HasDerivAt (fun s : Real => F (s, s)) (a + b) t := by
  have hdiag : HasDerivAt (fun s : Real => F (s, s))
      (fderiv Real F (t, t) (1, 1)) t := by
    change HasDerivAt (F ∘ fun s : Real => (s, s))
      (fderiv Real F (t, t) (1, 1)) t
    exact HasFDerivAt.comp_hasDerivAt (f := fun s : Real => (s, s)) t hF.hasFDerivAt
      ((hasDerivAt_id t).prodMk (hasDerivAt_id t))
  have hfirst : HasDerivAt (fun s : Real => F (s, t))
      (fderiv Real F (t, t) (1, 0)) t := by
    change HasDerivAt (F ∘ fun s : Real => (s, t))
      (fderiv Real F (t, t) (1, 0)) t
    exact HasFDerivAt.comp_hasDerivAt (f := fun s : Real => (s, t)) t hF.hasFDerivAt
      ((hasDerivAt_id t).prodMk (hasDerivAt_const (x := t) (c := t)))
  have hsecond : HasDerivAt (fun s : Real => F (t, s))
      (fderiv Real F (t, t) (0, 1)) t := by
    change HasDerivAt (F ∘ fun s : Real => (t, s))
      (fderiv Real F (t, t) (0, 1)) t
    exact HasFDerivAt.comp_hasDerivAt (f := fun s : Real => (t, s)) t hF.hasFDerivAt
      ((hasDerivAt_const (x := t) (c := t)).prodMk (hasDerivAt_id t))
  have haf : fderiv Real F (t, t) (1, 0) = a := hfirst.unique ha
  have hbf : fderiv Real F (t, t) (0, 1) = b := hsecond.unique hb
  apply hdiag.congr_deriv
  calc
    fderiv Real F (t, t) (1, 1) =
        fderiv Real F (t, t) ((1, 0) + (0, 1)) := by norm_num
    _ = fderiv Real F (t, t) (1, 0) +
        fderiv Real F (t, t) (0, 1) := by rw [map_add]
    _ = a + b := by rw [haf, hbf]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem lInner_deriv_chart
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (V W : ∀ tau, TangentSpace I (gamma tau)) (tau0 : Real)
    (ht : T - tau0 ∈ D.regular)
    (hgamma_cont : ContinuousAt gamma tau0)
    (hgamma_chart :
      DifferentiableAt Real (chartCurve (I := I) (gamma tau0) gamma) tau0)
    (hV : DifferentiableAt Real (chartRepAt (I := I) gamma V tau0) tau0)
    (hW : DifferentiableAt Real (chartRepAt (I := I) gamma W tau0) tau0) :
    HasDerivAt
      (fun tau : Real =>
        (S.base.metric (T - tau)).inner (gamma tau) (V tau) (W tau))
      (((S.base.metric (T - tau0)).inner (gamma tau0)
          (covDerivAlong (I := I) (S.base.metric (T - tau0)) gamma V tau0)
          (W tau0) +
        (S.base.metric (T - tau0)).inner (gamma tau0) (V tau0)
          (covDerivAlong (I := I) (S.base.metric (T - tau0)) gamma W tau0)) +
        2 * S.ricciAt (T - tau0) (gamma tau0)
          (DifferentialGeometry.Geometry.Curvature.vec2 (V tau0) (W tau0)))
      tau0 := by
  classical
  set alpha : M := gamma tau0 with halpha
  set e := trivializationAt E (TangentSpace I : M → Type _) alpha with he
  set b := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E with hb
  set u : Real → E := chartCurve (I := I) alpha gamma with hu
  set Vrep : Real → E := chartRepAt (I := I) gamma V tau0 with hVrep
  set Wrep : Real → E := chartRepAt (I := I) gamma W tau0 with hWrep
  set Q : Real × Real → Real := fun p =>
    ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
      chartGramOnE (I := I) (S.family.metric (T - p.1)) alpha i j (u p.2) *
        chartCoord (E := E) i (Vrep p.2) * chartCoord (E := E) j (Wrep p.2)
    with hQ
  have hu0 : u tau0 ∈ (extChartAt I alpha).target := by
    have hxsrc : gamma tau0 ∈ (extChartAt I alpha).source := by
      rw [extChartAt_source, halpha]
      exact mem_chart_source H (gamma tau0)
    exact (extChartAt I alpha).map_source hxsrc
  have hinv0 : (extChartAt I alpha).symm (u tau0) = alpha := by
    calc
      (extChartAt I alpha).symm (u tau0) = gamma tau0 := by
        rw [hu, chartCurve_def]
        exact (extChartAt I alpha).left_inv (by
          rw [extChartAt_source, halpha]
          exact mem_chart_source H (gamma tau0))
      _ = alpha := halpha.symm
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  have hentry : ∀ i j : Fin (Module.finrank Real E),
      DifferentiableAt Real
        (fun q : Real × E =>
          chartGramOnE (I := I) (S.family.metric q.1) alpha i j q.2)
        (T - tau0, u tau0) := by
    intro i j
    have hcompOn := hS.smoothMetric.frameCompSmooth (e.localFrame b) hframe i j
    have hbase : alpha ∈ e.baseSet := by simp [e]
    have hcompAt : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          (S.family.metric q.1).inner q.2
            (e.localFrame b i q.2) (e.localFrame b j q.2))
        (T - tau0, alpha) :=
      hcompOn.contMDiffAt
        (prod_mem_nhds (D.regular_isOpen.mem_nhds ht)
          (e.open_baseSet.mem_nhds hbase))
    have hsymm : ContMDiffAt 𝓘(Real, E) I (∞ : WithTop ℕ∞)
        (extChartAt I alpha).symm (u tau0) :=
      (contMDiffOn_extChartAt_symm (I := I) (n := (∞ : WithTop ℕ∞)) alpha).contMDiffAt
        ((isOpen_extChartAt_target (I := I) alpha).mem_nhds hu0)
    have hmap : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E))
        (𝓘(Real, Real).prod I) (∞ : WithTop ℕ∞)
        (fun q : Real × E => (q.1, (extChartAt I alpha).symm q.2))
        (T - tau0, u tau0) :=
      contMDiffAt_fst.prodMk
        (hsymm.comp (T - tau0, u tau0) contMDiffAt_snd)
    have hjoint0 := hcompAt.comp_of_eq hmap (by simp only [hinv0])
    have hjoint : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E)) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        (fun q : Real × E =>
          (S.family.metric q.1).inner ((extChartAt I alpha).symm q.2)
            (e.localFrame b i ((extChartAt I alpha).symm q.2))
            (e.localFrame b j ((extChartAt I alpha).symm q.2)))
        (T - tau0, u tau0) := by
      change ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E)) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        ((fun q : Real × M =>
          (S.family.metric q.1).inner q.2
            (e.localFrame b i q.2) (e.localFrame b j q.2)) ∘
          fun q : Real × E => (q.1, (extChartAt I alpha).symm q.2))
        (T - tau0, u tau0)
      exact hjoint0
    have htarget : ∀ᶠ q : Real × E in nhds (T - tau0, u tau0),
        q.2 ∈ (extChartAt I alpha).target :=
      (continuous_snd.tendsto (T - tau0, u tau0)).eventually
        ((isOpen_extChartAt_target (I := I) alpha).mem_nhds hu0)
    have heq :
        (fun q : Real × E =>
          (S.family.metric q.1).inner ((extChartAt I alpha).symm q.2)
            (e.localFrame b i ((extChartAt I alpha).symm q.2))
            (e.localFrame b j ((extChartAt I alpha).symm q.2))) =ᶠ[nhds (T - tau0, u tau0)]
        (fun q : Real × E =>
          chartGramOnE (I := I) (S.family.metric q.1) alpha i j q.2) := by
      filter_upwards [htarget] with q hq
      have hxsrc : (extChartAt I alpha).symm q.2 ∈ (extChartAt I alpha).source :=
        (extChartAt I alpha).map_target hq
      have hxbase : (extChartAt I alpha).symm q.2 ∈ e.baseSet := by
        rw [he, TangentBundle.trivializationAt_baseSet]
        rw [← extChartAt_source_eq_chartAt_source (I := I)]
        exact hxsrc
      rw [chartGramOnE_def, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
        e.localFrame_apply_of_mem_baseSet b hxbase,
        e.localFrame_apply_of_mem_baseSet b hxbase]
      simp only [e, b, Bundle.Trivialization.basisAt, Module.Basis.map_apply,
        Trivialization.linearEquivAt_symm_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber,
        Trivialization.symmL_apply _ hxbase]
    have hcd : ContDiffAt Real (∞ : WithTop ℕ∞)
        (fun q : Real × E =>
          chartGramOnE (I := I) (S.family.metric q.1) alpha i j q.2)
        (T - tau0, u tau0) := by
      rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
        ← chartedSpaceSelf_prod]
      exact hjoint.congr_of_eventuallyEq heq.symm
    exact hcd.differentiableAt (by simp)
  have hpair : DifferentiableAt Real
      (fun p : Real × Real => (T - p.1, u p.2)) (tau0, tau0) := by
    have htpart : DifferentiableAt Real (fun p : Real × Real => T - p.1)
        (tau0, tau0) :=
      (differentiableAt_const (c := T)).sub differentiableAt_fst
    have hsnd : DifferentiableAt Real (fun p : Real × Real => p.2)
        (tau0, tau0) := differentiableAt_snd
    have hup : DifferentiableAt Real (fun p : Real × Real => u p.2)
        (tau0, tau0) := by
      change DifferentiableAt Real (u ∘ fun p : Real × Real => p.2) (tau0, tau0)
      exact hgamma_chart.comp (tau0, tau0) hsnd
    exact htpart.prodMk hup
  have hVpair : DifferentiableAt Real (fun p : Real × Real => Vrep p.2)
      (tau0, tau0) := by
    have hsnd : DifferentiableAt Real (fun p : Real × Real => p.2)
        (tau0, tau0) := differentiableAt_snd
    change DifferentiableAt Real (Vrep ∘ fun p : Real × Real => p.2) (tau0, tau0)
    exact hV.comp (tau0, tau0) hsnd
  have hWpair : DifferentiableAt Real (fun p : Real × Real => Wrep p.2)
      (tau0, tau0) := by
    have hsnd : DifferentiableAt Real (fun p : Real × Real => p.2)
        (tau0, tau0) := differentiableAt_snd
    change DifferentiableAt Real (Wrep ∘ fun p : Real × Real => p.2) (tau0, tau0)
    exact hW.comp (tau0, tau0) hsnd
  have hQdiff : DifferentiableAt Real Q (tau0, tau0) := by
    rw [hQ]
    refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
    have hG := (hentry i j).comp (tau0, tau0) hpair
    have hVi := (chartCoordCLM (E := E) i).differentiableAt.comp
      (tau0, tau0) hVpair
    have hWj := (chartCoordCLM (E := E) j).differentiableAt.comp
      (tau0, tau0) hWpair
    change DifferentiableAt Real
      ((((fun q : Real × E =>
        chartGramOnE (I := I) (S.family.metric q.1) alpha i j q.2) ∘
          fun p : Real × Real => (T - p.1, u p.2)) *
        ((chartCoordCLM (E := E) i) ∘ fun p : Real × Real => Vrep p.2)) *
        ((chartCoordCLM (E := E) j) ∘ fun p : Real × Real => Wrep p.2))
      (tau0, tau0)
    exact (hG.mul hVi).mul hWj
  have hbase_nhds : {s : Real | gamma s ∈ e.baseSet} ∈ nhds tau0 := by
    have hbase : gamma tau0 ∈ e.baseSet := by simp [halpha, e]
    exact hgamma_cont (e.open_baseSet.mem_nhds hbase)
  have hdiagEq :
      (fun s : Real =>
        (S.family.metric (T - s)).inner (gamma s) (V s) (W s)) =ᶠ[nhds tau0]
        (fun s : Real => Q (s, s)) := by
    filter_upwards [hbase_nhds] with s hs
    have hVr : e.symmL Real (gamma s) (Vrep s) = V s := by
      simpa [hVrep, chartRepAt_apply] using
        e.symmL_continuousLinearMapAt (R := Real) hs (V s)
    have hWr : e.symmL Real (gamma s) (Wrep s) = W s := by
      simpa [hWrep, chartRepAt_apply] using
        e.symmL_continuousLinearMapAt (R := Real) hs (W s)
    rw [hQ]
    have hinv : (extChartAt I alpha).symm (u s) = gamma s := by
      rw [hu, chartCurve_def]
      exact (extChartAt I alpha).left_inv (by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        simpa [e, TangentBundle.trivializationAt_baseSet] using hs)
    rw [← hVr, ← hWr,
      inner_eq_chartGramOnE_bilinear_on_baseSet (I := I)
        (S.family.metric (T - s)) alpha (Vrep s) (Wrep s)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [chartGramOnE_def, hinv]
  have hspace :=
    DifferentialGeometry.Geometry.Riemannian.Variation.metric_compat_hasDerivAt_inner_of_chartCurveDeriv
      (I := I) (S.family.metric (T - tau0)) gamma V W tau0
      hgamma_cont hgamma_chart hV hW
  have hspaceQ : HasDerivAt (fun s : Real => Q (tau0, s))
      ((S.family.metric (T - tau0)).inner (gamma tau0)
          (covDerivAlong (I := I) (S.family.metric (T - tau0)) gamma V tau0)
          (W tau0) +
        (S.family.metric (T - tau0)).inner (gamma tau0) (V tau0)
          (covDerivAlong (I := I) (S.family.metric (T - tau0)) gamma W tau0)) tau0 := by
    apply hspace.congr_of_eventuallyEq
    filter_upwards [hbase_nhds] with s hs
    have hVr : e.symmL Real (gamma s) (Vrep s) = V s := by
      simpa [hVrep, chartRepAt_apply] using
        e.symmL_continuousLinearMapAt (R := Real) hs (V s)
    have hWr : e.symmL Real (gamma s) (Wrep s) = W s := by
      simpa [hWrep, chartRepAt_apply] using
        e.symmL_continuousLinearMapAt (R := Real) hs (W s)
    rw [hQ]
    have hinv : (extChartAt I alpha).symm (u s) = gamma s := by
      rw [hu, chartCurve_def]
      exact (extChartAt I alpha).left_inv (by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        simpa [e, TangentBundle.trivializationAt_baseSet] using hs)
    rw [← hVr, ← hWr,
      inner_eq_chartGramOnE_bilinear_on_baseSet (I := I)
        (S.family.metric (T - tau0)) alpha (Vrep s) (Wrep s)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [chartGramOnE_def, hinv]
  have hmetric := metricDerivAt (I := I) S hS
    (⟨T - tau0, ht⟩ :
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (gamma tau0) (V tau0) (W tau0)
  have hsub : HasDerivAt (fun tau : Real => T - tau) (-1) tau0 := by
    change HasDerivAt ((fun _ : Real => T) - id) (-1) tau0
    simpa using (hasDerivAt_const (x := tau0) (c := T)).sub
      (hasDerivAt_id (x := tau0))
  have htime := hmetric.comp tau0 hsub
  have htimeQ : HasDerivAt (fun s : Real => Q (s, tau0))
      (2 * S.ricciAt (T - tau0) (gamma tau0)
        (DifferentialGeometry.Geometry.Curvature.vec2 (V tau0) (W tau0))) tau0 := by
    have htime' : HasDerivAt
        (fun s : Real =>
          (S.family.metric (T - s)).inner (gamma tau0) (V tau0) (W tau0))
        (2 * S.ricciAt (T - tau0) (gamma tau0)
          (DifferentialGeometry.Geometry.Curvature.vec2 (V tau0) (W tau0))) tau0 := by
      change HasDerivAt
        ((fun r : Real =>
          (S.family.metric r).inner (gamma tau0) (V tau0) (W tau0)) ∘
          fun r : Real => T - r)
        (2 * S.ricciAt (T - tau0) (gamma tau0)
          (DifferentialGeometry.Geometry.Curvature.vec2 (V tau0) (W tau0))) tau0
      simpa only [mul_neg, neg_mul, neg_neg, mul_one] using htime
    apply htime'.congr_of_eventuallyEq
    rw [hQ]
    have hbase : gamma tau0 ∈ e.baseSet := by simp [halpha, e]
    have hVr : e.symmL Real (gamma tau0) (Vrep tau0) = V tau0 := by
      simpa [hVrep, chartRepAt_apply] using
        e.symmL_continuousLinearMapAt (R := Real) hbase (V tau0)
    have hWr : e.symmL Real (gamma tau0) (Wrep tau0) = W tau0 := by
      simpa [hWrep, chartRepAt_apply] using
        e.symmL_continuousLinearMapAt (R := Real) hbase (W tau0)
    filter_upwards [] with s
    have hinv : (extChartAt I alpha).symm (u tau0) = gamma tau0 := by
      rw [hu, chartCurve_def]
      exact (extChartAt I alpha).left_inv (by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact mem_chart_source H (gamma tau0))
    rw [← hVr, ← hWr,
      inner_eq_chartGramOnE_bilinear_on_baseSet (I := I)
        (S.family.metric (T - s)) alpha (Vrep tau0) (Wrep tau0)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [chartGramOnE_def, hinv]
  have hQdiag := hasDerivAt_diag Q tau0 hQdiff htimeQ hspaceQ
  exact (hQdiag.congr_of_eventuallyEq hdiagEq).congr_deriv (by
    simp only [SolutionOn.family_metric]
    ring)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem lInner_deriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (V W : ∀ tau, TangentSpace I (gamma tau)) (tau0 : Real)
    (ht : T - tau0 ∈ D.regular)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma tau0)
    (hV : DifferentiableAt Real (chartRepAt (I := I) gamma V tau0) tau0)
    (hW : DifferentiableAt Real (chartRepAt (I := I) gamma W tau0) tau0) :
    HasDerivAt
      (fun tau : Real =>
        (S.base.metric (T - tau)).inner (gamma tau) (V tau) (W tau))
      (((S.base.metric (T - tau0)).inner (gamma tau0)
          (covDerivAlong (I := I) (S.base.metric (T - tau0)) gamma V tau0)
          (W tau0) +
        (S.base.metric (T - tau0)).inner (gamma tau0) (V tau0)
          (covDerivAlong (I := I) (S.base.metric (T - tau0)) gamma W tau0)) +
        2 * S.ricciAt (T - tau0) (gamma tau0)
          (DifferentialGeometry.Geometry.Curvature.vec2 (V tau0) (W tau0)))
      tau0 := by
  have hchart : DifferentiableAt Real
      (chartCurve (I := I) (gamma tau0) gamma) tau0 := by
    exact ((mdifferentiableAt_extChartAt
      (I := I) (x := gamma tau0) (mem_chart_source H (gamma tau0))).comp
        tau0 hgamma).differentiableAt
  exact lInner_deriv_chart S hS T gamma V W tau0 ht hgamma.continuousAt
    hchart hV hW

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegInner_deriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (alpha : Real → M)
    (V W : ∀ s, TangentSpace I (alpha s)) (s : Real)
    (ht : T - s ^ 2 ∈ D.regular)
    (halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s)
    (hV : DifferentiableAt Real (chartRepAt (I := I) alpha V s) s)
    (hW : DifferentiableAt Real (chartRepAt (I := I) alpha W s) s) :
    HasDerivAt
      (fun r : Real =>
        (S.base.metric (T - r ^ 2)).inner (alpha r) (V r) (W r))
      (((S.base.metric (T - s ^ 2)).inner (alpha s)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha V s)
          (W s) +
        (S.base.metric (T - s ^ 2)).inner (alpha s) (V s)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha W s)) +
        4 * s * S.ricciAt (T - s ^ 2) (alpha s)
          (DifferentialGeometry.Geometry.Curvature.vec2 (V s) (W s)))
      s := by
  let F : Real × Real → Real := fun p =>
    (S.base.metric (T - p.1 ^ 2)).inner (alpha p.2) (V p.2) (W p.2)
  have hsndDiff : MDifferentiableAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (fun p : Real × Real => p.2) (s, s) :=
    contMDiffAt_snd.mdifferentiableAt one_ne_zero
  have halphaPair : MDifferentiableAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I
      (fun p : Real × Real => alpha p.2) (s, s) :=
    halpha.comp (s, s) hsndDiff
  have htimeArg : MDifferentiableAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (fun p : Real × Real => T - p.1 ^ 2) (s, s) :=
    (contMDiffAt_const.sub (contMDiffAt_fst.pow 2)).mdifferentiableAt
      one_ne_zero
  have harg : MDifferentiableAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I)
      (fun p : Real × Real => (T - p.1 ^ 2, alpha p.2)) (s, s) :=
    htimeArg.prodMk halphaPair
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T - s ^ 2) (x := alpha s) (D.regular_isOpen.mem_nhds ht)
  have hmetric : MDifferentiableAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
      (fun p : Real × Real =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (alpha p.2) ((S.base.metric (T - p.1 ^ 2)).inner (alpha p.2)))
      (s, s) := by
    change MDifferentiableAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
      ((fun q : Real × M =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          q.2 ((S.base.metric q.1).inner q.2)) ∘
        fun p : Real × Real => (T - p.1 ^ 2, alpha p.2)) (s, s)
    exact (hmetric₀.mdifferentiableAt (by simp)).comp (s, s) harg
  have hVtotal := tangentCurve_diff (I := I) alpha V s halpha hV
  have hWtotal := tangentCurve_diff (I := I) alpha W s halpha hW
  have hVpair : MDifferentiableAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (fun p : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (alpha p.2) (V p.2) :
          TangentBundle I M)) (s, s) :=
    hVtotal.comp (s, s) hsndDiff
  have hWpair : MDifferentiableAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (fun p : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (alpha p.2) (W p.2) :
          TangentBundle I M)) (s, s) :=
    hWtotal.comp (s, s) hsndDiff
  have htotal := MDifferentiableAt.clm_bundle_apply₂
    (E₁ := fun y : M => TangentSpace I y)
    (E₂ := fun y : M => TangentSpace I y)
    (E₃ := fun _ : M => Real) hmetric hVpair hWpair
  have hFdiff : DifferentiableAt Real F (s, s) := by
    have hscalar : MDifferentiableAt
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real) F (s, s) := by
      rw [mdifferentiableAt_totalSpace] at htotal
      have heq : ∀ p : Real × Real,
          (trivializationAt Real (Bundle.Trivial M Real) (alpha s)
            (TotalSpace.mk' Real (alpha p.2)
              ((S.base.metric (T - p.1 ^ 2)).inner (alpha p.2) (V p.2) (W p.2)))).2 =
            F p := by
        intro p
        simp only [Bundle.Trivial.fiberBundle_trivializationAt']
        rfl
      exact htotal.2.congr_of_eventuallyEq
        (Filter.Eventually.of_forall heq)
    rw [← mdifferentiableAt_iff_differentiableAt,
      modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hscalar
  have hspace :=
    DifferentialGeometry.Geometry.Riemannian.Variation.metric_compat_hasDerivAt_inner_of_chartCurveDeriv
      (I := I) (S.base.metric (T - s ^ 2)) alpha V W s
      halpha.continuousAt
      (((mdifferentiableAt_extChartAt
        (I := I) (x := alpha s) (mem_chart_source H (alpha s))).comp
          s halpha).differentiableAt) hV hW
  have hspaceF : HasDerivAt (fun r : Real => F (s, r))
      ((S.base.metric (T - s ^ 2)).inner (alpha s)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha V s)
          (W s) +
        (S.base.metric (T - s ^ 2)).inner (alpha s) (V s)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha W s)) s := by
    simpa only [F] using hspace
  have hmetricTime := metricDerivAt (I := I) S hS
    (⟨T - s ^ 2, ht⟩ :
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (alpha s) (V s) (W s)
  have hsq : HasDerivAt (fun r : Real => T - r ^ 2) (-2 * s) s := by
    change HasDerivAt ((fun _ : Real => T) - fun r : Real => r ^ 2) (-2 * s) s
    have hpow : HasDerivAt (fun r : Real => r ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    have hsub := (hasDerivAt_const (x := s) (c := T)).sub hpow
    simpa using hsub
  have htime := hmetricTime.comp s hsq
  have htimeF : HasDerivAt (fun r : Real => F (r, s))
      (4 * s * S.ricciAt (T - s ^ 2) (alpha s)
        (DifferentialGeometry.Geometry.Curvature.vec2 (V s) (W s))) s := by
    change HasDerivAt
      ((fun q : Real => (S.base.metric q).inner (alpha s) (V s) (W s)) ∘
        fun r : Real => T - r ^ 2)
      (4 * s * S.ricciAt (T - s ^ 2) (alpha s)
        (DifferentialGeometry.Geometry.Curvature.vec2 (V s) (W s))) s
    exact htime.congr_deriv (by ring)
  exact (hasDerivAt_diag F s hFdiff htimeF hspaceF).congr_deriv (by ring)

end DifferentialGeometry.PDE.RicciFlow.Perelman
