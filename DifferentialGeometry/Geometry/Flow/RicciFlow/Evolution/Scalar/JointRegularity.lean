import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TraceAlgebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff BigOperators Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [SigmaCompactSpace M] in
theorem scalar_joint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M => S.scalar p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
  classical
  intro p hp
  let x₀ : M := p.2
  let frame := coordinateFrameAt (I := I) x₀
  let t : D.RegularTime := ⟨p.1, hp.1⟩
  have hx : p.2 ∈ coordinateFrameSet (I := I) x₀ := by
    simpa only [x₀] using coordinateFrameAt_mem (I := I) p.2
  have hdomain :
      D.regular ×ˢ coordinateFrameSet (I := I) x₀ ∈ 𝓝 p :=
    prod_mem_nhds (D.regular_isOpen.mem_nhds hp.1)
      ((coordinateFrameSet_open (I := I) x₀).mem_nhds hx)
  have hmetric (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          metricCompInFrame (I := I) S frame q.1 q.2 i j) p := by
    simpa only [frame] using
      (coordMetricSmooth (I := I) S hS x₀ i j).contMDiffAt hdomain
  have hderiv (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          deriv (fun s : Real =>
            metricCompInFrame (I := I) S frame s q.2 i j) q.1) p := by
    exact timeDeriv_smoothAt (hmetric i j) (by simp)
  have hricci (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          ricciCompInFrame (I := I) S frame q.1 q.2 i j) p := by
    have hsmooth :
        ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
          (modelWithCornersSelf Real Real) ∞
          (fun q : Real × M => (-1 / 2 : Real) *
            deriv (fun s : Real =>
              metricCompInFrame (I := I) S frame s q.2 i j) q.1) p :=
      contMDiffAt_const.mul (hderiv i j)
    refine hsmooth.congr_of_eventuallyEq ?_
    filter_upwards [hdomain] with q hq
    have heq :=
      ((metricCompInFrame_hasDerivWithinAt
        (I := I) S hS frame
        (⟨q.1, hq.1⟩ : D.RegularTime) q.2 i j).hasDerivAt
          (D.regular_mem_nhds hq.1)).deriv
    rw [heq]
    ring
  have hinv (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M => coordInv (I := I) S x₀ q.1 q.2 i j) p := by
    simpa only [t] using
      coordInvSmoothAt (I := I) S hS x₀ t p.2 hx i j
  have htrace :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          ∑ i, ∑ j,
            coordInv (I := I) S x₀ q.1 q.2 i j *
              ricciCompInFrame (I := I) S frame q.1 q.2 i j) p := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (hinv i j).mul (hricci i j)
  refine (htrace.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hdomain] with q hq
  change S.scalar q.1 q.2 =
    scalarTraceInFrame (I := I) S (coordInv (I := I) S x₀)
      frame q.1 q.2
  symm
  rw [scalarTraceInFrame_eq_metricTracePair
    (I := I) S (coordInv (I := I) S x₀) frame
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordInvLocal (I := I) S x₀) q.1 hq.2]
  rw [SolutionOn.scalar_eq_metricTrace]
  simp only [SolutionOn.ricci, SolutionFamily.ricci_apply]
  rfl

omit [SigmaCompactSpace M] in
theorem chartScalFun_smooth
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (alpha : M) :
    ContDiffOn Real ∞
      (fun q : Real × E =>
        S.scalar q.1 ((extChartAt I alpha).symm q.2))
      (D.regular ×ˢ interior (extChartAt I alpha).target) := by
  intro q hq
  let x := (extChartAt I alpha).symm q.2
  have hscalar : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun z : Real × M => S.scalar z.1 z.2) (q.1, x) :=
    (scalar_joint (I := I) S hS).contMDiffAt
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds
        ⟨hq.1, Set.mem_univ x⟩)
  have hsymm : ContMDiffAt 𝓘(Real, E) I ∞
      (extChartAt I alpha).symm q.2 :=
    ((contMDiffOn_extChartAt_symm (I := I) alpha) q.2
      (interior_subset hq.2)).contMDiffAt
        (Filter.mem_of_superset (isOpen_interior.mem_nhds hq.2)
          interior_subset)
  have hmap : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E))
      (𝓘(Real, Real).prod I) ∞
      (fun z : Real × E => (z.1, (extChartAt I alpha).symm z.2)) q :=
    contMDiffAt_fst.prodMk (hsymm.comp q contMDiffAt_snd)
  have hcomp := hscalar.comp q hmap
  have hdiff : ContDiffAt Real ∞
      (fun z : Real × E =>
        S.scalar z.1 ((extChartAt I alpha).symm z.2)) q := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    change ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E)) 𝓘(Real, Real) ∞
      ((fun z : Real × M => S.scalar z.1 z.2) ∘
        fun z : Real × E => (z.1, (extChartAt I alpha).symm z.2)) q
    exact hcomp
  exact hdiff.contDiffWithinAt

noncomputable def chartScalCov
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (alpha : M) (q : Real × E) : E →L[Real] Real :=
  (fderiv Real
    (fun z : Real × E =>
      S.scalar z.1 ((extChartAt I alpha).symm z.2)) q).comp
    (ContinuousLinearMap.inr Real Real E)

omit [SigmaCompactSpace M] in
theorem chartScalCov_smooth
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (alpha : M) :
    ContDiffOn Real ∞ (chartScalCov (I := I) S alpha)
      (D.regular ×ˢ interior (extChartAt I alpha).target) := by
  let U : Set (Real × E) :=
    D.regular ×ˢ interior (extChartAt I alpha).target
  have hU : IsOpen U := D.regular_isOpen.prod isOpen_interior
  have hfun := chartScalFun_smooth (I := I) S hS alpha
  have hfd : ContDiffOn Real ∞
      (fderiv Real (fun z : Real × E =>
        S.scalar z.1 ((extChartAt I alpha).symm z.2))) U :=
    hfun.fderiv_of_isOpen hU (by rw [ENat.coe_top_add_one])
  have hcomp := ((ContinuousLinearMap.compL Real E (Real × E) Real).flip
    (ContinuousLinearMap.inr Real Real E)).contDiff.comp_contDiffOn hfd
  change ContDiffOn Real ∞
    (((ContinuousLinearMap.compL Real E (Real × E) Real).flip
      (ContinuousLinearMap.inr Real Real E)) ∘
        fderiv Real (fun z : Real × E =>
          S.scalar z.1 ((extChartAt I alpha).symm z.2))) U
  exact hcomp

omit [SigmaCompactSpace M] in
theorem chartScalCov_eq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (alpha : M)
    {t : Real} {y : E} (ht : t ∈ D.regular)
    (hy : y ∈ interior (extChartAt I alpha).target) :
    chartScalCov (I := I) S alpha (t, y) =
      fderiv Real (scalarOnE (I := I) alpha (S.scalar t)) y := by
  let G : Real × E → Real := fun z =>
    S.scalar z.1 ((extChartAt I alpha).symm z.2)
  have hG : DifferentiableAt Real G (t, y) :=
    ((chartScalFun_smooth (I := I) S hS alpha).contDiffAt
      ((D.regular_isOpen.prod isOpen_interior).mem_nhds ⟨ht, hy⟩)).differentiableAt
        (by simp)
  have hpair : HasFDerivAt (fun z : E => ((t, z) : Real × E))
      (ContinuousLinearMap.inr Real Real E) y :=
    (hasFDerivAt_const (x := y) (c := t)).prodMk (hasFDerivAt_id y)
  have hslice := hG.hasFDerivAt.comp y hpair
  rw [chartScalCov]
  exact hslice.fderiv.symm

omit [SigmaCompactSpace M] in
theorem chartScalCov_apply
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (alpha : M)
    {t : Real} {y : E} (ht : t ∈ D.regular)
    (hy : y ∈ interior (extChartAt I alpha).target) (w : E) :
    chartScalCov (I := I) S alpha (t, y) w =
      fderiv Real (scalarOnE (I := I) alpha (S.scalar t)) y w := by
  rw [chartScalCov_eq (I := I) S hS alpha ht hy]

omit [SigmaCompactSpace M] in
theorem chartScalarDeriv
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (α : M)
    (j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E =>
        let x := (extChartAt I α).symm p.2
        mvfderiv (I := I) (S.scalar p.1) x
          (chartBasisVecFiber (I := I) α j x))
      (D.regular ×ˢ interior (extChartAt I α).target) := by
  intro p hp
  let x := (extChartAt I α).symm p.2
  have hxsrc : x ∈ (chartAt H α).source := by
    have hxext : x ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (interior_subset hp.2)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hxext
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hscalar : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => S.scalar q.1 q.2) (p.1, x) :=
    (scalar_joint (I := I) S hS).contMDiffAt
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds
        ⟨hp.1, Set.mem_univ x⟩)
  have hframe : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (fun y : M => TotalSpace.mk' E y
        (chartBasisVecFiber (I := I) α j y)) x :=
    (chartBasisVec_contMDiffOn (I := I) α j).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hxbase)
  have hderiv := DifferentialGeometry.prodExtDerivAt_smooth hscalar hframe
  have hsymm : ContMDiffAt 𝓘(Real, E) I ∞
      (extChartAt I α).symm p.2 :=
    ((contMDiffOn_extChartAt_symm (I := I) α) p.2
      (interior_subset hp.2)).contMDiffAt
        (Filter.mem_of_superset (isOpen_interior.mem_nhds hp.2)
          interior_subset)
  have hmap : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E))
      (𝓘(Real, Real).prod I) ∞
      (fun q : Real × E => (q.1, (extChartAt I α).symm q.2)) p :=
    contMDiffAt_fst.prodMk (hsymm.comp p contMDiffAt_snd)
  have hcomp := hderiv.comp p hmap
  have hdiff : ContDiffAt Real ∞
      (fun q : Real × E =>
        let y := (extChartAt I α).symm q.2
        mvfderiv (I := I) (S.scalar q.1) y
          (chartBasisVecFiber (I := I) α j y)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    change ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E)) 𝓘(Real, Real) ∞
      ((fun p : Real × M =>
        mvfderiv (I := I) (S.scalar p.1) p.2
          (chartBasisVecFiber (I := I) α j p.2)) ∘
        fun q : Real × E => (q.1, (extChartAt I α).symm q.2)) p
    exact hcomp
  exact hdiff.contDiffWithinAt

omit [SigmaCompactSpace M] in
private theorem scalarPart_joint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (alpha : M)
    (j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
          (scalarOnE (I := I) alpha (S.scalar p.1)) p.2)
      (D.regular ×ˢ interior (extChartAt I alpha).target) := by
  refine (chartScalarDeriv (I := I) S hS alpha j).congr ?_
  intro p hp
  let x := (extChartAt I alpha).symm p.2
  have hxsrc : x ∈ (chartAt H alpha).source := by
    have hxext : x ∈ (extChartAt I alpha).source :=
      (extChartAt I alpha).map_target (interior_subset hp.2)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hxext
  have hright : extChartAt I alpha x = p.2 :=
    (extChartAt I alpha).right_inv (interior_subset hp.2)
  rw [mvfderiv_real_eq_mfderiv]
  change DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
      (scalarOnE (I := I) alpha (S.scalar p.1)) p.2 =
    mfderiv I 𝓘(Real, Real) (S.scalar p.1) x
      (chartBasisVecFiber (I := I) alpha j x)
  rw [← hright]
  exact (mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) alpha
    ((scalarSmoothOfSol (I := I) S p.1).mdifferentiableAt (by simp))
    hxsrc (by simpa only [hright] using hp.2) j).symm

omit [SigmaCompactSpace M] in
theorem chartScalarHess
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (alpha : M)
    (i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E =>
        let x := (extChartAt I alpha).symm p.2
        chartHessianTensor (I := I) (S.family.metric p.1) alpha
          (S.scalar p.1) i j x)
      (D.regular ×ˢ interior (extChartAt I alpha).target) := by
  classical
  let U := D.regular ×ˢ interior (extChartAt I alpha).target
  have hfirst (k : Fin (Module.finrank Real E)) : ContDiffOn Real ∞
      (fun p : Real × E => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k
        (scalarOnE (I := I) alpha (S.scalar p.1)) p.2) U := by
    exact scalarPart_joint (I := I) S hS alpha k
  have hsecond : ContDiffOn Real ∞
      (fun p : Real × E => chartIteratedPartialDeriv (I := I) alpha
        (S.scalar p.1) i j p.2) U := by
    have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t y => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
        (scalarOnE (I := I) alpha (S.scalar t)) y)
      D.regular_isOpen.uniqueDiffOn isOpen_interior
        (scalarPart_joint (I := I) S hS alpha j)
    have hraw := hfd.clm_apply
      (contDiffOn_const (c := chartModelBasis E i))
    change ContDiffOn Real ∞
      (fun p : Real × E =>
        (Function.uncurry (fun t y => fderiv Real
          (fun z => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
            (scalarOnE (I := I) alpha (S.scalar t)) z) y) p)
          (chartModelBasis E i)) U
    exact hraw
  have hGamma (k : Fin (Module.finrank Real E)) : ContDiffOn Real ∞
      (fun p : Real × E => chartChristoffel (I := I)
        (S.family.metric p.1) alpha i j k p.2) U :=
    MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn
      (I := I) (g_fam := S.family.metric) hS.smoothMetric
      (J := D.regular) (fun _ ht => ht) D.regular_isOpen.uniqueDiffOn alpha i j k
  have hchart : ContDiffOn Real ∞
      (fun p : Real × E =>
        chartIteratedPartialDeriv (I := I) alpha (S.scalar p.1) i j p.2 -
          ∑ k, chartChristoffel (I := I) (S.family.metric p.1)
            alpha i j k p.2 * DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k
              (scalarOnE (I := I) alpha (S.scalar p.1)) p.2) U := by
    exact hsecond.sub (ContDiffOn.sum fun k _ => (hGamma k).mul (hfirst k))
  refine hchart.congr ?_
  intro p hp
  have hright : extChartAt I alpha ((extChartAt I alpha).symm p.2) = p.2 :=
    (extChartAt I alpha).right_inv (interior_subset hp.2)
  simp only [chartHessianTensor_def, hright]

omit [SigmaCompactSpace M] in
theorem scalarHess_cont [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.regular
      (fun t x => hessianSec (I := I) (S.base.connection t)
        (metricCov_smooth (I := I) (S.base.metric t))
        (S.scalar t) (scalarSmoothOfSol (I := I) S t) x) := by
  classical
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun alpha => chartLeviCivitaGoodSet (I := I) alpha)
    (hN := fun alpha => (chartLeviCivitaGoodSet_isOpen (I := I) alpha).mem_nhds
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := alpha)))
  intro alpha idx
  have hincl : ContinuousOn
      (fun q : {t : Real // t ∈ D.regular} × M =>
        ((q.1 : Real), extChartAt I alpha q.2))
      {q : {t : Real // t ∈ D.regular} × M |
        q.2 ∈ chartLeviCivitaGoodSet (I := I) alpha} :=
    (continuous_subtype_val.comp continuous_fst).continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) alpha).comp
        continuous_snd.continuousOn (fun q hq =>
          chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq))
  have hraw := (chartScalarHess (I := I) S hS alpha (idx 0) (idx 1)).continuousOn
  refine (hraw.comp hincl (fun q hq =>
    ⟨q.1.2, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq⟩)).congr ?_
  intro q hq
  have hleft : (extChartAt I alpha).symm (extChartAt I alpha q.2) = q.2 :=
    (extChartAt I alpha).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq)
  have hslots :
      (fun k => chartBasisVecFiber (I := I) alpha (idx k) q.2) =
        vec2 (chartBasisVecFiber (I := I) alpha (idx 0) q.2)
          (chartBasisVecFiber (I := I) alpha (idx 1) q.2) := by
    funext k
    fin_cases k <;> rfl
  simp only [Function.comp_apply]
  rw [hslots]
  have hx := chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hq
  have hmc := MetricConnectionFamilyOn.metricCompatibleAt_regular
    (I := I) S.family q.1
  rw [hessSec_inner_cov (I := I) (S.base.connection q.1.1)
    (metricCov_smooth (I := I) (S.base.metric q.1.1))
    (S.base.metric q.1.1) (by simpa using hmc)
    (S.scalar q.1.1) (scalarSmoothOfSol (I := I) S q.1.1)]
  rw [show gradientFun (I := I) (S.base.metric q.1.1) (S.scalar q.1.1) =
      gradFun (I := I) (S.base.metric q.1.1) (S.scalar q.1.1) from rfl]
  rw [show S.base.connection q.1.1 =
      LeviCivita (I := I) (S.base.metric q.1.1) from rfl]
  rw [abstractHessian_eq_inner_cov_gradFun_extend (I := I)
    (S.base.metric q.1.1) (scalarSmoothOfSol (I := I) S q.1.1)]
  rw [chartAlphaMatrixIdentity_holds (I := I) (S.base.metric q.1.1)
    alpha (scalarSmoothOfSol (I := I) S q.1.1) hx (idx 0) (idx 1)]
  rw [hleft]
  simp only [SolutionOn.family_metric]

end DifferentialGeometry.PDE.RicciFlow

end
