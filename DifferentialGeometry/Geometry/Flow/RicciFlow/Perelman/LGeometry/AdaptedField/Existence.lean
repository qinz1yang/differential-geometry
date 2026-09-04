import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Chart
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Regularity.Joint
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Smoothness
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Parametric
import Mathlib.Algebra.Order.Field.Pi
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open Bundle Filter Set
open scoped Bundle Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem movingCov_smooth
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y : ∀ s, TangentSpace I (alpha s))
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {Omega : Set Real} (hOmega : IsOpen Omega)
    (hY : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) Omega)
    (hreg : ∀ s ∈ Omega, T - s ^ 2 ∈ D.regular) :
    ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (alpha s)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s) :
            TangentBundle I M)) Omega := by
  classical
  intro t ht
  have hnhds : Omega ∈ 𝓝 t := hOmega.mem_nhds ht
  let e := trivializationAt E (TangentSpace I : M → Type _) (alpha t)
  let u : Real → E := chartCurve (I := I) (alpha t) alpha
  let rep : Real → E := chartRepAtBase (I := I) (alpha t) alpha Y
  let tau : Real → Real := fun s ↦ T - s ^ 2
  have htreg : tau t ∈ D.regular := hreg t ht
  have halphaAt : ContMDiffAt (modelWithCornersSelf Real Real) I ∞ alpha t :=
    halpha.contMDiffAt
  have hYAt : ContMDiffAt (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) t :=
    (hY t ht).contMDiffAt hnhds
  have huInf : ContDiffAt Real ∞ u t := by
    have h := (contMDiffAt_extChartAt (I := I) (x := alpha t) (n := ∞)).comp t halphaAt
    exact contMDiffAt_iff_contDiffAt.mp h
  have hrepInf : ContDiffAt Real ∞ rep t := by
    have hcoord := (Bundle.contMDiffAt_totalSpace.mp hYAt).2
    have hcoord' : ContDiffAt Real ∞
        (fun s : Real ↦ (e (TotalSpace.mk' E (alpha s) (Y s))).2) t :=
      contMDiffAt_iff_contDiffAt.mp hcoord
    have hbase : ∀ᶠ s in 𝓝 t, alpha s ∈ e.baseSet :=
      halpha.continuous.continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (alpha t)))
    refine hcoord'.congr_of_eventuallyEq ?_
    filter_upwards [hbase] with s hs
    dsimp only [rep]
    rw [chartRepAtBase_apply]
    change (trivializationAt E (TangentSpace I) (alpha t)).continuousLinearMapAt
        Real (alpha s) (Y s) = _
    rw [(trivializationAt E (TangentSpace I) (alpha t)).continuousLinearMapAt_apply
      (R := Real)]
    rw [(trivializationAt E (TangentSpace I) (alpha t)).coe_linearMapAt_of_mem hs]
  have hdu : ContDiffAt Real ∞ (deriv u) t := by
    have hfd : ContDiffAt Real ∞ (fderiv Real u) t :=
      huInf.fderiv_right (m := ∞) le_rfl
    have happ := hfd.clm_apply (contDiffAt_const (c := (1 : Real)))
    have heq : (fun s ↦ fderiv Real u s (1 : Real)) = deriv u := by
      funext s
      exact fderiv_apply_one_eq_deriv
    rwa [heq] at happ
  have hdrep : ContDiffAt Real ∞ (deriv rep) t := by
    have hfd : ContDiffAt Real ∞ (fderiv Real rep) t :=
      hrepInf.fderiv_right (m := ∞) le_rfl
    have happ := hfd.clm_apply (contDiffAt_const (c := (1 : Real)))
    have heq : (fun s ↦ fderiv Real rep s (1 : Real)) = deriv rep := by
      funext s
      exact fderiv_apply_one_eq_deriv
    rwa [heq] at happ
  have htau : ContDiffAt Real ∞ tau t :=
    contDiffAt_const.sub (contDiffAt_id.pow 2)
  have hGamma (i j k : Fin (Module.finrank Real E)) :
      ContDiffAt Real ∞
        (fun s ↦ chartChristoffel (I := I) (S.family.metric (tau s))
          (alpha t) i j k (u s)) t := by
    have hu_mem : u t ∈ interior (extChartAt I (alpha t)).target :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) (alpha t)
        ((extChartAt I (alpha t)).map_source
          (mem_extChartAt_source (I := I) (alpha t)))
    have hopen : IsOpen
        (D.regular ×ˢ interior (extChartAt I (alpha t)).target) :=
      D.regular_isOpen.prod isOpen_interior
    have hraw := (MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn
      (I := I) (g_fam := S.family.metric) hS.smoothMetric
      (J := D.regular) (fun _ hs ↦ hs) D.regular_isOpen.uniqueDiffOn
      (alpha t) i j k)
    have hpair : (tau t, u t) ∈
        D.regular ×ˢ interior (extChartAt I (alpha t)).target :=
      ⟨htreg, hu_mem⟩
    have hrawAt := hraw.contDiffAt (hopen.mem_nhds hpair)
    let base : Real → Real × E := fun s ↦ (tau s, u s)
    have hbase : ContDiffAt Real ∞ base t := htau.prodMk huInf
    have hcomp := hrawAt.comp t hbase
    with_unfolding_all exact hcomp
  have hchrist : ContDiffAt Real ∞
      (fun s ↦ chartChristoffelContraction (I := I)
        (S.family.metric (tau s)) (alpha t) (deriv u s) (rep s) (u s)) t := by
    unfold chartChristoffelContraction
    refine ContDiffAt.sum fun k _ ↦ ?_
    refine (ContDiffAt.sum fun i _ ↦ ContDiffAt.sum fun j _ ↦ ?_).smul contDiffAt_const
    exact (((hGamma i j k).mul
      (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.contDiff.contDiffAt.comp
        t hdu)).mul
      (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.contDiff.contDiffAt.comp
        t hrepInf))
  have hchart : ContDiffAt Real ∞
      (fun s ↦ chartCovDerivAlong (I := I) (S.base.metric (tau s))
        (alpha t) alpha rep s) t := by
    with_unfolding_all exact hdrep.add hchrist
  apply ContMDiffAt.contMDiffWithinAt
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨halphaAt, ?_⟩
  have hsrc : ∀ᶠ s in 𝓝 t, alpha s ∈ (chartAt H (alpha t)).source :=
    halpha.continuous.continuousAt.preimage_mem_nhds
      ((chartAt H (alpha t)).open_source.mem_nhds (mem_chart_source H (alpha t)))
  have heq :
      (fun s ↦
        (e (TotalSpace.mk' E (alpha s)
          (covDerivAlong (I := I) (S.base.metric (tau s)) alpha Y s))).2)
        =ᶠ[𝓝 t]
      (fun s ↦ chartCovDerivAlong (I := I) (S.base.metric (tau s))
        (alpha t) alpha rep s) := by
    filter_upwards [hsrc, hnhds] with s hs hsOmega
    have hYsAt : ContMDiffAt (modelWithCornersSelf Real Real) I.tangent 2
        (fun r : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha r) (Y r) : TangentBundle I M)) s :=
      ((hY s hsOmega).contMDiffAt (hOmega.mem_nhds hsOmega)).of_le
        (by
          change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hYdiff := differentiableAt_chartRepAt_of_contMDiffAt_two (I := I) hYsAt
    have hinv := covDerivAlong_chart_foot_invariance
      (I := I) (n := (∞ : WithTop ℕ∞)) (by simp)
      (S.base.metric (tau s)) alpha Y s (alpha t) halpha hs hYdiff
    have hbase : alpha s ∈ e.baseSet := by
      simpa only [e, trivializationAt_baseSet_eq_chartAt_source] using hs
    have hcoord :
        (e (TotalSpace.mk' E (alpha s)
          (covDerivAlong (I := I) (S.base.metric (tau s)) alpha Y s))).2 =
          e.continuousLinearMapAt Real (alpha s)
            (covDerivAlong (I := I) (S.base.metric (tau s)) alpha Y s) := by
      symm
      rw [e.continuousLinearMapAt_apply (R := Real)]
      rw [e.coe_linearMapAt_of_mem hbase]
    rw [hcoord, ← hinv]
    exact e.continuousLinearMapAt_symmL (R := Real) hbase _
  exact contMDiffAt_iff_contDiffAt.mpr (hchart.congr_of_eventuallyEq heq)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem movingRicciPair_smooth
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (q : SmoothRiemannianMetric I M)
    (alpha : Real → M)
    (U V : ∀ s, TangentSpace I (alpha s))
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {Omega : Set Real} (hOmega : IsOpen Omega)
    (hU : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (U s) : TangentBundle I M)) Omega)
    (hV : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (V s) : TangentBundle I M)) Omega)
    (hreg : ∀ s ∈ Omega, T - s ^ 2 ∈ D.regular) :
    ContDiffOn Real ∞
      (fun s : Real ↦ q.inner (alpha s) (U s)
        (ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (V s))) Omega := by
  classical
  intro t ht
  have hnhds : Omega ∈ 𝓝 t := hOmega.mem_nhds ht
  let u : Real → E := chartCurve (I := I) (alpha t) alpha
  let urep : Real → E := chartRepAtBase (I := I) (alpha t) alpha U
  let vrep : Real → E := chartRepAtBase (I := I) (alpha t) alpha V
  let tau : Real → Real := fun s ↦ T - s ^ 2
  let coeff : Real → Fin (Module.finrank Real E) → Real := fun s i ↦
    ∑ j : Fin (Module.finrank Real E),
      chartInvGramOnE (I := I) (S.base.metric (tau s)) (alpha t) i j (u s) *
        ∑ k : Fin (Module.finrank Real E),
          chartCoord (E := E) k (vrep s) *
            (let x := (extChartAt I (alpha t)).symm (u s)
             S.ricciAt (tau s) x
               (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (alpha t) k x)
                 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (alpha t) j x)))
  let wrep : Real → E := fun s ↦
    ∑ i : Fin (Module.finrank Real E), coeff s i • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i
  let f : Real → Real := fun s ↦
    ∑ i : Fin (Module.finrank Real E),
      ∑ j : Fin (Module.finrank Real E),
        chartGramOnE (I := I) q (alpha t) i j (u s) *
          chartCoord (E := E) i (urep s) * chartCoord (E := E) j (wrep s)
  have halphaAt : ContMDiffAt (modelWithCornersSelf Real Real) I ∞ alpha t :=
    halpha.contMDiffAt
  have huInf : ContDiffAt Real ∞ u t := by
    have h := (contMDiffAt_extChartAt (I := I) (x := alpha t) (n := ∞)).comp t halphaAt
    exact contMDiffAt_iff_contDiffAt.mp h
  have rep_smooth (W : ∀ s, TangentSpace I (alpha s))
      (hW : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (W s) : TangentBundle I M)) Omega) :
      ContDiffAt Real ∞ (chartRepAtBase (I := I) (alpha t) alpha W) t := by
    let e := trivializationAt E (TangentSpace I : M → Type _) (alpha t)
    have hWAt := (hW t ht).contMDiffAt hnhds
    have hcoord := (Bundle.contMDiffAt_totalSpace.mp hWAt).2
    have hcoord' : ContDiffAt Real ∞
        (fun s : Real ↦ (e (TotalSpace.mk' E (alpha s) (W s))).2) t :=
      contMDiffAt_iff_contDiffAt.mp hcoord
    have hbase : ∀ᶠ s in 𝓝 t, alpha s ∈ e.baseSet :=
      halpha.continuous.continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (alpha t)))
    refine hcoord'.congr_of_eventuallyEq ?_
    filter_upwards [hbase] with s hs
    rw [chartRepAtBase_apply]
    change (trivializationAt E (TangentSpace I) (alpha t)).continuousLinearMapAt
        Real (alpha s) (W s) = _
    rw [(trivializationAt E (TangentSpace I) (alpha t)).continuousLinearMapAt_apply
      (R := Real)]
    rw [(trivializationAt E (TangentSpace I) (alpha t)).coe_linearMapAt_of_mem hs]
  have hurep : ContDiffAt Real ∞ urep t := rep_smooth U hU
  have hvrep : ContDiffAt Real ∞ vrep t := rep_smooth V hV
  have htau : ContDiffAt Real ∞ tau t :=
    contDiffAt_const.sub (contDiffAt_id.pow 2)
  have htreg : tau t ∈ D.regular := hreg t ht
  have hu_mem : u t ∈ interior (extChartAt I (alpha t)).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) (alpha t)
      ((extChartAt I (alpha t)).map_source
        (mem_extChartAt_source (I := I) (alpha t)))
  have hopen : IsOpen
      (D.regular ×ˢ interior (extChartAt I (alpha t)).target) :=
    D.regular_isOpen.prod isOpen_interior
  have hpair : (tau t, u t) ∈
      D.regular ×ˢ interior (extChartAt I (alpha t)).target :=
    ⟨htreg, hu_mem⟩
  let base : Real → Real × E := fun s ↦ (tau s, u s)
  have hbase : ContDiffAt Real ∞ base t := htau.prodMk huInf
  have hinv (i j : Fin (Module.finrank Real E)) : ContDiffAt Real ∞
      (fun s ↦ chartInvGramOnE (I := I) (S.base.metric (tau s))
        (alpha t) i j (u s)) t := by
    have hraw := (MetricFamilySmoothOn.chartInvGramOnE_contDiffOn
      (I := I) (g_fam := S.family.metric) hS.smoothMetric
      (J := D.regular) (fun _ hs ↦ hs) (alpha t) i j).contDiffAt
        (hopen.mem_nhds hpair)
    with_unfolding_all exact hraw.comp t hbase
  have hric (k j : Fin (Module.finrank Real E)) : ContDiffAt Real ∞
      (fun s ↦
        let x := (extChartAt I (alpha t)).symm (u s)
        S.ricciAt (tau s) x
          (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (alpha t) k x)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (alpha t) j x))) t := by
    have hraw := (chartRicci_joint (I := I) S hS (alpha t) k j).contDiffAt
      (hopen.mem_nhds hpair)
    with_unfolding_all exact hraw.comp t hbase
  have hcoordV (k : Fin (Module.finrank Real E)) : ContDiffAt Real ∞
      (fun s ↦ chartCoord (E := E) k (vrep s)) t :=
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord k).toContinuousLinearMap.contDiff.contDiffAt.comp t hvrep
  have hcoeff (i : Fin (Module.finrank Real E)) : ContDiffAt Real ∞
      (fun s ↦ coeff s i) t := by
    dsimp only [coeff]
    exact ContDiffAt.sum fun j _ ↦ (hinv i j).mul
      (ContDiffAt.sum fun k _ ↦ (hcoordV k).mul (hric k j))
  have hwrep : ContDiffAt Real ∞ wrep t := by
    dsimp only [wrep]
    exact ContDiffAt.sum fun i _ ↦ (hcoeff i).smul contDiffAt_const
  have hqgram (i j : Fin (Module.finrank Real E)) : ContDiffAt Real ∞
      (fun s ↦ chartGramOnE (I := I) q (alpha t) i j (u s)) t := by
    have hraw := (chartGramOnE_contDiffOn (I := I) q (alpha t) i j).contDiffAt
      (isOpen_extChartAt_target (alpha t) |>.mem_nhds
        (interior_subset hu_mem))
    exact hraw.comp t huInf
  have hcoordU (i : Fin (Module.finrank Real E)) : ContDiffAt Real ∞
      (fun s ↦ chartCoord (E := E) i (urep s)) t :=
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.contDiff.contDiffAt.comp t hurep
  have hcoordW (j : Fin (Module.finrank Real E)) : ContDiffAt Real ∞
      (fun s ↦ chartCoord (E := E) j (wrep s)) t :=
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.contDiff.contDiffAt.comp t hwrep
  have hf : ContDiffAt Real ∞ f t := by
    dsimp only [f]
    exact ContDiffAt.sum fun i _ ↦ ContDiffAt.sum fun j _ ↦
      ((hqgram i j).mul (hcoordU i)).mul (hcoordW j)
  refine (hf.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hsrc : ∀ᶠ s in 𝓝 t, alpha s ∈ (chartAt H (alpha t)).source :=
    halpha.continuous.continuousAt.preimage_mem_nhds
      ((chartAt H (alpha t)).open_source.mem_nhds (mem_chart_source H (alpha t)))
  filter_upwards [hsrc] with s hs
  let x := alpha s
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) (alpha t)).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hUround :
      (trivializationAt E (TangentSpace I) (alpha t)).symmL Real x (urep s) = U s := by
    simpa only [urep, chartRepAtBase_apply] using
      (trivializationAt E (TangentSpace I) (alpha t)).symmL_continuousLinearMapAt
        (R := Real) hxbase (U s)
  have hu_eq : (extChartAt I (alpha t)).symm (u s) = x := by
    dsimp only [u, chartCurve, x]
    exact (extChartAt I (alpha t)).left_inv
      (by rwa [extChartAt_source_eq_chartAt_source (I := I)])
  have hsharp :
      trivToE (I := I) (alpha t) x
          (ricciSharp (I := I) (S.base.metric (tau s)) x (V s)) = wrep s := by
    rw [ricciSharp_chart (E := E) (I := I)
      (S.base.metric (tau s)) (alpha t) hxbase]
    dsimp only [wrep, coeff]
    simp only [← metricRicciAt_apply_eq_ricciTensor, SolutionOn.ricciAt,
      SolutionFamily.ricciAt, chartInvGramOnE_def, chartCoord_def, vrep,
      chartRepAtBase_apply]
    rw [hu_eq]
  have hRround :
      (trivializationAt E (TangentSpace I) (alpha t)).symmL Real x (wrep s) =
        ricciSharp (I := I) (S.base.metric (tau s)) x (V s) := by
    rw [← hsharp]
    exact (trivializationAt E (TangentSpace I) (alpha t)).symmL_continuousLinearMapAt
      (R := Real) hxbase _
  change q.inner x (U s)
      (ricciSharp (I := I) (S.base.metric (tau s)) x (V s)) = f s
  rw [← hUround, ← hRround]
  rw [inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) q (alpha t)]
  change (∑ i, ∑ j, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) q (alpha t) x i j *
      chartCoord (E := E) i (urep s) * chartCoord (E := E) j (wrep s)) =
    ∑ i, ∑ j, chartGramOnE (I := I) q (alpha t) i j (u s) *
      chartCoord (E := E) i (urep s) * chartCoord (E := E) j (wrep s)
  simp only [chartGramOnE_def, hu_eq]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem adaptCoeff_smooth
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (q : SmoothRiemannianMetric I M)
    (alpha : Real → M)
    (U V : ∀ s, TangentSpace I (alpha s))
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {Omega : Set Real} (hOmega : IsOpen Omega)
    (hU : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (U s) : TangentBundle I M)) Omega)
    (hV : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (V s) : TangentBundle I M)) Omega)
    (hreg : ∀ s ∈ Omega, T - s ^ 2 ∈ D.regular) :
    ContDiffOn Real ∞
      (fun s : Real ↦ q.inner (alpha s) (U s)
        ((-2 * s) •
            ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (V s) -
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha V s)) Omega := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨q.toRiemannianMetric⟩
  have hric := movingRicciPair_smooth (E := E) S hS T q alpha U V halpha
    hOmega hU hV hreg
  have hDV := movingCov_smooth (E := E) S hS T alpha V halpha hOmega hV hreg
  have hcovM := ContMDiffOn.inner_bundle
    (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := alpha) (v := U)
    (w := fun s ↦ covDerivAlong (I := I)
      (S.base.metric (T - s ^ 2)) alpha V s) hU hDV
  have hcov : ContDiffOn Real ∞
      (fun s ↦ q.inner (alpha s) (U s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha V s)) Omega := by
    with_unfolding_all exact hcovM.contDiffOn
  have hscale : ContDiffOn Real ∞ (fun s : Real ↦ -2 * s) Omega :=
    contDiffOn_const.mul contDiffOn_id
  have hsmooth := hscale.mul hric |>.sub hcov
  simpa only [map_sub, sub_apply, map_smul,
    smul_apply, smul_eq_mul] using hsmooth

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private theorem sumField_smooth
    (alpha : Real → M)
    (z : Real → (Fin (Module.finrank Real E) → Real))
    (F : Fin (Module.finrank Real E) → ∀ s, TangentSpace I (alpha s))
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {Omega : Set Real} (hOmega : IsOpen Omega)
    (hz : ContDiffOn Real ∞ z Omega)
    (hF : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (F i s) : TangentBundle I M)) Omega) :
    ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (alpha s)
          (∑ i, z s i • F i s) : TangentBundle I M)) Omega := by
  classical
  intro t ht
  have hnhds : Omega ∈ 𝓝 t := hOmega.mem_nhds ht
  let e := trivializationAt E (TangentSpace I : M → Type _) (alpha t)
  have hcoord (i : Fin (Module.finrank Real E)) : ContDiffAt Real ∞
      (fun s : Real ↦ (e (TotalSpace.mk' E (alpha s) (F i s))).2) t := by
    have hiAt := (hF i t ht).contMDiffAt hnhds
    exact contMDiffAt_iff_contDiffAt.mp (Bundle.contMDiffAt_totalSpace.mp hiAt).2
  have hzi (i : Fin (Module.finrank Real E)) : ContDiffAt Real ∞
      (fun s ↦ z s i) t :=
    (((contDiffOn_pi.mp hz) i) t ht).contDiffAt hnhds
  have hsum : ContDiffAt Real ∞
      (fun s ↦ ∑ i, z s i • (e (TotalSpace.mk' E (alpha s) (F i s))).2) t :=
    ContDiffAt.sum fun i _ ↦ (hzi i).smul (hcoord i)
  apply ContMDiffAt.contMDiffWithinAt
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨halpha.contMDiffAt, ?_⟩
  apply contMDiffAt_iff_contDiffAt.mpr
  refine hsum.congr_of_eventuallyEq ?_
  have hbase : ∀ᶠ s in 𝓝 t, alpha s ∈ e.baseSet :=
    halpha.continuous.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (alpha t)))
  filter_upwards [hbase] with s hs
  change (e (TotalSpace.mk' E (alpha s) (∑ i, z s i • F i s))).2 = _
  have hcoordSum :
      (e (TotalSpace.mk' E (alpha s) (∑ i, z s i • F i s))).2 =
        e.continuousLinearMapAt Real (alpha s) (∑ i, z s i • F i s) := by
    symm
    rw [e.continuousLinearMapAt_apply (R := Real)]
    rw [e.coe_linearMapAt_of_mem hs]
  rw [hcoordSum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul]
  congr 1
  symm
  rw [e.continuousLinearMapAt_apply (R := Real)]
  rw [e.coe_linearMapAt_of_mem hs]

omit [InnerProductSpace Real E] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_parFrame
    (q : SmoothRiemannianMetric I M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {b : Real} (hb : 0 < b) :
    ∃ (eps : Real) (_ : 0 < eps)
      (F : Fin (Module.finrank Real E) → ∀ s, TangentSpace I (alpha s)),
      (∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (F i s) : TangentBundle I M)) (Set.Ioo (-eps) (b + eps))) ∧
      (∀ i, ∀ s ∈ Set.Ioo (-eps) (b + eps),
        DifferentiableAt Real (chartRepAt (I := I) alpha (F i) s) s) ∧
      (∀ i, ∀ s ∈ Set.Ioo (-eps) (b + eps),
        covDerivAlong (I := I) q alpha (F i) s = 0) ∧
      (∀ s ∈ Set.Ioo (-eps) (b + eps), ∀ i j,
        q.inner (alpha s) (F i s) (F j s) = if i = j then 1 else 0) := by
  classical
  obtain ⟨basis, hbasis⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) q (alpha b)
  let beta : Real → M := fun r ↦ alpha (b - r)
  have hbeta : ContMDiff (modelWithCornersSelf Real Real) I ∞ beta := by
    exact halpha.comp (contMDiff_const.sub contMDiff_id)
  have htransport : ∀ i, ∃ (d : Real) (_ : 0 < d)
      (P : ∀ r, TangentSpace I (beta r)),
      P 0 = basis i ∧
      (∀ r ∈ Set.Ioo (-d) (b + d),
        DifferentiableAt Real (chartRepAt (I := I) beta P r) r) ∧
      (∀ r ∈ Set.Ioo (-d) (b + d),
        covDerivAlong (I := I) q beta P r = 0) ∧
      ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun r : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta r) (P r) : TangentBundle I M)) (Set.Ioo (-d) (b + d)) :=
    fun i ↦ parallelTransport_section_contMDiffOn_Ioo
      (I := I) q beta hbeta hb (basis i)
  choose d hd P hP0 hPdiff hPpar hPsmooth using htransport
  obtain ⟨eps, heps, hepsd⟩ :=
    Pi.exists_forall_pos_add_lt (x := fun _ : Fin (Module.finrank Real E) ↦ 0)
      (y := d) (fun i ↦ hd i)
  have heps_lt (i : Fin (Module.finrank Real E)) : eps < d i := by
    simpa only [zero_add] using hepsd i
  let phi : Real → Real := fun s ↦ b - s
  let F : Fin (Module.finrank Real E) → ∀ s, TangentSpace I (alpha s) :=
    fun i s ↦ P i (phi s)
  have hphi : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ phi :=
    contMDiff_const.sub contMDiff_id
  have hphiDiff : Differentiable Real phi :=
    (contMDiff_iff_contDiff.mp hphi).differentiable (by simp)
  have hcurve : (fun s ↦ beta (phi s)) = alpha := by
    funext s
    dsimp only [beta, phi]
    congr 1
    ring
  have hrev (s : Real) (hs : s ∈ Set.Ioo (-eps) (b + eps))
      (i : Fin (Module.finrank Real E)) :
      phi s ∈ Set.Ioo (-(d i)) (b + d i) := by
    dsimp only [phi]
    constructor <;> linarith [hs.1, hs.2, heps_lt i]
  have hFsmooth : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (F i s) : TangentBundle I M)) (Set.Ioo (-eps) (b + eps)) := by
    intro i
    have hcomp := (hPsmooth i).comp hphi.contMDiffOn
      (fun s hs ↦ hrev s hs i)
    have heq :
        ((fun r : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta r) (P i r) : TangentBundle I M)) ∘ phi) =
          (fun s : Real ↦
            (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (alpha s) (F i s) : TangentBundle I M)) := by
      funext s
      simp only [Function.comp_apply, F]
      rw [congrFun hcurve s]
    rwa [heq] at hcomp
  have hFdiff : ∀ i, ∀ s ∈ Set.Ioo (-eps) (b + eps),
      DifferentiableAt Real (chartRepAt (I := I) alpha (F i) s) s := by
    intro i s hs
    have hAt := (hFsmooth i s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)
    exact (differentiableAt_chartRepAt_of_contMDiffAt_two (I := I) (hAt.of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))))
  have hFpar : ∀ i, ∀ s ∈ Set.Ioo (-eps) (b + eps),
      covDerivAlong (I := I) q alpha (F i) s = 0 := by
    intro i s hs
    have hcomp := covDerivAlong_comp (I := I) q beta (P i) phi s
      (hbeta.mdifferentiableAt (by simp)) (hPdiff i (phi s) (hrev s hs i))
      hphiDiff.differentiableAt
    have hzero := hPpar i (phi s) (hrev s hs i)
    rw [hzero, smul_zero] at hcomp
    rw [hcurve] at hcomp
    exact hcomp
  have hFON : ∀ s ∈ Set.Ioo (-eps) (b + eps), ∀ i j,
      q.inner (alpha s) (F i s) (F j s) = if i = j then 1 else 0 := by
    intro s hs i j
    let r := phi s
    let lo := min 0 r
    let hi := max 0 r
    have hr_mem : r ∈ Set.Icc lo hi := ⟨min_le_right _ _, le_max_right _ _⟩
    have h0_mem : (0 : Real) ∈ Set.Icc lo hi :=
      ⟨min_le_left _ _, le_max_left _ _⟩
    have hseg : Set.Icc lo hi ⊆ Set.Ioo (-(d i)) (b + d i) := by
      intro z hz
      have hrange := hrev s hs i
      dsimp only [lo, hi] at hz
      rcases le_total 0 r with hr | hr
      · rw [min_eq_left hr, max_eq_right hr] at hz
        constructor <;> linarith [hz.1, hz.2, hrange.1, hrange.2, hd i]
      · rw [min_eq_right hr, max_eq_left hr] at hz
        constructor <;> linarith [hz.1, hz.2, hrange.1, hrange.2, hd i]
    have hsegj : Set.Icc lo hi ⊆ Set.Ioo (-(d j)) (b + d j) := by
      intro z hz
      have hrange := hrev s hs j
      dsimp only [lo, hi] at hz
      rcases le_total 0 r with hr | hr
      · rw [min_eq_left hr, max_eq_right hr] at hz
        constructor <;> linarith [hz.1, hz.2, hrange.1, hrange.2, hd j]
      · rw [min_eq_right hr, max_eq_left hr] at hz
        constructor <;> linarith [hz.1, hz.2, hrange.1, hrange.2, hd j]
    have hconst := parallel_transport_preserves_inner_product (I := I) q beta
      (N := 2) le_rfl (hbeta.of_le (by exact_mod_cast le_top)) (P i) (P j)
      (fun z hz ↦ hPdiff i z (hseg hz))
      (fun z hz ↦ hPdiff j z (hsegj hz))
      (fun z hz ↦ hPpar i z (hseg hz))
      (fun z hz ↦ hPpar j z (hsegj hz))
    have hr_eq := hconst r hr_mem
    have h0_eq := hconst 0 h0_mem
    have hrbase : beta r = alpha s := by
      dsimp only [r, beta, phi]
      congr 1
      ring
    dsimp only [F]
    rw [← hrbase]
    rw [hr_eq, ← h0_eq, hP0 i, hP0 j]
    have hbeta0 : beta 0 = alpha b := by
      dsimp only [beta]
      congr 1
      ring
    rw [hbeta0]
    exact hbasis i j
  exact ⟨eps, heps, F, hFsmooth, hFdiff, hFpar, hFON⟩

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
theorem exists_lAdaptedField
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {a b c : Real} (ha : a < 0) (hb : 0 < b) (hc : b < c)
    (hreg : ∀ s ∈ Set.Ioo a c, T - s ^ 2 ∈ D.regular)
    (V : TangentSpace I (alpha b)) :
    ∃ (P : ∀ s, TangentSpace I (alpha s)) (Omega' : Set Real),
      IsOpen Omega' ∧ Set.Icc 0 b ⊆ Omega' ∧ Omega' ⊆ Set.Ioo a c ∧
      ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (P s) : TangentBundle I M)) Omega' ∧
      P b = V ∧
      IsLAdapted S T alpha P Omega' := by
  classical
  let q := S.base.metric (T - b ^ 2)
  obtain ⟨eps, heps, F, hFsmooth0, hFdiff0, hFpar0, hFON0⟩ :=
    exists_parFrame (E := E) q alpha halpha hb
  let rho : Real := min eps (min (-a) (c - b))
  let eta : Real := rho / 2
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min heps (lt_min (neg_pos.mpr ha) (sub_pos.mpr hc))
  have heta : 0 < eta := by
    dsimp only [eta]
    linarith
  have heta_eps : eta < eps := by
    dsimp only [eta, rho]
    have hhalf : min eps (min (-a) (c - b)) / 2 <
        min eps (min (-a) (c - b)) := by linarith [hrho]
    exact hhalf.trans_le (min_le_left _ _)
  have heta_a : eta < -a := by
    dsimp only [eta, rho]
    have hhalf : min eps (min (-a) (c - b)) / 2 <
        min eps (min (-a) (c - b)) := by linarith [hrho]
    exact hhalf.trans_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have heta_c : eta < c - b := by
    dsimp only [eta, rho]
    have hhalf : min eps (min (-a) (c - b)) / 2 <
        min eps (min (-a) (c - b)) := by linarith [hrho]
    exact hhalf.trans_le (le_trans (min_le_right _ _) (min_le_right _ _))
  let Omega' : Set Real := Set.Ioo (-eta) (b + eta)
  have hOmega : IsOpen Omega' := isOpen_Ioo
  have hIcc : Set.Icc (0 : Real) b ⊆ Omega' := by
    intro s hs
    dsimp only [Omega']
    constructor <;> linarith [hs.1, hs.2, heta]
  have hOmegaReg : Omega' ⊆ Set.Ioo a c := by
    intro s hs
    dsimp only [Omega'] at hs
    constructor <;> linarith [hs.1, hs.2, heta_a, heta_c]
  have hOmegaFrame : Omega' ⊆ Set.Ioo (-eps) (b + eps) := by
    intro s hs
    dsimp only [Omega'] at hs
    constructor <;> linarith [hs.1, hs.2, heta_eps]
  have hFsmooth (i : Fin (Module.finrank Real E)) :=
    (hFsmooth0 i).mono hOmegaFrame
  have hFdiff (i : Fin (Module.finrank Real E)) (s : Real) (hs : s ∈ Omega') :=
    hFdiff0 i s (hOmegaFrame hs)
  have hFON (s : Real) (hs : s ∈ Omega') (i j : Fin (Module.finrank Real E)) :=
    hFON0 s (hOmegaFrame hs) i j
  let aij : Real → Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun s i j ↦ q.inner (alpha s) (F i s)
      ((-2 * s) •
          ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (F j s) -
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha (F j) s)
  have haij (i j : Fin (Module.finrank Real E)) :
      ContDiffOn Real ∞ (fun s ↦ aij s i j) Omega' := by
    simpa only [aij] using adaptCoeff_smooth (E := E) S hS T q alpha
      (F i) (F j) halpha hOmega (hFsmooth i) (hFsmooth j)
      (fun s hs ↦ hreg s (hOmegaReg hs))
  let amat : Real → Matrix (Fin (Module.finrank Real E))
      (Fin (Module.finrank Real E)) Real := fun s i j ↦ aij s i j
  let A : Unit → Real →
      ((Fin (Module.finrank Real E) → Real) →L[Real]
        (Fin (Module.finrank Real E) → Real)) := fun _ s ↦
    (Matrix.toLin' (amat s)).toContinuousLinearMap
  have hA : ContDiffOn Real ∞ (Function.uncurry A)
      (Set.univ ×ˢ Omega') := by
    rw [contDiffOn_clm_apply]
    intro z
    rw [contDiffOn_pi]
    intro i
    change ContDiffOn Real ∞
      (fun p : Unit × Real ↦ ∑ j, aij p.2 i j * z j) (Set.univ ×ˢ Omega')
    exact ContDiffOn.sum fun j _ ↦
      ((haij i j).comp contDiffOn_snd (fun p hp ↦ hp.2)).mul contDiffOn_const
  have hbmem : b ∈ Set.Ioo (-eta) (b + eta) := by
    constructor <;> linarith [hb, heta]
  let z0 : Unit → (Fin (Module.finrank Real E) → Real) := fun _ i ↦
    q.inner (alpha b) (F i b) V
  have hz0 : ContDiffOn Real ∞ z0 Set.univ := contDiffOn_const
  have hA' : ContDiffOn Real ∞ (Function.uncurry A)
      (Set.univ ×ˢ Set.Ioo (-eta) (b + eta)) := by
    simpa only [Omega'] using hA
  let z : Real → (Fin (Module.finrank Real E) → Real) := fun s ↦
    linearODESolution A (-eta) (b + eta) b z0 () s
  have hzRaw := linearODESolution_contDiffOn_top hbmem isOpen_univ hA' hz0
  have hz : ContDiffOn Real ∞ z Omega' := by
    have hpair : ContDiff Real ∞ (fun s : Real ↦ ((), s)) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := hzRaw.comp hpair.contDiffOn
      (fun s hs ↦ ⟨Set.mem_univ (), by simpa only [Omega'] using hs⟩)
    change ContDiffOn Real ∞
      (fun s ↦ linearODESolution A (-eta) (b + eta) b z0 () s) Omega' at hcomp
    exact hcomp
  let P : ∀ s, TangentSpace I (alpha s) := fun s ↦
    ∑ i : Fin (Module.finrank Real E), z s i • F i s
  have hPsmooth : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (P s) : TangentBundle I M)) Omega' := by
    simpa only [P] using
      sumField_smooth (E := E) alpha z F halpha hOmega hz hFsmooth
  have hzb : z b = z0 () := by
    exact linearODESolution_init A (-eta) (b + eta) b z0 ()
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I (alpha b)) := by
    rw [Fintype.card_fin]
    rfl
  have hPb : P b = V := by
    dsimp only [P]
    rw [hzb]
    dsimp only [z0]
    exact (Geometry.Riemannian.expand_orthonormal q (alpha b) hcard
      (fun i ↦ F i b) (hFON b (hIcc ⟨le_of_lt hb, le_rfl⟩)) V).symm
  refine ⟨P, Omega', hOmega, hIcc, hOmegaReg, hPsmooth, hPb, ?_⟩
  intro s hs
  change covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha P s =
    (-2 * s) •
      ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (P s)
  let g := S.base.metric (T - s ^ 2)
  have hsIoo : s ∈ Set.Ioo (-eta) (b + eta) := by
    simpa only [Omega'] using hs
  have hzDeriv : HasDerivAt z (A () s (z s)) s := by
    simpa only [z] using linearODESolution_hasDerivAt hbmem
      hA'.continuousOn (Set.mem_univ ()) hsIoo
  have hziDiff (i : Fin (Module.finrank Real E)) :
      DifferentiableAt Real (fun r ↦ z r i) s :=
    ((((contDiffOn_pi.mp hz) i).differentiableOn (by simp)) s hs).differentiableAt
      (hOmega.mem_nhds hs)
  have hziDeriv (i : Fin (Module.finrank Real E)) :
      deriv (fun r ↦ z r i) s = (A () s (z s)) i := by
    exact ((hasDerivAt_pi.mp hzDeriv) i).deriv
  have htermDiff (i : Fin (Module.finrank Real E)) : DifferentiableAt Real
      (chartRepAt (I := I) alpha (fun r ↦ z r i • F i r) s) s := by
    rw [chartRepAt_smulFun]
    exact (hziDiff i).smul (hFdiff i s hs)
  have hAapply (i : Fin (Module.finrank Real E)) :
      (A () s (z s)) i = ∑ j, aij s i j * z s j := by
    rfl
  have hDP : covDerivAlong (I := I) g alpha P s =
      ∑ i : Fin (Module.finrank Real E), (
        (∑ j, aij s i j * z s j) • F i s +
          z s i • covDerivAlong (I := I) g alpha (F i) s) := by
    dsimp only [P]
    rw [covDerivAlong_sum (I := I) g alpha Finset.univ
      (fun i r ↦ z r i • F i r) s (fun i _ ↦ htermDiff i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [covDerivAlong_smulFun (I := I) g alpha (fun r ↦ z r i) (F i) s
      (hziDiff i) (hFdiff i s hs), hziDeriv i, hAapply i]
  let B : Fin (Module.finrank Real E) → TangentSpace I (alpha s) := fun j ↦
    (-2 * s) • ricciSharp (I := I) g (alpha s) (F j s) -
      covDerivAlong (I := I) g alpha (F j) s
  have hcard_s : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I (alpha s)) := by
    rw [Fintype.card_fin]
    rfl
  have hBexp (j : Fin (Module.finrank Real E)) :
      B j = ∑ i, aij s i j • F i s := by
    have hexp := Geometry.Riemannian.expand_orthonormal q (alpha s) hcard_s
      (fun i ↦ F i s) (hFON s hs) (B j)
    rw [hexp]
  have hswap :
      (∑ i : Fin (Module.finrank Real E),
        (∑ j, aij s i j * z s j) • F i s) =
      ∑ j : Fin (Module.finrank Real E), z s j •
        (∑ i, aij s i j • F i s) := by
    simp_rw [Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    module
  rw [hDP, Finset.sum_add_distrib, hswap]
  have hcols : (∑ j : Fin (Module.finrank Real E), z s j •
      (∑ i, aij s i j • F i s)) = ∑ j, z s j • B j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hBexp j]
  rw [hcols]
  dsimp only [B, g]
  dsimp only [P]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, sub_add_cancel]
  rw [map_sum]
  simp_rw [map_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm]

end DifferentialGeometry.PDE.RicciFlow.Perelman
