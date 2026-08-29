import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.JointRegularity
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SInnerSectionContinuity
import DifferentialGeometry.Analysis.ODE.Flow.SolutionOperator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set Filter
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
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

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem lRegJacCLM_cont
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x0 : M)
    (K : Set Real) (alpha : Real → M) (a : Real → E)
    (halpha : Continuous (fun z : {s : Real // s ∈ K} ↦ alpha z))
    (ha : Continuous (fun z : {s : Real // s ∈ K} ↦ a z))
    (hsrc : ∀ s ∈ K, alpha s ∈ (chartAt H x0).source)
    (hreg : ∀ s ∈ K, T - s ^ 2 ∈ D.regular) :
    Continuous (fun z : {s : Real // s ∈ K} ↦
      lRegJacobiCLM S T z x0 (alpha z)
        (trivFromE (I := I) x0 (alpha z) (a z)) (a z)
        (chartCurve (I := I) x0 alpha z)) := by
  classical
  let P := {s : Real // s ∈ K}
  let tau : P → Real := fun z ↦ T - (z : Real) ^ 2
  let b : P → M := fun z ↦ alpha z
  let u : P → E := fun z ↦ chartCurve (I := I) x0 alpha z
  let e := trivializationAt E (TangentSpace I : M → Type _) x0
  have hz : Continuous (fun z : P ↦ (z : Real)) := continuous_subtype_val
  have htau : Continuous tau := by
    have hraw : Continuous
        ((fun _ : P ↦ T) - (fun z : P ↦ (z : Real)) ^ 2) :=
      continuous_const.sub (hz.pow 2)
    have hfun : (fun _ : P ↦ T) - (fun z : P ↦ (z : Real)) ^ 2 = tau := by
      funext z
      rfl
    rw [hfun] at hraw
    exact hraw
  have hb : Continuous b := by
    simpa only [b, P] using halpha
  have hbase (z : P) : b z ∈ e.baseSet := by
    rw [show e.baseSet = (chartAt H x0).source by
      simpa only [e] using
        trivializationAt_baseSet_eq_chartAt_source (I := I) x0]
    exact hsrc z z.2
  have hbext (z : P) : b z ∈ (extChartAt I x0).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hsrc z z.2
  have hu : Continuous u := by
    have h := (continuousOn_extChartAt (I := I) x0).comp_continuous hb
      (fun z ↦ hbext z)
    have hfun : (extChartAt I x0) ∘ b = u := by
      funext z
      rfl
    rw [hfun] at h
    exact h
  have hu_mem (z : P) : u z ∈ interior (extChartAt I x0).target := by
    apply extChartAt_target_subset_interior_of_boundaryless (I := I) x0
    simpa only [u, b, chartCurve] using (extChartAt I x0).map_source (hbext z)
  have hcoord (z : P) : (extChartAt I x0).symm (u z) = b z := by
    simpa only [u, b, chartCurve] using (extChartAt I x0).left_inv (hbext z)
  have hsec (v : P → E) (hv : Continuous v) :
      Continuous (fun z : P ↦
        (TotalSpace.mk' E (b z) (trivFromE (I := I) x0 (b z) (v z)) :
          TangentBundle I M)) := by
    have hp : Continuous (fun z : P ↦ (b z, v z)) := hb.prodMk hv
    have hm : MapsTo (fun z : P ↦ (b z, v z)) Set.univ
        (e.baseSet ×ˢ (Set.univ : Set E)) := by
      intro z _
      exact ⟨hbase z, Set.mem_univ _⟩
    have htot := e.continuousOn_symm.comp hp.continuousOn hm
    have htot' := continuousOn_univ.mp htot
    have hfun :
        (fun z : M × E ↦
          (e.symm z.1 z.2 : TotalSpace E (TangentSpace I : M → Type _))) ∘
            (fun z : P ↦ (b z, v z)) =
          (fun z : P ↦
            (TotalSpace.mk' E (b z) (trivFromE (I := I) x0 (b z) (v z)) :
              TangentBundle I M)) := by
      funext z
      change (TotalSpace.mk' E (b z) (e.symm (b z) (v z)) :
          TangentBundle I M) =
        TotalSpace.mk' E (b z) (trivFromE (I := I) x0 (b z) (v z))
      change (TotalSpace.mk' E (b z) (e.symm (b z) (v z)) :
          TangentBundle I M) =
        TotalSpace.mk' E (b z) (e.symmL Real (b z) (v z))
      rw [e.symmL_apply (hbase z)]
    rw [hfun] at htot'
    exact htot'
  let A : (z : P) → TangentSpace I (b z) := fun z ↦
    trivFromE (I := I) x0 (b z) (a z)
  let Yv : (E × E) → ((z : P) → TangentSpace I (b z)) := fun Z z ↦
    trivFromE (I := I) x0 (b z) Z.1
  let Pv : (E × E) → ((z : P) → TangentSpace I (b z)) := fun Z z ↦
    trivFromE (I := I) x0 (b z) Z.2
  let Wv : Fin (Module.finrank Real E) →
      ((z : P) → TangentSpace I (b z)) := fun j z ↦
    trivFromE (I := I) x0 (b z) (chartModelBasis E j)
  have hAsec : Continuous (fun z : P ↦
      (TotalSpace.mk' E (b z) (A z) : TangentBundle I M)) := by
    simpa only [A] using hsec (fun z ↦ a z) (by simpa only [P] using ha)
  have hYsec (Z : E × E) : Continuous (fun z : P ↦
      (TotalSpace.mk' E (b z) (Yv Z z) : TangentBundle I M)) := by
    simpa only [Yv] using hsec (fun _ ↦ Z.1) continuous_const
  have hPsec (Z : E × E) : Continuous (fun z : P ↦
      (TotalSpace.mk' E (b z) (Pv Z z) : TangentBundle I M)) := by
    simpa only [Pv] using hsec (fun _ ↦ Z.2) continuous_const
  have hWsec (j : Fin (Module.finrank Real E)) : Continuous (fun z : P ↦
      (TotalSpace.mk' E (b z) (Wv j z) : TangentBundle I M)) := by
    simpa only [Wv] using hsec (fun _ ↦ chartModelBasis E j) continuous_const
  have hRm (Z : E × E) (j : Fin (Module.finrank Real E)) :
      Continuous (fun z : P ↦ S.base.rm04 (tau z) (b z)
        (vec4 (Yv Z z) (A z) (A z) (Wv j z))) := by
    apply hS.rm04Cont.eval_continuous (P := P) htau
      (fun z ↦ D.regular_subset (hreg z z.2)) hb
    intro i
    fin_cases i
    · with_unfolding_all exact (hYsec Z)
    · with_unfolding_all exact hAsec
    · with_unfolding_all exact hAsec
    · with_unfolding_all exact (hWsec j)
  have hHess (Z : E × E) (j : Fin (Module.finrank Real E)) :
      Continuous (fun z : P ↦
        hessianSec (I := I) (S.base.connection (tau z))
          (metricCov_smooth (I := I) (S.base.metric (tau z)))
          (S.scalar (tau z)) (scalarSmoothOfSol (I := I) S (tau z)) (b z)
          (vec2 (Yv Z z) (Wv j z))) := by
    apply (scalarHess_cont (I := I) S hS).eval_continuous
      (P := P) htau (fun z ↦ hreg z z.2) hb
    intro i
    fin_cases i
    · with_unfolding_all exact (hYsec Z)
    · with_unfolding_all exact (hWsec j)
  have hRic (Z : E × E) (j : Fin (Module.finrank Real E)) :
      Continuous (fun z : P ↦
        S.ricciAt (tau z) (b z) (vec2 (Pv Z z) (Wv j z))) := by
    have h := hS.ricciCont.eval_continuous (P := P) htau
      (fun z ↦ D.regular_subset (hreg z z.2)) hb (v := fun i z ↦
        vec2 (Pv Z z) (Wv j z) i) (by
          intro i
          fin_cases i
          · with_unfolding_all exact (hPsec Z)
          · with_unfolding_all exact (hWsec j))
    simpa only [SolutionOn.ricciAt, SolutionOn.ricci,
      SolutionFamily.ricci_apply] using h
  have hCov (Z : E × E) (j : Fin (Module.finrank Real E)) :
      Continuous (fun z : P ↦
        lRegJacobiCov S T z (b z) (Yv Z z) (A z) (Pv Z z) (Wv j z)) := by
    have h0 := hRm Z j
    have h1 := hHess Z j
    have h2 := hRic Z j
    have h3 : Continuous (fun z : P ↦ totalNabla0SFun (𝕜 := Real) (I := I) 2
        (S.base.connection (tau z)) (S.ricci (tau z)) (b z)
        (vec3 (A z) (Yv Z z) (Wv j z))) := by
      apply (nablaRicci_cont (I := I) S hS).eval_continuous
        (P := P) htau (fun z ↦ hreg z z.2) hb
      intro i
      fin_cases i
      · with_unfolding_all exact hAsec
      · with_unfolding_all exact (hYsec Z)
      · with_unfolding_all exact (hWsec j)
    have h4 : Continuous (fun z : P ↦ totalNabla0SFun (𝕜 := Real) (I := I) 2
        (S.base.connection (tau z)) (S.ricci (tau z)) (b z)
        (vec3 (Yv Z z) (A z) (Wv j z))) := by
      apply (nablaRicci_cont (I := I) S hS).eval_continuous
        (P := P) htau (fun z ↦ hreg z z.2) hb
      intro i
      fin_cases i
      · with_unfolding_all exact (hYsec Z)
      · with_unfolding_all exact hAsec
      · with_unfolding_all exact (hWsec j)
    have h5 : Continuous (fun z : P ↦ totalNabla0SFun (𝕜 := Real) (I := I) 2
        (S.base.connection (tau z)) (S.ricci (tau z)) (b z)
        (vec3 (Wv j z) (A z) (Yv Z z))) := by
      apply (nablaRicci_cont (I := I) S hS).eval_continuous
        (P := P) htau (fun z ↦ hreg z z.2) hb
      intro i
      fin_cases i
      · with_unfolding_all exact (hWsec j)
      · with_unfolding_all exact hAsec
      · with_unfolding_all exact (hYsec Z)
    have hs : Continuous (fun z : P ↦ (z : Real)) := continuous_subtype_val
    have hc2 : Continuous (fun z : P ↦ 2 * (z : Real) ^ 2) :=
      continuous_const.mul (hs.pow 2)
    have hc4 : Continuous (fun z : P ↦ 4 * (z : Real)) :=
      continuous_const.mul hs
    have hc2s : Continuous (fun z : P ↦ 2 * (z : Real)) :=
      continuous_const.mul hs
    have hall := (((((h0.neg.add
      (hc2.mul h1)).sub (hc4.mul h2)).add (hc2s.mul h3)).sub
        (hc2s.mul h4)).sub (hc2s.mul h5))
    rw [show (fun z : P ↦
        lRegJacobiCov S T z (b z) (Yv Z z) (A z) (Pv Z z) (Wv j z)) =
      fun z : P ↦
        -S.base.rm04 (tau z) (b z)
            (vec4 (Yv Z z) (A z) (A z) (Wv j z)) +
          2 * (z : Real) ^ 2 *
            hessianSec (I := I) (S.base.connection (tau z))
              (metricCov_smooth (I := I) (S.base.metric (tau z)))
              (S.scalar (tau z)) (scalarSmoothOfSol (I := I) S (tau z)) (b z)
              (vec2 (Yv Z z) (Wv j z)) -
          4 * (z : Real) *
            S.ricciAt (tau z) (b z) (vec2 (Pv Z z) (Wv j z)) +
          2 * (z : Real) * totalNabla0SFun (𝕜 := Real) (I := I) 2
            (S.base.connection (tau z)) (S.ricci (tau z)) (b z)
            (vec3 (A z) (Yv Z z) (Wv j z)) -
          2 * (z : Real) * totalNabla0SFun (𝕜 := Real) (I := I) 2
            (S.base.connection (tau z)) (S.ricci (tau z)) (b z)
            (vec3 (Yv Z z) (A z) (Wv j z)) -
          2 * (z : Real) * totalNabla0SFun (𝕜 := Real) (I := I) 2
            (S.base.connection (tau z)) (S.ricci (tau z)) (b z)
            (vec3 (Wv j z) (A z) (Yv Z z)) by
        funext z
        simpa only [tau] using
          lRegJacobiCov_apply (I := I) S T z (b z)
            (Yv Z z) (A z) (Pv Z z) (Wv j z)]
    exact hall
  have hInv (i j : Fin (Module.finrank Real E)) :
      Continuous (fun z : P ↦
        chartInvGramMatrix (I := I) (S.base.metric (tau z)) x0 (b z) i j) := by
    have hraw := MetricFamilySmoothOn.chartInvGramOnE_continuousOn
      (I := I) (G := S.family) hS.smoothMetric
      (J := D.regular) (fun _ ht ↦ ht) x0 i j
    have hcomp := hraw.comp_continuous (htau.prodMk hu)
      (fun z ↦ ⟨hreg z z.2, hu_mem z⟩)
    refine hcomp.congr (fun z ↦ ?_)
    change chartInvGramMatrix (I := I) (S.family.metric (tau z)) x0
        ((extChartAt I x0).symm (u z)) i j =
      chartInvGramMatrix (I := I) (S.base.metric (tau z)) x0 (b z) i j
    rw [hcoord z]
    rfl
  have hForce (Z : E × E) : Continuous (fun z : P ↦
      lRegForceChart S T z x0 (b z) (A z) Z) := by
    have hsum : Continuous (fun z : P ↦
        ∑ i : Fin (Module.finrank Real E),
          (∑ j : Fin (Module.finrank Real E),
            chartInvGramMatrix (I := I) (S.base.metric (tau z)) x0 (b z) i j *
              lRegJacobiCov S T z (b z) (Yv Z z) (A z) (Pv Z z) (Wv j z)) •
            chartModelBasis E i) := by
      refine continuous_finsetSum _ (fun i _ ↦ ?_)
      refine (continuous_finsetSum _ (fun j _ ↦
        (hInv i j).mul (hCov Z j))).smul continuous_const
    refine hsum.congr (fun z ↦ ?_)
    symm
    rw [lRegForceChart_apply]
    let cv : ∀ x : M, TangentSpace I x →ₗ[Real] Real := fun x ↦
      lRegJacobiCov S T z x
        (trivFromE (I := I) x0 x Z.1)
        (trivFromE (I := I) x0 x (a z))
        (trivFromE (I := I) x0 x Z.2)
    change trivToE (I := I) x0 (b z)
        (metricSharp (I := I) (S.base.metric (tau z)) (b z) (cv (b z))) = _
    have hsharp := trivToE_metricSharp (I := I)
      (S.base.metric (tau z)) x0 cv (hbase z)
    with_unfolding_all exact hsharp
  have haCoord (i : Fin (Module.finrank Real E)) :
      Continuous (fun z : P ↦
        Geometry.Riemannian.Geodesic.chartCoord (E := E) i (a z)) := by
    exact (((chartModelBasis E).coord i).toContinuousLinearMap.continuous).comp
      (by simpa only [P] using ha)
  have hGamma (i j k : Fin (Module.finrank Real E)) :
      Continuous (fun z : P ↦ chartChristoffel (I := I)
        (S.base.metric (tau z)) x0 i j k (u z)) := by
    have hraw := MetricFamilySmoothOn.chartChristoffelOnE_continuousOn
      (I := I) (G := S.family) hS.smoothMetric
      (J := D.regular) (fun _ ht ↦ ht) D.regular_isOpen.uniqueDiffOn x0 i j k
    have hcomp := hraw.comp_continuous (htau.prodMk hu)
      (fun z ↦ ⟨hreg z z.2, hu_mem z⟩)
    have hfun :
        (fun p : Real × E ↦ chartChristoffel (I := I)
          (S.base.metric p.1) x0 i j k p.2) ∘ (fun z : P ↦ (tau z, u z)) =
        (fun z : P ↦ chartChristoffel (I := I)
          (S.base.metric (tau z)) x0 i j k (u z)) := by
      rfl
    simp only [SolutionOn.family_metric] at hcomp
    rw [hfun] at hcomp
    exact hcomp
  have hGApp (w : E) : Continuous (fun z : P ↦
      Geometry.Riemannian.Geodesic.chartChristoffelContraction (I := I)
        (S.base.metric (tau z)) x0 (a z) w (u z)) := by
    unfold Geometry.Riemannian.Geodesic.chartChristoffelContraction
    refine continuous_finsetSum _ (fun k _ ↦ ?_)
    refine (continuous_finsetSum _ (fun i _ ↦
      continuous_finsetSum _ (fun j _ ↦ ?_))).smul continuous_const
    exact ((hGamma i j k).mul (haCoord i)).mul continuous_const
  have hEval (Z : E × E) : Continuous (fun z : P ↦
      lRegJacobiCLM S T z x0 (b z) (A z) (a z) (u z) Z) := by
    rw [show (fun z : P ↦
        lRegJacobiCLM S T z x0 (b z) (A z) (a z) (u z) Z) =
      fun z : P ↦
        (Z.2 - Geometry.Riemannian.Geodesic.chartChristoffelContraction
            (I := I) (S.base.metric (tau z)) x0 (a z) Z.1 (u z),
          lRegForceChart S T z x0 (b z) (A z) Z -
            Geometry.Riemannian.Geodesic.chartChristoffelContraction
              (I := I) (S.base.metric (tau z)) x0 (a z) Z.2 (u z)) by
        funext z
        simpa only [tau] using
          lRegJacobiCLM_apply (I := I) S T z x0 (b z) (A z) (a z) (u z) Z]
    exact (continuous_const.sub (hGApp Z.1)).prodMk
      ((hForce Z).sub (hGApp Z.2))
  rw [continuous_iff_continuousAt]
  intro z
  refine DifferentialGeometry.Tensor.Tensor0SInnerSectionContinuity.continuousAt_clm_of_basis_continuousAt
      (v := Module.finBasis Real (E × E)) ?_
  intro i
  exact (hEval (Module.finBasis Real (E × E) i)).continuousAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lRegJacobi_unique
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {alpha : Real → M} {Y Y' : ∀ s, TangentSpace I (alpha s)}
    {J : Set Real} {s0 : Real}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J) (hs0 : s0 ∈ J)
    (hreg : ∀ s ∈ J, T - s ^ 2 ∈ D.regular)
    (hvel : ∀ s ∈ J, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : IsLRegJacobi S T alpha Y J)
    (hY' : IsLRegJacobi S T alpha Y' J)
    (h0 : Y s0 = Y' s0)
    (hD0 : covDerivAlong (I := I) (S.base.metric (T - s0 ^ 2)) alpha Y s0 =
      covDerivAlong (I := I) (S.base.metric (T - s0 ^ 2)) alpha Y' s0) :
    Set.EqOn Y Y' J := by
  classical
  let A : ∀ s, TangentSpace I (alpha s) := fun s ↦
    lVelocity (I := I) alpha s
  let P : ∀ s, TangentSpace I (alpha s) := fun s ↦
    covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s
  let P' : ∀ s, TangentSpace I (alpha s) := fun s ↦
    covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y' s
  let za : Real → TangentBundle I M × TangentBundle I M := fun s ↦
    (TotalSpace.mk' E (alpha s) (Y s), TotalSpace.mk' E (alpha s) (P s))
  let zb : Real → TangentBundle I M × TangentBundle I M := fun s ↦
    (TotalSpace.mk' E (alpha s) (Y' s), TotalSpace.mk' E (alpha s) (P' s))
  let U : Set Real := {s | za s = zb s} ∩ J
  have halpha : ContinuousOn alpha J := by
    intro s hs
    exact (hY s hs).1.continuousAt.continuousWithinAt
  have hPgerm (V : ∀ s, TangentSpace I (alpha s))
      (hV : IsLRegJacobi S T alpha V J) (s : Real) (hs : s ∈ J) :
      DifferentiableAt Real
        (chartRepAt (I := I) alpha
          (fun r ↦ covDerivAlong (I := I)
            (S.base.metric (T - r ^ 2)) alpha V r) s) s := by
    apply lRegJacobiVel_diff (I := I) S hS T alpha V s (hreg s hs)
    · filter_upwards [hJopen.mem_nhds hs] with r hr
      exact (hV r hr).1
    · exact (hV s hs).2.1
    · simpa only [A] using hvel s hs
    · exact (hV s hs).2.2.1
  have hza : ContinuousOn za J := by
    apply ContinuousOn.prodMk
    · apply sectionAlongCurve_continuousOn_totalSpace (I := I) alpha Y halpha
      intro s hs
      exact (hY s hs).2.1
    · apply sectionAlongCurve_continuousOn_totalSpace (I := I) alpha P halpha
      intro s hs
      simpa only [P] using hPgerm Y hY s hs
  have hzb : ContinuousOn zb J := by
    apply ContinuousOn.prodMk
    · apply sectionAlongCurve_continuousOn_totalSpace (I := I) alpha Y' halpha
      intro s hs
      exact (hY' s hs).2.1
    · apply sectionAlongCurve_continuousOn_totalSpace (I := I) alpha P' halpha
      intro s hs
      simpa only [P'] using hPgerm Y' hY' s hs
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hsJ : s ∈ J := hs.2
    let x0 := alpha s
    have hsrcs : alpha s ∈ (chartAt H x0).source := by
      exact mem_chart_source H (alpha s)
    have hpre : alpha ⁻¹' (chartAt H x0).source ∈ nhds s :=
      (hY s hsJ).1.continuousAt.preimage_mem_nhds
        ((chartAt H x0).open_source.mem_nhds hsrcs)
    obtain ⟨c, d, hscd, hcd⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (inter_mem (hJopen.mem_nhds hsJ) hpre)
    let y := chartRepAtBase (I := I) x0 alpha Y
    let y' := chartRepAtBase (I := I) x0 alpha Y'
    let a := chartRepAtBase (I := I) x0 alpha A
    let p := chartRepAtBase (I := I) x0 alpha P
    let p' := chartRepAtBase (I := I) x0 alpha P'
    let z : Real → E × E := fun r ↦ (y r, p r)
    let z' : Real → E × E := fun r ↦ (y' r, p' r)
    let C : Real → (E × E →L[Real] E × E) := fun r ↦
      lRegJacobiCLM S T r x0 (alpha r) (A r) (a r)
        (chartCurve (I := I) x0 alpha r)
    have hsubJ : Ioo c d ⊆ J := fun r hr ↦ (hcd hr).1
    have hsrc : ∀ r ∈ Ioo c d, alpha r ∈ (chartAt H x0).source :=
      fun r hr ↦ (hcd hr).2
    have halphaI : ContinuousOn alpha (Ioo c d) := halpha.mono hsubJ
    have haI : ContinuousOn a (Ioo c d) := by
      intro r hr
      exact (chartRep_base_diff (I := I) alpha A r x0
        (hY r (hsubJ hr)).1 (hsrc r hr)
        (by simpa only [A] using hvel r (hsubJ hr))).continuousAt.continuousWithinAt
    have hC : ContinuousOn C (Ioo c d) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hraw := lRegJacCLM_cont (I := I) S hS T x0 (Ioo c d) alpha a
        (continuousOn_iff_continuous_domRestrict.mp halphaI)
        (continuousOn_iff_continuous_domRestrict.mp haI) hsrc
        (fun r hr ↦ hreg r (hsubJ hr))
      refine hraw.congr (fun r ↦ ?_)
      change lRegJacobiCLM S T r x0 (alpha r)
          (trivFromE (I := I) x0 (alpha r) (a r)) (a r)
          (chartCurve (I := I) x0 alpha r) = C r
      have hbase : alpha r ∈
          (trivializationAt E (TangentSpace I) x0).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]
        exact hsrc r r.2
      rw [show a r = trivToE (I := I) x0 (alpha r) (A r) by
        rfl, trivFromE_trivToE (I := I) x0 hbase]
      rfl
    have hz (r : Real) (hr : r ∈ Ioo c d) :
        HasDerivAt z (C r (z r)) r := by
      simpa only [A, P, y, a, p, z, C] using
        lRegJacobi_state_clm (I := I) S hS T x0 alpha Y r
          (hreg r (hsubJ hr)) (hsrc r hr)
          (by
            filter_upwards [hJopen.mem_nhds (hsubJ hr)] with q hq
            exact (hY q hq).1)
          (hvel r (hsubJ hr)) (hY r (hsubJ hr))
    have hz' (r : Real) (hr : r ∈ Ioo c d) :
        HasDerivAt z' (C r (z' r)) r := by
      simpa only [A, P', y', a, p', z', C] using
        lRegJacobi_state_clm (I := I) S hS T x0 alpha Y' r
          (hreg r (hsubJ hr)) (hsrc r hr)
          (by
            filter_upwards [hJopen.mem_nhds (hsubJ hr)] with q hq
            exact (hY' q hq).1)
          (hvel r (hsubJ hr)) (hY' r (hsubJ hr))
    have hYs : Y s = Y' s :=
      TotalSpace.mk_inj.mp (congrArg Prod.fst hs.1)
    have hPs : P s = P' s :=
      TotalSpace.mk_inj.mp (congrArg Prod.snd hs.1)
    have hzs : z s = z' s := by
      apply Prod.ext
      · simp only [z, z', y, y', chartRepAtBase_apply, hYs]
      · simp only [z, z', p, p', chartRepAtBase_apply, hPs]
    have heq : Set.EqOn z z' (Ioo c d) :=
      linearODE_unique_on_Ioo hscd hC hz hz' hzs
    apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds hscd)
    intro r hr
    refine ⟨?_, hsubJ hr⟩
    have hbase : alpha r ∈
        (trivializationAt E (TangentSpace I) x0).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hsrc r hr
    have hcoord := heq hr
    have hYr : Y r = Y' r := by
      rw [← trivFromE_trivToE (I := I) x0 hbase (Y r),
        ← trivFromE_trivToE (I := I) x0 hbase (Y' r)]
      exact congrArg (trivFromE (I := I) x0 (alpha r))
        (by with_unfolding_all exact congrArg Prod.fst hcoord)
    have hPr : P r = P' r := by
      rw [← trivFromE_trivToE (I := I) x0 hbase (P r),
        ← trivFromE_trivToE (I := I) x0 hbase (P' r)]
      exact congrArg (trivFromE (I := I) x0 (alpha r))
        (by with_unfolding_all exact congrArg Prod.snd hcoord)
    apply Prod.ext
    · exact TotalSpace.mk_inj.mpr hYr
    · exact TotalSpace.mk_inj.mpr hPr
  have hclosed : closure U ∩ J ⊆ U := by
    change closure ({s | za s = zb s} ∩ J) ∩ J ⊆ {s | za s = zb s} ∩ J
    rw [inter_comm (closure ({s | za s = zb s} ∩ J)) J,
      ← Subtype.image_preimage_val J (closure ({s | za s = zb s} ∩ J)),
      inter_comm {s | za s = zb s} J,
      ← Subtype.image_preimage_val J {s | za s = zb s},
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro s hs
    rw [mem_preimage, ← closure_subtype] at hs
    revert hs s
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨s, hs⟩
      have hza_at : ContinuousAt za s :=
        (hza s hs).continuousAt (hJopen.mem_nhds hs)
      apply ContinuousAt.comp'
      · simpa using hza_at
      · exact continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨s, hs⟩
      have hzb_at : ContinuousAt zb s :=
        (hzb s hs).continuousAt (hJopen.mem_nhds hs)
      apply ContinuousAt.comp'
      · simpa using hzb_at
      · exact continuousAt_subtype_val
  have hstate : za s0 = zb s0 := by
    apply Prod.ext
    · exact TotalSpace.mk_inj.mpr h0
    · exact TotalSpace.mk_inj.mpr (by simpa only [P, P'] using hD0)
  have hsub : J ⊆ U := by
    apply hJconn.subset_of_closure_inter_subset hUopen
    · exact ⟨s0, ⟨hs0, hstate, hs0⟩⟩
    · exact hclosed
  intro s hs
  exact TotalSpace.mk_inj.mp (congrArg Prod.fst (hsub hs).1)

end DifferentialGeometry.PDE.RicciFlow.Perelman
