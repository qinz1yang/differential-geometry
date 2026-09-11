import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Regularized
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Regularity.Joint
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
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

private theorem contAt_sum
    {X F ι : Type*} [TopologicalSpace X] [AddCommMonoid F]
    [TopologicalSpace F] [ContinuousAdd F]
    {x : X} (s : Finset ι) (f : ι → X → F)
    (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y ↦ ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : F)) x)
  | @insert a s ha ih =>
      have hadd := (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      have hfun : f a + (fun y ↦ ∑ i ∈ s, f i y) =
          (fun y ↦ f a y + ∑ i ∈ s, f i y) := by rfl
      rw [hfun] at hadd
      simpa only [Finset.sum_insert ha] using hadd

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem movingCov_contOn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y : ∀ s, TangentSpace I (alpha s))
    {Ω K : Set Real} (hΩ : IsOpen Ω) (hK : K ⊆ Ω)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 2 alpha Ω)
    (hY : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) Ω)
    (hreg : ∀ s ∈ K, T - s ^ 2 ∈ D.regular) :
    ContinuousOn
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (alpha s)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s) :
            TangentBundle I M)) K := by
  classical
  intro t ht
  have htΩ : t ∈ Ω := hK ht
  have halphaAt : ContMDiffAt (modelWithCornersSelf Real Real) I 2 alpha t :=
    (halpha t htΩ).contMDiffAt (hΩ.mem_nhds htΩ)
  have hYAt : ContMDiffAt (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) t :=
    (hY t htΩ).contMDiffAt (hΩ.mem_nhds htΩ)
  let e := trivializationAt E (TangentSpace I : M → Type _) (alpha t)
  let u : Real → E := chartCurve (I := I) (alpha t) alpha
  let rep : Real → E := chartRepAtBase (I := I) (alpha t) alpha Y
  let tau : Real → Real := fun s ↦ T - s ^ 2
  have htreg : tau t ∈ D.regular := hreg t ht
  have hu2 : ContDiffAt Real 2 u t := by
    have h := (contMDiffAt_extChartAt (I := I) (x := alpha t) (n := 2)).comp t halphaAt
    exact contMDiffAt_iff_contDiffAt.mp h
  have hrep2 : ContDiffAt Real 2 rep t := by
    have hcoord := (Bundle.contMDiffAt_totalSpace.mp hYAt).2
    have hcoord' : ContDiffAt Real 2
        (fun s : Real ↦ (e (TotalSpace.mk' E (alpha s) (Y s))).2) t :=
      contMDiffAt_iff_contDiffAt.mp hcoord
    have hbase : ∀ᶠ s in 𝓝 t, alpha s ∈ e.baseSet :=
      halphaAt.continuousAt.preimage_mem_nhds
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
  have hdu : ContinuousAt (deriv u) t := by
    have hfd : ContDiffAt Real 1 (fderiv Real u) t :=
      hu2.fderiv_right (m := 1) (by norm_num)
    have happ := (hfd.clm_apply (contDiffAt_const (c := (1 : Real)))).continuousAt
    have heq : (fun s ↦ fderiv Real u s (1 : Real)) = deriv u := by
      funext s
      exact fderiv_apply_one_eq_deriv
    rw [heq] at happ
    exact happ
  have hdrep : ContinuousAt (deriv rep) t := by
    have hfd : ContDiffAt Real 1 (fderiv Real rep) t :=
      hrep2.fderiv_right (m := 1) (by norm_num)
    have happ := (hfd.clm_apply (contDiffAt_const (c := (1 : Real)))).continuousAt
    have heq : (fun s ↦ fderiv Real rep s (1 : Real)) = deriv rep := by
      funext s
      exact fderiv_apply_one_eq_deriv
    rw [heq] at happ
    exact happ
  have hu : ContinuousAt u t := hu2.continuousAt
  have hrep : ContinuousAt rep t := hrep2.continuousAt
  have htau : ContinuousAt tau t :=
    continuousAt_const.sub (continuousAt_id.pow 2)
  have hGamma (i j k : Fin (Module.finrank Real E)) :
      ContinuousAt
        (fun s ↦ chartChristoffel (I := I) (S.family.metric (tau s))
          (alpha t) i j k (u s)) t := by
    have hu_mem : u t ∈ interior (extChartAt I (alpha t)).target := by
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) (alpha t)
        ((extChartAt I (alpha t)).map_source
          (mem_extChartAt_source (I := I) (alpha t)))
    have hopen : IsOpen
        (D.regular ×ˢ interior (extChartAt I (alpha t)).target) :=
      D.regular_isOpen.prod isOpen_interior
    have hraw := MetricFamilySmoothOn.chartChristoffelOnE_continuousOn
      (I := I) (g_fam := S.family.metric) hS.smoothMetric
      (J := D.regular) (fun _ hs ↦ hs) D.regular_isOpen.uniqueDiffOn
      (alpha t) i j k
    have hrawAt : ContinuousAt
        (fun p : Real × E ↦ chartChristoffel (I := I)
          (S.family.metric p.1) (alpha t) i j k p.2) (tau t, u t) :=
      hraw.continuousAt (hopen.mem_nhds ⟨htreg, hu_mem⟩)
    let base : Real → Real × E := fun s ↦ (tau s, u s)
    have hbase : ContinuousAt base t := htau.prodMk hu
    have hcomp : ContinuousAt
        ((fun p : Real × E ↦ chartChristoffel (I := I)
          (S.family.metric p.1) (alpha t) i j k p.2) ∘ base) t :=
      ContinuousAt.comp (f := base) (x := t) hrawAt hbase
    have hfun : ((fun p : Real × E ↦ chartChristoffel (I := I)
        (S.family.metric p.1) (alpha t) i j k p.2) ∘ base) =
        (fun s ↦ chartChristoffel (I := I) (S.family.metric (tau s))
          (alpha t) i j k (u s)) := by rfl
    rw [hfun] at hcomp
    exact hcomp
  have hchrist : ContinuousAt
      (fun s ↦ chartChristoffelContraction (I := I)
        (S.family.metric (tau s)) (alpha t) (deriv u s) (rep s) (u s)) t := by
    unfold chartChristoffelContraction
    refine contAt_sum Finset.univ _ (fun k _ ↦ ?_)
    refine (contAt_sum Finset.univ _ (fun i _ ↦
      contAt_sum Finset.univ _ (fun j _ ↦ ?_))).smul continuousAt_const
    exact (((hGamma i j k).mul
      (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.continuous.continuousAt.comp
        hdu)).mul
      (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.continuous.continuousAt.comp
        hrep))
  have hchart : ContinuousAt
      (fun s ↦ chartCovDerivAlong (I := I) (S.base.metric (tau s))
        (alpha t) alpha rep s) t := by
    have hfun : (deriv rep + fun s ↦
        chartChristoffelContraction (I := I)
          (S.family.metric (tau s)) (alpha t) (deriv u s) (rep s) (u s)) =
        (fun s ↦ chartCovDerivAlong (I := I) (S.base.metric (tau s))
          (alpha t) alpha rep s) := by
      funext s
      rw [chartCovDerivAlong_def]
      rfl
    have hadd := hdrep.add hchrist
    rw [hfun] at hadd
    exact hadd
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨halphaAt.continuousAt.continuousWithinAt, ?_⟩
  have hsrc : ∀ᶠ s in 𝓝 t, alpha s ∈ (chartAt H (alpha t)).source :=
    halphaAt.continuousAt.preimage_mem_nhds
      ((chartAt H (alpha t)).open_source.mem_nhds (mem_chart_source H (alpha t)))
  have heq :
      (fun s ↦
        (e (TotalSpace.mk' E (alpha s)
          (covDerivAlong (I := I) (S.base.metric (tau s)) alpha Y s))).2)
        =ᶠ[𝓝 t]
      (fun s ↦ chartCovDerivAlong (I := I) (S.base.metric (tau s))
        (alpha t) alpha rep s) := by
    filter_upwards [hsrc, hΩ.mem_nhds htΩ] with s hs hsΩ
    have halphaS : ContMDiffAt (modelWithCornersSelf Real Real) I 2 alpha s :=
      (halpha s hsΩ).contMDiffAt (hΩ.mem_nhds hsΩ)
    have hYS : ContMDiffAt (modelWithCornersSelf Real Real) I.tangent 2
        (fun r : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha r) (Y r) : TangentBundle I M)) s :=
      (hY s hsΩ).contMDiffAt (hΩ.mem_nhds hsΩ)
    have hYdiff := differentiableAt_chartRepAt_of_contMDiffAt_two (I := I) hYS
    have hinv := covDeriv_chartAt (I := I)
      (S.base.metric (tau s)) alpha Y s (alpha t)
      (halphaS.mdifferentiableAt (by norm_num)) hs hYdiff
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
    rw [hcoord]
    rw [← hinv]
    exact (e.continuousLinearMapAt_symmL (R := Real) hbase _)
  exact (hchart.congr_of_eventuallyEq heq).continuousWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem movingCov_cont
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y : ∀ s, TangentSpace I (alpha s))
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 2 alpha)
    (hY : ContMDiff (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)))
    {K : Set Real} (hreg : ∀ s ∈ K, T - s ^ 2 ∈ D.regular) :
    ContinuousOn
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (alpha s)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s) :
            TangentBundle I M)) K :=
  movingCov_contOn S hS T alpha Y isOpen_univ (Set.subset_univ K)
    halpha.contMDiffOn hY.contMDiffOn hreg

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiffOn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a b : Real)
    (alpha : Real → M) (Y W : ∀ s, TangentSpace I (alpha s))
    {Ω : Set Real} (hΩ : IsOpen Ω) (hseg : uIcc a b ⊆ Ω)
    (hY : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) Ω)
    (hW : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (W s) : TangentBundle I M)) Ω)
    (hreg : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume a b := by
  classical
  have halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 2 alpha Ω := by
    intro t ht
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (hY t ht)).1
  let K := uIcc a b
  let P := {s : Real // s ∈ K}
  let tau : P → Real := fun z ↦ T - (z : Real) ^ 2
  let base : P → M := fun z ↦ alpha z
  let A : (z : P) → TangentSpace I (base z) := fun z ↦
    lVelocity (I := I) alpha z
  let DY : (z : P) → TangentSpace I (base z) := fun z ↦
    covDerivAlong (I := I) (S.base.metric (tau z)) alpha Y z
  let DW : (z : P) → TangentSpace I (base z) := fun z ↦
    covDerivAlong (I := I) (S.base.metric (tau z)) alpha W z
  have hz : Continuous (fun z : P ↦ (z : Real)) := continuous_subtype_val
  have htau : Continuous tau := by
    have hconst : Continuous (fun _ : P ↦ T) := continuous_const
    have hpow : Continuous (fun z : P ↦ (z : Real) ^ 2) := hz.pow 2
    with_unfolding_all exact hconst.sub hpow
  have hbase : Continuous base := by
    have h := (halpha.continuousOn.mono hseg).domRestrict
    with_unfolding_all exact h
  have hYsec : Continuous (fun z : P ↦
      (TotalSpace.mk' E (base z) (Y z) : TangentBundle I M)) := by
    have h := (hY.continuousOn.mono hseg).domRestrict
    with_unfolding_all exact h
  have hWsec : Continuous (fun z : P ↦
      (TotalSpace.mk' E (base z) (W z) : TangentBundle I M)) := by
    have h := (hW.continuousOn.mono hseg).domRestrict
    with_unfolding_all exact h
  have hAsec : Continuous (fun z : P ↦
      (TotalSpace.mk' E (base z) (A z) : TangentBundle I M)) := by
    have htangent := halpha.contMDiffOn_tangentMapWithin
      (m := 0) (by norm_num) hΩ.uniqueMDiffOn
    have hone : ContMDiff (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real).tangent 0
        (fun s : Real ↦ (⟨s, 1⟩ : TangentBundle
          (modelWithCornersSelf Real Real) Real)) := by
      rw [contMDiff_vectorSpace_iff_contDiff]
      exact contDiff_const
    have hcomp : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent 0
        (fun s : Real ↦ tangentMapWithin (modelWithCornersSelf Real Real) I
          alpha Ω (⟨s, 1⟩ : TangentBundle
            (modelWithCornersSelf Real Real) Real)) Ω :=
      htangent.comp hone.contMDiffOn (fun _ hs ↦ hs)
    have hvel : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent 0
        (fun s : Real ↦
          (TotalSpace.mk' E (alpha s) (lVelocity (I := I) alpha s) :
            TangentBundle I M)) Ω := by
      refine hcomp.congr ?_
      intro s hs
      have hwithin : mfderivWithin (modelWithCornersSelf Real Real) I
          alpha Ω s = mfderiv (modelWithCornersSelf Real Real) I alpha s :=
        mfderivWithin_of_isOpen hΩ hs
      simp only [tangentMapWithin, lVelocity, hwithin]
      rfl
    have h := (hvel.continuousOn.mono hseg).domRestrict
    with_unfolding_all exact h
  have hDYsec : Continuous (fun z : P ↦
      (TotalSpace.mk' E (base z) (DY z) : TangentBundle I M)) := by
    have h := movingCov_contOn (I := I) S hS T alpha Y hΩ hseg halpha hY
      (K := K) (by simpa only [K] using hreg)
    have h' := h.domRestrict
    with_unfolding_all exact h'
  have hDWsec : Continuous (fun z : P ↦
      (TotalSpace.mk' E (base z) (DW z) : TangentBundle I M)) := by
    have h := movingCov_contOn (I := I) S hS T alpha W hΩ hseg halpha hW
      (K := K) (by simpa only [K] using hreg)
    have h' := h.domRestrict
    with_unfolding_all exact h'
  have hInner : Continuous (fun z : P ↦
      (S.base.metric (tau z)).inner (base z) (DY z) (DW z)) := by
    have h := hS.smoothMetric.metricTensor_cont.eval_continuous
      (P := P) htau
      (fun z ↦ D.regular_subset (hreg z (by simpa only [K] using z.2))) hbase
      (v := fun i z ↦ vec2 (DY z) (DW z) i) (by
        intro i
        fin_cases i
        · with_unfolding_all
            simpa [vec2] using hDYsec
        · with_unfolding_all
            simpa [vec2] using hDWsec)
    refine h.congr (fun z ↦ ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [SolutionOn.family_metric, vec2]
  have hRm : Continuous (fun z : P ↦
      S.base.rm04 (tau z) (base z) (vec4 (Y z) (A z) (A z) (W z))) := by
    apply hS.rm04Cont.eval_continuous (P := P) htau
      (fun z ↦ D.regular_subset (hreg z (by simpa only [K] using z.2))) hbase
    intro i
    fin_cases i
    · with_unfolding_all
        simpa [vec4] using hYsec
    · with_unfolding_all
        simpa [vec4] using hAsec
    · with_unfolding_all
        simpa [vec4] using hAsec
    · with_unfolding_all
        simpa [vec4] using hWsec
  have hHess : Continuous (fun z : P ↦
      hessianSec (I := I) (S.base.connection (tau z))
        (metricCov_smooth (I := I) (S.base.metric (tau z)))
        (S.scalar (tau z)) (scalarSmoothOfSolution (I := I) S (tau z)) (base z)
        (vec2 (Y z) (W z))) := by
    apply (scalarHess_cont (I := I) S hS).eval_continuous
      (P := P) htau (fun z ↦ hreg z (by simpa only [K] using z.2)) hbase
    intro i
    fin_cases i
    · with_unfolding_all
        simpa [vec2] using hYsec
    · with_unfolding_all
        simpa [vec2] using hWsec
  have hRic1 : Continuous (fun z : P ↦
      totalNabla0SFun (𝕜 := Real) (I := I) 2
        (S.base.connection (tau z)) (S.ricci (tau z)) (base z)
        (vec3 (A z) (Y z) (W z))) := by
    apply (nablaRicci_cont (I := I) S hS).eval_continuous
      (P := P) htau (fun z ↦ hreg z (by simpa only [K] using z.2)) hbase
    intro i
    fin_cases i
    · with_unfolding_all
        simpa [vec3] using hAsec
    · with_unfolding_all
        simpa [vec3] using hYsec
    · with_unfolding_all
        simpa [vec3] using hWsec
  have hRic2 : Continuous (fun z : P ↦
      totalNabla0SFun (𝕜 := Real) (I := I) 2
        (S.base.connection (tau z)) (S.ricci (tau z)) (base z)
        (vec3 (Y z) (A z) (W z))) := by
    apply (nablaRicci_cont (I := I) S hS).eval_continuous
      (P := P) htau (fun z ↦ hreg z (by simpa only [K] using z.2)) hbase
    intro i
    fin_cases i
    · with_unfolding_all
        simpa [vec3] using hYsec
    · with_unfolding_all
        simpa [vec3] using hAsec
    · with_unfolding_all
        simpa [vec3] using hWsec
  have hRic3 : Continuous (fun z : P ↦
      totalNabla0SFun (𝕜 := Real) (I := I) 2
        (S.base.connection (tau z)) (S.ricci (tau z)) (base z)
        (vec3 (W z) (A z) (Y z))) := by
    apply (nablaRicci_cont (I := I) S hS).eval_continuous
      (P := P) htau (fun z ↦ hreg z (by simpa only [K] using z.2)) hbase
    intro i
    fin_cases i
    · with_unfolding_all
        simpa [vec3] using hWsec
    · with_unfolding_all
        simpa [vec3] using hAsec
    · with_unfolding_all
        simpa [vec3] using hYsec
  have hhalf : Continuous (fun _ : P ↦ (1 / 2 : Real)) := continuous_const
  have hsq : Continuous (fun z : P ↦ (z : Real) ^ 2) := hz.pow 2
  have hall := ((hhalf.mul (hInner.sub hRm)).add (hsq.mul hHess)).add
    (hz.mul ((hRic1.sub hRic2).sub hRic3))
  have hcont : ContinuousOn (lRegularizedIndexIntegrand S T alpha Y W) K := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine hall.congr (fun z ↦ ?_)
    change _ = lRegularizedIndexIntegrand S T alpha Y W (z : Real)
    rfl
  exact hcont.intervalIntegrable

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiff
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a b : Real)
    (alpha : Real → M) (Y W : ∀ s, TangentSpace I (alpha s))
    (hY : ContMDiff (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)))
    (hW : ContMDiff (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (W s) : TangentBundle I M)))
    (hreg : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume a b :=
  intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiffOn S hS T a b alpha Y W isOpen_univ
    (Set.subset_univ (uIcc a b)) hY.contMDiffOn hW.contMDiffOn hreg

end DifferentialGeometry.PDE.RicciFlow.Perelman
