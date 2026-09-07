import DifferentialGeometry.Analysis.Elliptic.WeakLaplacian
import DifferentialGeometry.Analysis.Elliptic.MetricEllipticCoeff
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapSource
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionHeadline
import DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.PositiveTestDensity
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.CoefficientOperator

set_option autoImplicit false

open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DistributionalSupersolution

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Tensor.Coordinates
  (chartModelBasis chartModelBasis_apply partialDeriv)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma partial_comp_euclid
    (i : Fin (Module.finrank ℝ E)) (f : E → ℝ) (y : EuclN) :
    partialDeriv (E := E) i f ((toEuclidean (E := E)).symm y) =
      euclidPartial (E := E) i (f ∘ (toEuclidean (E := E)).symm) y := by
  rw [euclidPartial_def, partialDeriv]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv (f := f) (x := y)]
  rw [ContinuousLinearMap.comp_apply]
  rw [show (toEuclidean (E := E)).symm.toContinuousLinearMap
      (EuclideanSpace.single i (1 : ℝ)) = (chartModelBasis E) i from by
    rw [chartModelBasis_apply]
    rfl]

def laplacianChartTestFlux (g : SmoothRiemannianMetric I M) (α : M)
    (ψ : EuclN → ℝ) (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y => ∑ j : Fin (Module.finrank ℝ E),
    weightedInvGramOnEuclid (I := I) g α i j y *
      euclidPartial (E := E) j ψ y

omit [IsManifold I ∞ M] in
private lemma chartTest_partial_eq [I.Boundaryless]
    (α : M) (ψ : EuclN → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) j
        (scalarOnE (I := I) α
          (chartTestPullback (I := I) (M := M) α ψ))
        ((toEuclidean (E := E)).symm y) =
      euclidPartial (E := E) j ψ y := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_raw :
      (scalarOnE (I := I) α
          (chartTestPullback (I := I) (M := M) α ψ) ∘
        (toEuclidean (E := E)).symm) =ᶠ[𝓝 y] ψ := by
    filter_upwards [h_open.mem_nhds hy] with z hz
    have hz_target : (toEuclidean (E := E)).symm z ∈
        (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hz
    have hx_src_ext :
        (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∈
          (extChartAt I α).source :=
      (extChartAt I α).map_target hz_target
    have hx_src :
        (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∈
          (chartAt H α).source := by
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_src_ext
    rw [Function.comp_apply, scalarOnE_def,
      chartTestPullback_apply_of_mem (I := I) α ψ hx_src,
      (extChartAt I α).right_inv hz_target,
      (toEuclidean (E := E)).apply_symm_apply]
  rw [partial_comp_euclid (E := E)]
  rw [euclidPartial_def, euclidPartial_def, h_raw.fderiv_eq]

private lemma vossFlux_eventuallyEq [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M) (ψ : EuclN → ℝ)
    (i : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (chartVossWeylIntegrand (I := I) g α
        (chartTestPullback (I := I) (M := M) α ψ) i ∘
      (toEuclidean (E := E)).symm) =ᶠ[𝓝 y]
        laplacianChartTestFlux (I := I) g α ψ i := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  filter_upwards [h_open.mem_nhds hy] with z hz
  rw [Function.comp_apply, chartVossWeylIntegrand_def,
    gradChartCoeffOnE_def, Finset.sum_mul]
  unfold laplacianChartTestFlux
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [chartTest_partial_eq (I := I) (M := M) α ψ hz j]
  change
    (invGramOnEuclid (I := I) g α i j z *
        euclidPartial (E := E) j ψ z) * densityOnEuclid (I := I) g α z =
      densityOnEuclid (I := I) g α z *
        invGramOnEuclid (I := I) g α i j z *
          euclidPartial (E := E) j ψ z
  ring

theorem laplacian_chart_divergence
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    densityOnEuclid (I := I) g α y *
        ΔG (I := I) g
          ⟨chartTestPullback (I := I) (M := M) α ψ,
            chartTestPullback_contMDiff (I := I) (M := M) α hψ hψ_cs hψ_supp⟩
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      ∑ i : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) i (laplacianChartTestFlux (I := I) g α ψ i) y := by
  let f : M → ℝ := chartTestPullback (I := I) (M := M) α ψ
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    chartTestPullback_contMDiff (I := I) (M := M) α hψ hψ_cs hψ_supp
  let x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have hx_src_ext : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_target
  have hx_src : x ∈ (chartAt H α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_src_ext
  have h_voss :
      ΔG (I := I) g ⟨f, hf⟩ x =
        chartVossWeylLaplacian (I := I) g α f x :=
    laplacian_eq_chartVossWeyl_of_sigmaCompact (I := I) g α hf hx_src
  have h_density :
      chartDensity (I := I) g α x = densityOnEuclid (I := I) g α y := by
    rfl
  have h_density_ne : densityOnEuclid (I := I) g α y ≠ 0 :=
    ne_of_gt (densityOnEuclid_pos (I := I) g α hy)
  change densityOnEuclid (I := I) g α y * ΔG (I := I) g ⟨f, hf⟩ x = _
  rw [h_voss, chartVossWeylLaplacian_def, h_density]
  calc
    densityOnEuclid (I := I) g α y *
          ((∑ i : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i
              (chartVossWeylIntegrand (I := I) g α f i)
              ((extChartAt I α) x)) /
            densityOnEuclid (I := I) g α y) =
        ∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (chartVossWeylIntegrand (I := I) g α f i)
            ((extChartAt I α) x) := by
              field_simp [h_density_ne]
    _ = ∑ i : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) i (laplacianChartTestFlux (I := I) g α ψ i) y := by
      refine Finset.sum_congr rfl ?_
      intro i _
      have hx_coord : (extChartAt I α) x = (toEuclidean (E := E)).symm y :=
        (extChartAt I α).right_inv hy_target
      rw [hx_coord, partial_comp_euclid (E := E)]
      rw [euclidPartial_def, euclidPartial_def,
        (vossFlux_eventuallyEq (I := I) (M := M) g α ψ i hy).fderiv_eq]

private theorem lap_tsupport_subset [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    tsupport (ΔG (I := I) g φ) ⊆ tsupport (φ : M → ℝ) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hx_not
  have heq : (φ : M → ℝ) =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) :=
    notMem_tsupport_iff_eventuallyEq.mp hx_not
  have hφ_eta : (⟨(φ : M → ℝ), φ.contMDiff⟩ : C^∞⟮I, M; ℝ⟯) = φ := by
    ext y
    rfl
  have hlap := Δ_g_congr_of_eventuallyEq (I := I) g φ.contMDiff
    (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ))) heq
  have hzero : ΔG (I := I) g φ x = 0 := by
    rw [← hφ_eta, hlap]
    exact Δ_g_const (I := I) g 0 x
  exact hx hzero

private theorem tsupport_sum_subset
    {X ι : Type*} [TopologicalSpace X]
    (S : Finset ι) (F : ι → X → ℝ) {K : Set X}
    (hK : IsClosed K) (hF : ∀ i ∈ S, tsupport (F i) ⊆ K) :
    tsupport (fun x => ∑ i ∈ S, F i x) ⊆ K := by
  classical
  refine closure_minimal ?_ hK
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxK
  exact hx (Finset.sum_eq_zero fun i hi =>
    image_eq_zero_of_notMem_tsupport (fun hxi => hxK (hF i hi hxi)))

private theorem chart_divergence_test_le
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} {U : Set M}
    (h : IsLaplacianLEDistributionalOn (I := I) g u (fun _ => 0) U)
    (hu : Continuous u)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hψ_U : tsupport (chartTestPullback (I := I) (M := M) α ψ) ⊆ U)
    (hψ0 : ∀ y, 0 ≤ ψ y) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u y *
        (∑ i : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) i (laplacianChartTestFlux (I := I) g α ψ i) y)
      ∂(volume : Measure EuclN)) ≤ 0 := by
  let f : M → ℝ := chartTestPullback (I := I) (M := M) α ψ
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    chartTestPullback_contMDiff (I := I) (M := M) α hψ hψ_cs hψ_supp
  let φ : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
  have hφ_cs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact
      (euclTestLift_isCompact (I := I) (M := M) α hψ_cs hψ_supp)
      (chartTestPullback_support_subset (I := I) (M := M) α ψ)
  have hφ_mem : φ ∈ compactlySupportedSmoothFunctions I M := hφ_cs
  have hφ0 : ∀ x, 0 ≤ φ x := by
    intro x
    by_cases hx : x ∈ (chartAt H α).source
    · change 0 ≤ chartTestPullback (I := I) (M := M) α ψ x
      rw [chartTestPullback_apply_of_mem (I := I) α ψ hx]
      exact hψ0 _
    · change 0 ≤ chartTestPullback (I := I) (M := M) α ψ x
      rw [chartTestPullback_apply_of_notMem (I := I) α ψ hx]
  have h_distrib :
      (∫ x, u x * ΔG (I := I) g φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ 0 := by
    simpa only [zero_mul, integral_zero] using
      h.test_le φ hφ_mem hψ_U hφ0
  let F : M → ℝ := fun x => u x * ΔG (I := I) g φ x
  have hF_cont : Continuous F :=
    hu.mul (Δ_g_contMDiff (I := I) g φ).continuous
  have hΔ_cs : HasCompactSupport (ΔG (I := I) g φ) :=
    HasCompactSupport.of_support_subset_isCompact hφ_cs
      ((subset_tsupport _).trans (lap_tsupport_subset (I := I) g φ))
  have hF_cs : HasCompactSupport F := hΔ_cs.mul_left
  have hF_supp : tsupport F ⊆ (chartAt H α).source := by
    change tsupport (fun x => u x * ΔG (I := I) g φ x) ⊆ _
    refine tsupport_mul_subset_right.trans ?_
    exact (lap_tsupport_subset (I := I) g φ).trans
      (chartTestPullback_tsupport_subset_source
        (I := I) (M := M) α hψ_cs hψ_supp)
  have h_change :=
    ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport
    (I := I) (M := M) g α hF_cont hF_cs hF_supp
  rw [DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume
    (E := E)] at h_change
  have h_coord :
      (∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u y *
            (∑ i : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) i (laplacianChartTestFlux (I := I) g α ψ i) y)
          ∂(volume : Measure EuclN) := by
    rw [h_change]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet] with y hy
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α u hy]
    have hdiv := laplacian_chart_divergence
      (I := I) (M := M) g α hψ hψ_cs hψ_supp hy
    change densityOnEuclid (I := I) g α y *
        ΔG (I := I) g φ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = _ at hdiv
    change densityOnEuclid (I := I) g α y *
        (u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ΔG (I := I) g φ
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = _
    calc
      _ = u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          (densityOnEuclid (I := I) g α y *
            ΔG (I := I) g φ
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) := by ring
      _ = _ := by rw [hdiv]
  change (∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ 0 at h_distrib
  rwa [h_coord] at h_distrib

theorem isSupersolution_chartPushedRaw_of_isLaplacianLEDistributionalOn
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (alpha : M)
    {c : EuclN} {r : ℝ}
    (hball : closure (Metric.ball c r) ⊆
      chartTargetEuclid (I := I) (M := M) alpha)
    {u : M → ℝ}
    (h : IsLaplacianLEDistributionalOn (I := I) g u (fun _ => 0) Set.univ)
    (hu : Continuous u)
    (huW : DeGiorgi.MemW1p 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I alpha u)
      (Metric.ball c r))
    (A : DeGiorgi.EllipticCoeff
      (Module.finrank ℝ E) (Metric.ball c r))
    {s : ℝ} (hs : 0 < s)
    (hA : ∀ y ∈ Metric.ball c r, ∀ i j,
      A.a y i j =
        s * weightedInvGramOnEuclid (I := I) g alpha i j y) :
    DeGiorgi.IsSupersolution A
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I alpha u) := by
  classical
  let Omega : Set EuclN := Metric.ball c r
  have hOmega : IsOpen Omega := Metric.isOpen_ball
  have hOmega_chart : Omega ⊆ chartTargetEuclid (I := I) (M := M) alpha :=
    subset_closure.trans hball
  apply DeGiorgi.IsSupersolution.of_nonnegative_smooth_tests hOmega A huW
  intro hwv psi hpsi hpsi_nonneg
  let v : EuclN → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I alpha u
  let K : Set EuclN := tsupport psi
  have hK_compact : IsCompact K := hpsi.2.1
  have hK_chart : K ⊆ chartTargetEuclid (I := I) (M := M) alpha :=
    hpsi.2.2.trans hOmega_chart
  choose delta b hdelta _hdelta_chart hb_smooth hb_eq using
    fun i j : Fin (Module.finrank ℝ E) =>
      exists_smooth_global_extension
        (I := I) (M := M)
        (φ := weightedInvGramOnEuclid (I := I) g alpha i j) alpha
        (weightedInvGramOnEuclid_contDiffOn (I := I) g alpha i j)
        hK_compact hK_chart
  let q : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i y =>
    ∑ j : Fin (Module.finrank ℝ E),
      b i j y * euclidPartial (E := E) j psi y
  have hq_smooth (i : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ (⊤ : ℕ∞) (q i) := by
    dsimp only [q]
    exact ContDiff.sum fun j _ =>
      (hb_smooth i j).mul
        (euclidPartial_contDiff (E := E) hpsi.1 j)
  have hq_tsupport (i : Fin (Module.finrank ℝ E)) :
      tsupport (q i) ⊆ K := by
    change tsupport (fun y => ∑ j : Fin (Module.finrank ℝ E),
      b i j y * euclidPartial (E := E) j psi y) ⊆ K
    simpa using
      tsupport_sum_subset (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun j y => b i j y * euclidPartial (E := E) j psi y)
        (isClosed_tsupport psi) (fun j _ =>
          (tsupport_mul_subset_right.trans
            (euclidPartial_tsupport_subset (E := E) j)))
  have hq_compact (i : Fin (Module.finrank ℝ E)) :
      HasCompactSupport (q i) :=
    HasCompactSupport.of_support_subset_isCompact hK_compact
      ((subset_tsupport _).trans (hq_tsupport i))
  have hq_sub (i : Fin (Module.finrank ℝ E)) :
      tsupport (q i) ⊆ Omega :=
    (hq_tsupport i).trans hpsi.2.2
  have hq_eq (i : Fin (Module.finrank ℝ E)) (y : EuclN) :
      q i y = laplacianChartTestFlux (I := I) g alpha psi i y := by
    by_cases hy : y ∈ K
    · unfold q laplacianChartTestFlux
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hb_eq i j y (Metric.self_subset_cthickening K hy)]
    · have hpartial : ∀ j : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) j psi y = 0 := by
        intro j
        exact image_eq_zero_of_notMem_tsupport fun hj =>
          hy (euclidPartial_tsupport_subset (E := E) j hj)
      simp only [q, laplacianChartTestFlux, hpartial, mul_zero, Finset.sum_const_zero]
  have hq_eventuallyEq (i : Fin (Module.finrank ℝ E)) (y : EuclN) :
      q i =ᶠ[𝓝 y] laplacianChartTestFlux (I := I) g alpha psi i := by
    by_cases hy : y ∈ K
    · have hall : ∀ᶠ z in 𝓝 y, ∀ j ∈ (Finset.univ :
          Finset (Fin (Module.finrank ℝ E))),
          b i j z = weightedInvGramOnEuclid (I := I) g alpha i j z := by
        refine (Filter.eventually_all_finset Finset.univ).mpr ?_
        intro j _
        filter_upwards
          [Metric.isOpen_thickening.mem_nhds
            (Metric.self_subset_thickening (hdelta i j) K hy)] with z hz
        exact hb_eq i j z
          (Metric.thickening_subset_cthickening (delta i j) K hz)
      filter_upwards [hall] with z hz
      unfold q laplacianChartTestFlux
      exact Finset.sum_congr rfl fun j hj => by rw [hz j hj]
    · filter_upwards
        [(isClosed_tsupport psi).isOpen_compl.mem_nhds hy] with z hz
      have hpartial : ∀ j : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) j psi z = 0 := by
        intro j
        exact image_eq_zero_of_notMem_tsupport fun hj =>
          hz (euclidPartial_tsupport_subset (E := E) j hj)
      simp only [q, laplacianChartTestFlux, hpartial, mul_zero, Finset.sum_const_zero]
  have hdiv_eq (i : Fin (Module.finrank ℝ E)) (y : EuclN) :
      euclidPartial (E := E) i (q i) y =
        euclidPartial (E := E) i
          (laplacianChartTestFlux (I := I) g alpha psi i) y := by
    rw [euclidPartial_def, euclidPartial_def,
      (hq_eventuallyEq i y).fderiv_eq]
  have hdistrib := chart_divergence_test_le
    (I := I) (M := M) g alpha h hu hpsi.1 hpsi.2.1 hK_chart
      (subset_univ _) hpsi_nonneg
  have hdiv_le :
      (∫ y in Omega, v y *
        (∑ i : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) i (q i) y) ∂(volume : Measure EuclN)) ≤ 0 := by
    have hchart_le :
        (∫ y in chartTargetEuclid (I := I) (M := M) alpha, v y *
          (∑ i : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) i (q i) y)
          ∂(volume : Measure EuclN)) ≤ 0 := by
      simpa only [v, hdiv_eq] using hdistrib
    have hrestrict :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (μ := (volume : Measure EuclN))
        (chartTargetEuclid_isOpen (I := I) (M := M) alpha).measurableSet
        hOmega_chart
        (f := fun y => v y *
          (∑ i : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) i (q i) y))
        (fun y hy => by
          have hyK : y ∉ K := fun hy' => hy.2 (hpsi.2.2 hy')
          have hzero : ∀ i : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) i (q i) y = 0 := by
            intro i
            exact image_eq_zero_of_notMem_tsupport fun hi =>
              hyK ((euclidPartial_tsupport_subset (E := E) i).trans
                (hq_tsupport i) hi)
          simp only [hzero, Finset.sum_const_zero, mul_zero])
    rwa [hrestrict] at hchart_le
  have hleft_int (i : Fin (Module.finrank ℝ E)) :
      Integrable
        (fun y => v y * euclidPartial (E := E) i (q i) y)
        ((volume : Measure EuclN).restrict Omega) := by
    have hv_loc : LocallyIntegrable v ((volume : Measure EuclN).restrict Omega) :=
      hwv.memLp.locallyIntegrable (by norm_num)
    have hpartial_cont : Continuous (euclidPartial (E := E) i (q i)) :=
      (euclidPartial_contDiff (E := E) (hq_smooth i) i).continuous
    have hpartial_compact :
        HasCompactSupport (euclidPartial (E := E) i (q i)) := by
      change HasCompactSupport
        (fun y => (fderiv ℝ (q i) y) (EuclideanSpace.single i (1 : ℝ)))
      exact HasCompactSupport.fderiv_apply ℝ (hq_compact i)
        (EuclideanSpace.single i (1 : ℝ))
    simpa [smul_eq_mul] using
      hv_loc.integrable_smul_right_of_hasCompactSupport
        hpartial_cont hpartial_compact
  have hright_int (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun y => hwv.weakGrad y i * q i y)
        ((volume : Measure EuclN).restrict Omega) := by
    have hw_loc : LocallyIntegrable (fun y => hwv.weakGrad y i)
        ((volume : Measure EuclN).restrict Omega) :=
      (hwv.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
    simpa [smul_eq_mul] using
      hw_loc.integrable_smul_right_of_hasCompactSupport
        (hq_smooth i).continuous (hq_compact i)
  have hibp (i : Fin (Module.finrank ℝ E)) :
      (∫ y in Omega, v y * euclidPartial (E := E) i (q i) y
          ∂(volume : Measure EuclN)) =
        -∫ y in Omega, hwv.weakGrad y i * q i y
          ∂(volume : Measure EuclN) := by
    simpa only [v, euclidPartial_def] using
      hwv.isWeakGrad i (q i) (hq_smooth i) (hq_compact i) (hq_sub i)
  have hibp_sum :
      (∫ y in Omega, v y *
          (∑ i : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) i (q i) y)
          ∂(volume : Measure EuclN)) =
        -∫ y in Omega,
          ∑ i : Fin (Module.finrank ℝ E), hwv.weakGrad y i * q i y
          ∂(volume : Measure EuclN) := by
    calc
      (∫ y in Omega, v y *
          (∑ i : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) i (q i) y)
          ∂(volume : Measure EuclN)) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∫ y in Omega, v y * euclidPartial (E := E) i (q i) y
              ∂(volume : Measure EuclN) := by
                rw [show (fun y => v y *
                    (∑ i : Fin (Module.finrank ℝ E),
                      euclidPartial (E := E) i (q i) y)) =
                    fun y => ∑ i : Fin (Module.finrank ℝ E),
                      v y * euclidPartial (E := E) i (q i) y by
                  funext y
                  rw [Finset.mul_sum]]
                exact integral_finsetSum
                  (μ := (volume : Measure EuclN).restrict Omega)
                  Finset.univ fun i _ => hleft_int i
      _ = ∑ i : Fin (Module.finrank ℝ E),
          -∫ y in Omega, hwv.weakGrad y i * q i y
            ∂(volume : Measure EuclN) :=
        Finset.sum_congr rfl fun i _ => hibp i
      _ = -(∑ i : Fin (Module.finrank ℝ E),
          ∫ y in Omega, hwv.weakGrad y i * q i y
            ∂(volume : Measure EuclN)) := by
        rw [Finset.sum_neg_distrib]
      _ = -∫ y in Omega,
          ∑ i : Fin (Module.finrank ℝ E), hwv.weakGrad y i * q i y
          ∂(volume : Measure EuclN) := by
        rw [integral_finsetSum
          (μ := (volume : Measure EuclN).restrict Omega)
          Finset.univ fun i _ => hright_int i]
  have henergy :
      0 ≤ ∫ y in Omega,
        ∑ i : Fin (Module.finrank ℝ E), hwv.weakGrad y i * q i y
        ∂(volume : Measure EuclN) := by
    rw [hibp_sum] at hdiv_le
    linarith
  let hpsi_w : DeGiorgi.MemW1pWitness 2 psi Omega :=
    DeGiorgi.smoothTestWitness hOmega hpsi
  have hbilin_eq :
      DeGiorgi.bilinFormOfCoeff A hwv hpsi_w =
        s * ∫ y in Omega,
          ∑ i : Fin (Module.finrank ℝ E), hwv.weakGrad y i * q i y
          ∂(volume : Measure EuclN) := by
    unfold DeGiorgi.bilinFormOfCoeff
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hOmega.measurableSet] with y hy
    have hy_ball : y ∈ Metric.ball c r := hy
    have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
      intro a b
      simpa using (RCLike.inner_apply' a b)
    simp only [DeGiorgi.bilinFormIntegrandOfCoeff, PiLp.inner_apply,
      DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, hscalar,
      hpsi_w, DeGiorgi.smoothTestWitness, DeGiorgi.smoothGradField]
    simp_rw [hA y hy_ball]
    simp_rw [hq_eq]
    unfold laplacianChartTestFlux
    calc
      (∑ i : Fin (Module.finrank ℝ E),
          (∑ j : Fin (Module.finrank ℝ E),
            s * weightedInvGramOnEuclid (I := I) g alpha i j y *
              hwv.weakGrad y j) * euclidPartial (E := E) i psi y) =
          s * ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g alpha i j y *
                hwv.weakGrad y j * euclidPartial (E := E) i psi y := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            ring_nf
      _ = s * ∑ j : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g alpha i j y *
                hwv.weakGrad y j * euclidPartial (E := E) i psi y := by
            rw [Finset.sum_comm]
      _ = s * ∑ j : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g alpha j i y *
                hwv.weakGrad y j * euclidPartial (E := E) i psi y := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j _
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [weightedInvGramOnEuclid_symm_of_mem (I := I) g alpha i j
              (hOmega_chart hy)]
      _ = s * ∑ j : Fin (Module.finrank ℝ E),
            hwv.weakGrad y j *
              (∑ i : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g alpha j i y *
                  euclidPartial (E := E) i psi y) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
  have hnonneg : 0 ≤ DeGiorgi.bilinFormOfCoeff A hwv hpsi_w := by
    rw [hbilin_eq]
    exact mul_nonneg hs.le henergy
  simpa only [hpsi_w] using hnonneg

end DistributionalSupersolution
end Laplacian
end Analysis
end DifferentialGeometry
