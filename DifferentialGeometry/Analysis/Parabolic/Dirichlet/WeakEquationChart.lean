import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakFormIntegration
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Geometry.Operator.WithBoundary.VossWeyl
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Operator.WithBoundary
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

omit [T2Space M] [CompactSpace M] in
private theorem adjoint_test_eq_zero_of_notMem_tsupport
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a : ℝ) (v : SmoothScalarDirichlet q) {x : M} (hx : x ∉ tsupport v.toFun) :
    ΔGWithBoundary (I := I_hs) h v.smooth v.interior_support x -
      tangentSectionAction (I := I_hs) X v.toFun x -
      divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) h) X x * v.toFun x -
      a * v.toFun x = 0 := by
  have hv := image_eq_zero_of_notMem_tsupport hx
  have hΔ := image_eq_zero_of_notMem_tsupport
    (fun hxΔ => hx (tsupport_Δ_g_with_boundary_subset h v.smooth v.interior_support hxΔ))
  have hgrad : (gradGWithBoundarySection (I := I_hs) q v.smooth v.interior_support) x = 0 :=
    Function.notMem_support.mp
      (fun hxg => hx (support_grad_g_with_boundary_section_subset q v.smooth v.interior_support hxg))
  have ha : tangentSectionAction (I := I_hs) X v.toFun x = 0 := by
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I_hs) q X]
    change q.inner x (X x)
      ((gradGWithBoundarySection (I := I_hs) q v.smooth v.interior_support) x) = 0
    rw [hgrad]
    exact (q.inner x (X x)).map_zero
  rw [hv, hΔ, ha]
  ring

omit [T2Space M] [CompactSpace M] in
private theorem notMem_tsupport_of_mem_chart_target_sdiff_interior
    {q : SmoothRiemannianMetric I_hs M} (α : M) (v : SmoothScalarDirichlet q)
    {y : EuN} (hy : y ∈ (extChartAt I_hs α).target \ interior (extChartAt I_hs α).target) :
    (extChartAt I_hs α).symm y ∉ tsupport v.toFun := by
  intro hys
  have hsrc := (extChartAt I_hs α).map_target hy.1
  rw [extChartAt_source_eq_chartAt_source (I := I_hs)] at hsrc
  have hi := extChartAt_mem_interior_target_of_isInteriorPoint (I := I_hs) α hsrc
    (v.interior_support hys)
  rw [(extChartAt I_hs α).right_inv hy.1] at hi
  exact hy.2 hi

theorem integral_adjoint_test_eq_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a : ℝ) (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (v : SmoothScalarDirichlet q) (hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    (∫ x, u x *
      (ΔGWithBoundary (I := I_hs) h v.smooth v.interior_support x -
        tangentSectionAction (I := I_hs) X v.toFun x -
        divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) h) X x * v.toFun x -
        a * v.toFun x) ∂(riemannianVolumeMeasure (I := I_hs) (M := M) h)) =
      ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) h α y * u ((extChartAt I_hs α).symm y) *
          (chartVossWeylLaplacian (I := I_hs) h α v.toFun ((extChartAt I_hs α).symm y) -
            (∑ i : Fin (Module.finrank ℝ EuN), chartCoeffOnE (I := I_hs) α X i y *
              partialDeriv (E := EuN) i (scalarOnE (I := I_hs) α v.toFun) y) -
            localDivergence (I := I_hs) h α X ((extChartAt I_hs α).symm y) *
              scalarOnE (I := I_hs) α v.toFun y - a * scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN)) := by
  let b : M → ℝ := fun x => ΔGWithBoundary (I := I_hs) h v.smooth v.interior_support x -
    tangentSectionAction (I := I_hs) X v.toFun x -
    divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) h) X x * v.toFun x -
    a * v.toFun x
  have hb : Continuous b :=
    (((Δ_g_with_boundary_continuous (I := I_hs) h v.smooth v.interior_support).sub
      (tangentSectionAction_continuous_of_interior_support X v.smooth v.interior_support)).sub
        ((leviCivita_divergence_contMDiff h X).continuous.mul v.smooth.continuous)).sub
          (v.smooth.continuous.const_mul a)
  change (∫ x, u x * b x ∂(riemannianVolumeMeasure (I := I_hs) (M := M) h)) = _
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.integral_eq_integral_chartDensity_of_support_in_chart
    h α (f := fun x => u x * b x) ((Lp.stronglyMeasurable u).measurable.mul hb.measurable) (fun x hx => by
      rw [show b x = 0 from adjoint_test_eq_zero_of_notMem_tsupport h X a v
        (fun hxs => hx (hv hxs)), mul_zero])]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_extChartAt_target (I := I_hs) α) interior_subset
      (fun y hy => by
        rw [show b ((extChartAt I_hs α).symm y) = 0 from
          adjoint_test_eq_zero_of_notMem_tsupport h X a v
            (notMem_tsupport_of_mem_chart_target_sdiff_interior α v hy), mul_zero, mul_zero])]
  apply setIntegral_congr_fun isOpen_interior.measurableSet
  intro y hy
  have hsrc := (extChartAt I_hs α).map_target (interior_subset hy)
  rw [extChartAt_source_eq_chartAt_source (I := I_hs)] at hsrc
  have hright := (extChartAt I_hs α).right_inv (interior_subset hy)
  have hi : (extChartAt I_hs α).symm y ∈ (I_hs).interior M := by
    apply ((I_hs).isInteriorPoint_iff_of_mem_atlas (M := M) (n := ∞)
      (by simp) (chart_mem_atlas (EuclideanHalfSpace n) α) hsrc).2
    change extChartAt I_hs α ((extChartAt I_hs α).symm y) ∈
      interior (extChartAt I_hs α).target
    rwa [hright]
  have hdiv : divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) h) X
        ((extChartAt I_hs α).symm y) =
      localDivergence (I := I_hs) h α X ((extChartAt I_hs α).symm y) := by
    rw [← divergence_g_eq_leviCivita_divergence_of_isInteriorPoint (I := I_hs) h X hi,
      ← divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint h X hi,
      voss_weyl_divergence_with_boundary_formula h α X hsrc hi,
      localDivergenceWithin_eq_localDivergence_of_isInteriorPoint h α X hsrc hi]
  dsimp only [b]
  rw [voss_weyl_laplacian_with_boundary_formula h α v.smooth v.interior_support hsrc hi,
    tangentSectionAction_chartLocal α X v.smooth hsrc (hright.symm ▸ hy), hdiv, hright]
  simp only [chartDensityOnE, scalarOnE, chartCoeffOnE]
  ring

theorem integral_mul_smooth_test_eq_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (v : SmoothScalarDirichlet q) (hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    {c : M → ℝ} (hc : Measurable c) :
    (∫ x, c x * (u x * v.toFun x)
      ∂(riemannianVolumeMeasure (I := I_hs) (M := M) h)) =
      ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) h α y *
          (c ((extChartAt I_hs α).symm y) *
            (u ((extChartAt I_hs α).symm y) * scalarOnE (I := I_hs) α v.toFun y))
        ∂(modelHaar (E := EuN)) := by
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.integral_eq_integral_chartDensity_of_support_in_chart
    h α (f := fun x => c x * (u x * v.toFun x)) (hc.mul ((Lp.stronglyMeasurable u).measurable.mul v.smooth.continuous.measurable))
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hxs => hx (hv hxs)), mul_zero, mul_zero])]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_extChartAt_target (I := I_hs) α) interior_subset
      (fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport
          (notMem_tsupport_of_mem_chart_target_sdiff_interior α v hy), mul_zero, mul_zero, mul_zero])

theorem IsWeakEvolutionSolution.exists_timeH1_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯}
    {a : ℝ → ℝ} {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (α : M) (v : SmoothScalarDirichlet q)
    (hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    ∃ w : timeH1 ℝ T,
      w.init = ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) (G.metric 0) α y *
          (f₀ ((extChartAt I_hs α).symm y) * scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN)) ∧
      (fun t => ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) (G.metric t) α y *
          (H1ComplDirichletToLp q (u t) ((extChartAt I_hs α).symm y) *
            scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN))) =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] fun t =>
        (∫ y in interior (extChartAt I_hs α).target,
          chartDensityOnE (I := I_hs) (G.metric t) α y *
            ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t
                ((extChartAt I_hs α).symm y) *
              (H1ComplDirichletToLp q (u t) ((extChartAt I_hs α).symm y) *
                scalarOnE (I := I_hs) α v.toFun y)) ∂(modelHaar (E := EuN))) +
        ∫ y in interior (extChartAt I_hs α).target,
          chartDensityOnE (I := I_hs) (G.metric t) α y *
            H1ComplDirichletToLp q (u t) ((extChartAt I_hs α).symm y) *
            (chartVossWeylLaplacian (I := I_hs) (G.metric t) α v.toFun
                ((extChartAt I_hs α).symm y) -
              (∑ i : Fin (Module.finrank ℝ EuN), chartCoeffOnE (I := I_hs) α (X t) i y *
                partialDeriv (E := EuN) i (scalarOnE (I := I_hs) α v.toFun) y) -
              localDivergence (I := I_hs) (G.metric t) α (X t) ((extChartAt I_hs α).symm y) *
                scalarOnE (I := I_hs) α v.toFun y - a t * scalarOnE (I := I_hs) α v.toFun y)
          ∂(modelHaar (E := EuN)) := by
  obtain ⟨w, hwinit, hwmass, hwderiv⟩ := hu.exists_timeH1_integral v
  have hm (t : ℝ) (U : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) :
      (∫ x, U x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) =
      ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) (G.metric t) α y *
          (U ((extChartAt I_hs α).symm y) * scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN)) := by
    simpa only [one_mul] using integral_mul_smooth_test_eq_integral_chart
      (G.metric t) α U v hv (c := fun _ => 1) measurable_const
  have htr : ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I_hs) G.metric p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    apply continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
      (I := I_hs) (M := M) (g := G.metric) D.regular_isOpen
    intro β i j
    exact hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) β i j
  have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Ico (0 : ℝ) T := by
    unfold timeMeasure
    rw [← restrict_Ico_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ico
  refine ⟨w, hwinit.trans (hm 0 f₀), ?_, ?_⟩
  · filter_upwards [hwmass] with t ht
    exact (hm t (H1ComplDirichletToLp q (u t))).symm.trans ht
  · filter_upwards [hwderiv, hmem] with t ht htc
    rw [ht, integral_adjoint_test_eq_integral_chart (G.metric t) α (X t) (a t)
      (H1ComplDirichletToLp q (u t)) v hv]
    congr 1
    have hc : Measurable
        (fun x : M => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t x) := by
      have hct : Continuous (fun x : M => traceTimeDerivMetric (I := I_hs) G.metric t x) := by
        simpa only [Function.comp_def] using htr.comp_continuous
          (f := fun x : M => (t, x)) (continuous_const.prodMk continuous_id)
          (fun x => ⟨hreg ⟨htc.1, htc.2.le⟩, Set.mem_univ x⟩)
      exact (hct.const_mul (1 / 2 : ℝ)).measurable
    exact integral_mul_smooth_test_eq_integral_chart
      (G.metric t) α (H1ComplDirichletToLp q (u t)) v hv hc

omit [T2Space M] [CompactSpace M] [IsManifold I_hs ∞ M] in
private theorem scalarOnE_chartPullback_eq
    (α : M) (ψ : EuStd → ℝ) {y : EuN}
    (hy : y ∈ (extChartAt I_hs α).target) :
    scalarOnE (I := I_hs) α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ) y =
      ψ (toEuclidean (E := EuN) y) := by
  have hsrc := (extChartAt I_hs α).map_target hy
  rw [extChartAt_source] at hsrc
  rw [scalarOnE, DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_mem α ψ hsrc,
    (extChartAt I_hs α).right_inv hy]

omit [T2Space M] [CompactSpace M] [IsManifold I_hs ∞ M] in
private theorem partialDeriv_scalarOnE_chartPullback
    (α : M) (ψ : EuStd → ℝ) {y : EuN}
    (hy : y ∈ interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) :
    partialDeriv (E := EuN) i (scalarOnE (I := I_hs) α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ)) y =
      fderiv ℝ ψ (toEuclidean (E := EuN) y) (EuclideanSpace.single i 1) := by
  have heq : scalarOnE (I := I_hs) α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ) =ᶠ[𝓝 y]
        ψ ∘ (toEuclidean (E := EuN)) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    exact scalarOnE_chartPullback_eq α ψ (interior_subset hz)
  rw [partialDeriv, heq.fderiv_eq, (toEuclidean (E := EuN)).comp_right_fderiv,
    ContinuousLinearMap.comp_apply, chartModelBasis_apply]
  simp

omit [T2Space M] [CompactSpace M] in
private theorem chartVossWeylLaplacian_chartPullback
    (h : SmoothRiemannianMetric I_hs M) (α : M) (ψ : EuStd → ℝ) {y : EuN}
    (hy : y ∈ interior (extChartAt I_hs α).target) :
    chartVossWeylLaplacian (I := I_hs) h α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ)
        ((extChartAt I_hs α).symm y) =
      (∑ i : Fin (Module.finrank ℝ EuN),
        fderiv ℝ (fun z : EuStd =>
          (∑ j : Fin (Module.finrank ℝ EuN),
            chartInvGramOnE (I := I_hs) h α i j ((toEuclidean (E := EuN)).symm z) *
              fderiv ℝ ψ z (EuclideanSpace.single j 1)) *
            chartDensityOnE (I := I_hs) h α ((toEuclidean (E := EuN)).symm z))
          (toEuclidean (E := EuN) y) (EuclideanSpace.single i 1)) /
        chartDensityOnE (I := I_hs) h α y := by
  rw [chartVossWeylLaplacian, (extChartAt I_hs α).right_inv (interior_subset hy)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let F : EuStd → ℝ := fun z =>
    (∑ j : Fin (Module.finrank ℝ EuN),
      chartInvGramOnE (I := I_hs) h α i j ((toEuclidean (E := EuN)).symm z) *
        fderiv ℝ ψ z (EuclideanSpace.single j 1)) *
      chartDensityOnE (I := I_hs) h α ((toEuclidean (E := EuN)).symm z)
  have heq : chartVossWeylIntegrand (I := I_hs) h α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ) i =ᶠ[𝓝 y]
        F ∘ (toEuclidean (E := EuN)) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    simp only [chartVossWeylIntegrand, gradChartCoeffOnE, Function.comp_apply, F,
      ContinuousLinearEquiv.symm_apply_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [partialDeriv_scalarOnE_chartPullback α ψ hz j]
  rw [partialDeriv, heq.fderiv_eq, (toEuclidean (E := EuN)).comp_right_fderiv,
    ContinuousLinearMap.comp_apply, chartModelBasis_apply]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rfl

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem IsWeakEvolutionSolution.exists_timeH1_integral_euclidean
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯}
    {a : ℝ → ℝ} {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (α : M) (ψ : EuStd → ℝ)
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆
      toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    let e := toEuclidean (E := EuN)
    let Ω := e '' interior (extChartAt I_hs α).target
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    ∃ w : timeH1 ℝ T,
      w.init = ∫ z in Ω, ρ 0 z * (f₀ (x z) * ψ z) ∧
      (fun t => ∫ z in Ω, ρ t z * (H1ComplDirichletToLp q (u t) (x z) * ψ z))
        =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] fun t =>
        (∫ z in Ω, ρ t z *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
            (H1ComplDirichletToLp q (u t) (x z) * ψ z))) +
        ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) *
          ((∑ i : Fin (Module.finrank ℝ EuN),
            fderiv ℝ (fun z' : EuStd =>
              (∑ j : Fin (Module.finrank ℝ EuN),
                A t i j z' * fderiv ℝ ψ z' (EuclideanSpace.single j 1)) * ρ t z') z
                (EuclideanSpace.single i 1)) / ρ t z -
            (∑ i : Fin (Module.finrank ℝ EuN), B t i z *
              fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
            localDivergence (I := I_hs) (G.metric t) α (X t) (x z) * ψ z - a t * ψ z) := by
  let e := toEuclidean (E := EuN)
  let Ω := e '' interior (extChartAt I_hs α).target
  let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
  let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
  let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
  let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
  have hs : tsupport ψ ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I_hs) (M := M) α :=
    hψ_supp.trans (Set.image_mono interior_subset)
  let v : SmoothScalarDirichlet q :=
    ⟨DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff α hψ_smooth hψ_cpt hs,
      DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset_interior
        α hψ_cpt hψ_supp⟩
  have hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source := by
    intro z hz
    obtain ⟨y, ⟨z', hz', rfl⟩, rfl⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset α hψ_cpt hs hz
    have ht : e.symm z' ∈ (extChartAt I_hs α).target := by
      have hz's := hs hz'
      rwa [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm]
        at hz's
    have hm := (extChartAt I_hs α).map_target ht
    rwa [extChartAt_source] at hm
  have hΩ : IsOpen Ω := e.toHomeomorph.isOpenMap _ isOpen_interior
  have hy {z : EuStd} (hz : z ∈ Ω) : e.symm z ∈ interior (extChartAt I_hs α).target := by
    obtain ⟨y, hy, rfl⟩ := hz
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy
  have he : MeasurePreserving e (modelHaar (E := EuN)) volume :=
    ⟨e.continuous.measurable, map_toEuclidean_modelHaar_eq_volume (E := EuN)⟩
  have hchange (F : EuN → ℝ) :
      (∫ y in interior (extChartAt I_hs α).target, F y ∂(modelHaar (E := EuN))) =
      ∫ z in Ω, F (e.symm z) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (he.setIntegral_image_emb e.toHomeomorph.measurableEmbedding
        (fun z => F (e.symm z)) (interior (extChartAt I_hs α).target)).symm
  have hm (t : ℝ) (U : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (c : M → ℝ) :
      (∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) (G.metric t) α y *
          (c ((extChartAt I_hs α).symm y) *
            (U ((extChartAt I_hs α).symm y) * scalarOnE (I := I_hs) α v.toFun y))
        ∂(modelHaar (E := EuN))) =
      ∫ z in Ω, ρ t z * (c (x z) * (U (x z) * ψ z)) := by
    rw [hchange]
    apply setIntegral_congr_fun hΩ.measurableSet
    intro z hz
    change _ * (_ * (_ * scalarOnE (I := I_hs) α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ) (e.symm z))) = _
    rw [scalarOnE_chartPullback_eq α ψ (interior_subset (hy hz))]
    simp only [e, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hm₀ (t : ℝ) (U : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) :
      (∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) (G.metric t) α y *
          (U ((extChartAt I_hs α).symm y) * scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN))) =
      ∫ z in Ω, ρ t z * (U (x z) * ψ z) := by
    simpa only [one_mul] using hm t U (fun _ => 1)
  have ha (t : ℝ) :
      (∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) (G.metric t) α y *
          H1ComplDirichletToLp q (u t) ((extChartAt I_hs α).symm y) *
          (chartVossWeylLaplacian (I := I_hs) (G.metric t) α v.toFun
              ((extChartAt I_hs α).symm y) -
            (∑ i : Fin (Module.finrank ℝ EuN), chartCoeffOnE (I := I_hs) α (X t) i y *
              partialDeriv (E := EuN) i (scalarOnE (I := I_hs) α v.toFun) y) -
            localDivergence (I := I_hs) (G.metric t) α (X t) ((extChartAt I_hs α).symm y) *
              scalarOnE (I := I_hs) α v.toFun y - a t * scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN))) =
      ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) *
        ((∑ i : Fin (Module.finrank ℝ EuN),
          fderiv ℝ (fun z' : EuStd =>
            (∑ j : Fin (Module.finrank ℝ EuN),
              A t i j z' * fderiv ℝ ψ z' (EuclideanSpace.single j 1)) * ρ t z') z
              (EuclideanSpace.single i 1)) / ρ t z -
          (∑ i : Fin (Module.finrank ℝ EuN), B t i z *
            fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
          localDivergence (I := I_hs) (G.metric t) α (X t) (x z) * ψ z - a t * ψ z) := by
    rw [hchange]
    apply setIntegral_congr_fun hΩ.measurableSet
    intro z hz
    dsimp only [v]
    rw [chartVossWeylLaplacian_chartPullback (G.metric t) α ψ (hy hz),
      scalarOnE_chartPullback_eq α ψ (interior_subset (hy hz))]
    simp_rw [partialDeriv_scalarOnE_chartPullback α ψ (hy hz)]
    simp only [e, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨w, hwinit, hwmass, hwderiv⟩ := hu.exists_timeH1_integral_chart α v hv
  refine ⟨w, hwinit.trans (hm₀ 0 f₀), ?_, ?_⟩
  · filter_upwards [hwmass] with t ht
    exact (hm₀ t (H1ComplDirichletToLp q (u t))).symm.trans ht
  · filter_upwards [hwderiv] with t ht
    rw [ht, ha]
    congr 1
    exact hm t (H1ComplDirichletToLp q (u t))
      (fun x => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t x)

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
