import DifferentialGeometry.Analysis.Integration.Integral.Prod
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakFormChart
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartPullbackLp
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatWeakEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficients

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuN := borel _
private local instance : BorelSpace EuN := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private theorem integral_mul_add_mul_chartPullback_eq_integral
    (g : SmoothRiemannianMetric I_hs M) (α : M)
    {U c : M → ℝ} (hU : Measurable U) (hc : Measurable c)
    {ψ φ : EuStd → ℝ} (hψ : Measurable ψ) (hφ : Measurable φ)
    {Ω : Set EuStd} (hΩt : Ω ⊆ Sobolev.Chart.chartTargetEuclid (I := I_hs) α)
    (hψs : Function.support ψ ⊆ Ω) (hφs : Function.support φ ⊆ Ω) :
    (∫ x, U x * (chartPullback I_hs α ψ x + c x * chartPullback I_hs α φ x)
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) g) =
      ∫ z in Ω, chartDensityOnE (I := I_hs) g α ((toEuclidean (E := EuN)).symm z) *
        U ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
          (ψ z + c ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) * φ z) := by
  let e := toEuclidean (E := EuN)
  have he : MeasurePreserving e (modelHaar (E := EuN)) volume :=
    ⟨e.continuous.measurable, map_toEuclidean_modelHaar_eq_volume (E := EuN)⟩
  rw [integral_eq_integral_chartDensity_of_support_in_chart g α
    (f := fun x => U x * (chartPullback I_hs α ψ x + c x * chartPullback I_hs α φ x))
    (hU.mul ((measurable_chartPullback (I := I_hs) α hψ).add (hc.mul (measurable_chartPullback (I := I_hs) α hφ))))
    (fun x hx => by
      rw [chartPullback_apply_of_notMem α ψ hx, chartPullback_apply_of_notMem α φ hx]
      simp only [mul_zero, add_zero])]
  have hpoint (f : EuStd → ℝ) {y : EuN} (hy : y ∈ (extChartAt I_hs α).target) :
      chartPullback I_hs α f ((extChartAt I_hs α).symm y) = f (e y) := by
    have hs := (extChartAt I_hs α).map_target hy
    rw [extChartAt_source] at hs
    rw [chartPullback_apply_of_mem α f hs, (extChartAt I_hs α).right_inv hy]
  calc
    _ = ∫ y in (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) g α y * U ((extChartAt I_hs α).symm y) *
          (ψ (e y) + c ((extChartAt I_hs α).symm y) * φ (e y)) ∂modelHaar (E := EuN) := by
      apply setIntegral_congr_fun (measurableSet_extChartAt_target (I := I_hs) α)
      intro y hy
      dsimp only
      rw [hpoint ψ hy, hpoint φ hy, mul_assoc]
      rfl
    _ = ∫ z in e '' (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) g α (e.symm z) * U ((extChartAt I_hs α).symm (e.symm z)) *
          (ψ z + c ((extChartAt I_hs α).symm (e.symm z)) * φ z) := by
      rw [he.setIntegral_image_emb e.toHomeomorph.measurableEmbedding]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
        (measurableSet_extChartAt_target (I := I_hs) α)) hΩt (fun z hz => by
        rw [Function.notMem_support.mp (fun hs => hz.2 (hψs hs)),
          Function.notMem_support.mp (fun hs => hz.2 (hφs hs))]
        simp only [mul_zero, add_zero]))

private theorem integral_chart_test_of_heat_timeH1
    (q : SmoothRiemannianMetric I_hs M) (g : ℝ → SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z))
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {φ : ℝ × EuStd → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφi : tsupport φ ⊆ Ioo (0 : ℝ) T ×ˢ Ω) :
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (g t) α ((toEuclidean (E := EuN)).symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (g t) α i j ((toEuclidean (E := EuN)).symm z)
    (∫ t, ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) *
      (fderiv ℝ φ (t, z) (1, 0) + (1 / 2) *
        traceTimeDerivMetric (I := I_hs) g t (x z) * φ (t, z)) ∂volume ∂timeMeasure T) +
      (∫ t, (-(∑ i, ∫ z in Ω, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z *
        ((∑ j, A t i j z * fderiv ℝ (fun y => φ (t, y)) z (EuclideanSpace.single j 1)) * ρ t z))) +
          ∫ z in Ω, ρ t z * f t (x z) * φ (t, z) ∂volume ∂timeMeasure T) = 0 := by
  intro x ρ A
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let Ψ := fun p : ℝ × M => chartPullback I_hs α (fun y => φ (p.1, y)) p.2
  have hΩt : Ω ⊆ Sobolev.Chart.chartTargetEuclid (I := I_hs) α :=
    subset_closure.trans (hΩs.trans (image_mono interior_subset))
  have hφt : tsupport φ ⊆ univ ×ˢ Sobolev.Chart.chartTargetEuclid (I := I_hs) α :=
    hφi.trans (prod_mono (subset_univ _) hΩt)
  have hΨ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ Ψ :=
    chartPullback_contMDiff_prod_of_hasCompactSupport α hφ hφc hφt
  have hΨc : HasCompactSupport Ψ := hasCompactSupport_chartPullback_prod α hφc hφt
  have hΨs : tsupport Ψ ⊆ Ioo (0 : ℝ) T ×ˢ (I_hs).interior M :=
    tsupport_chartPullback_prod_subset_interior α hφc
      (hφi.trans (prod_mono Subset.rfl (subset_closure.trans hΩs)))
  have hΨi : tsupport Ψ ⊆ D.regular ×ˢ (I_hs).interior M :=
    hΨs.trans (prod_mono (Ioo_subset_Icc_self.trans hreg) Subset.rfl)
  have hΨ0 (y : M) : Ψ (0, y) = 0 :=
    image_eq_zero_of_notMem_tsupport fun hy => (lt_irrefl 0) (hΨs hy).1.1
  have hΨT (y : M) : Ψ (T, y) = 0 :=
    image_eq_zero_of_notMem_tsupport fun hy => (lt_irrefl T) (hΨs hy).1.2
  have hderiv (t : ℝ) (y : M) : deriv (fun s => Ψ (s, y)) t =
      chartPullback I_hs α (fun z => fderiv ℝ φ (t, z) (1, 0)) y := by
    apply HasDerivAt.deriv
    change HasDerivAt (fun s => chartPullback I_hs α (fun z => φ (s, z)) y) _ t
    by_cases hy : y ∈ (chartAt (EuclideanHalfSpace n) α).source
    · simp_rw [chartPullback_apply_of_mem (I := I_hs) α _ hy]
      exact (hφ.differentiable (by simp) (t, toEuclidean (extChartAt I_hs α y))).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t (toEuclidean (extChartAt I_hs α y))))
    · simp_rw [chartPullback_apply_of_notMem (I := I_hs) α _ hy]
      exact hasDerivAt_const t 0
  have hslice (t : ℝ) : ContDiff ℝ ∞ (fun z => φ (t, z)) :=
    hφ.comp (contDiff_const.prodMk contDiff_id)
  have hslice_s (t : ℝ) : tsupport (fun z => φ (t, z)) ⊆ Ω := by
    intro z hz
    exact (hφi (tsupport_comp_subset_preimage φ
      (continuous_const.prodMk continuous_id) hz)).2
  have hdt_s (t : ℝ) : tsupport (fun z => fderiv ℝ φ (t, z) (1, 0)) ⊆ Ω := by
    intro z hz
    exact (hφi (tsupport_fderiv_apply_subset ℝ (1, 0)
      (tsupport_comp_subset_preimage (fun p => fderiv ℝ φ p (1, 0))
        (continuous_const.prodMk continuous_id) hz))).2
  have hdt_m (t : ℝ) : Measurable (fun z => fderiv ℝ φ (t, z) (1, 0)) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id)).measurable
  have h := integral_spacetime_test_evolving_volume_of_heat_timeH1 q g hG hT hreg hCg hequiv
    Cv hCv0 hCvtop hvol u f w hwmass hwderiv hΨ hΨc hΨi hΨ0 hΨT
  refine Eq.trans ?_ h
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have htracej := continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
      D.regular_isOpen (fun α i j => hG.chartGramMatrix_contDiffOn (G := G) Subset.rfl α i j)
    have htrace : Continuous (fun y : M => traceTimeDerivMetric (I := I_hs) g t y) := by
      simpa only [Function.comp_def] using htracej.comp_continuous
        (f := fun y : M => (t, y)) (continuous_const.prodMk continuous_id)
        (fun y => ⟨hreg ht, mem_univ y⟩)
    simp_rw [hderiv]
    exact (integral_mul_add_mul_chartPullback_eq_integral (g t) α
      (Lp.stronglyMeasurable _).measurable (htrace.const_mul (1 / 2 : ℝ)).measurable
      (hdt_m t) (hslice t).continuous.measurable hΩt
      ((subset_tsupport _).trans (hdt_s t)) ((subset_tsupport _).trans (hslice_s t))).symm
  · apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      apply congrArg₂ (fun a b : ℝ => a + b)
      · exact (integral_mul_laplacian_chartPullback_eq_neg_sum_integral (g t) α hΩ hΩc hΩs
          (u t) (hslice t) (hΩc.of_isClosed_subset (isClosed_tsupport _)
            ((hslice_s t).trans subset_closure)) (hslice_s t)).symm
      · have he := Sobolev.Chart.integral_mul_chartPullback_eq_integral_euclidean
          (g t) α (Lp.stronglyMeasurable (f t)).measurable (hslice t).continuous.measurable
          (((subset_tsupport _).trans (hslice_s t)).trans hΩt)
        refine Eq.trans ?_ he.symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        rw [image_eq_zero_of_notMem_tsupport (fun hs => hz (hslice_s t hs)), mul_zero]

theorem integral_spacetime_test_divergence_of_heat_timeH1
    (q : SmoothRiemannianMetric I_hs M) (g : ℝ → SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z))
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {φ : ℝ × EuStd → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφi : tsupport φ ⊆ Ioo (0 : ℝ) T ×ˢ Ω) :
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    let ν := (timeMeasure T).prod (volume.restrict Ω)
    (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
      (∑ i, ∑ j, ∫ p, A i j p * V i p *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
      ∫ p, ρ p * ((1 / 2) * traceTimeDerivMetric (I := I_hs) g p.1 (x p.2) * U p + F p) * φ p ∂ν := by
  intro ρ A x U V F ν
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let : IsFiniteMeasure (volume.restrict Ω) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩc.measure_lt_top
  have hρ : MemLp ρ ∞ ν := by
    have h := densityOnEuclid_family_memLp_top (G := G) hG isCompact_Icc hreg α
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) (volume.prod volume)
    simpa only [ν, timeMeasure, ← Measure.prod_restrict] using h
  have hA (i j) : MemLp (A i j) ∞ ν := by
    have h := weightedInvGramOnEuclid_family_memLp_top (G := G) hG isCompact_Icc hreg α
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) i j (volume.prod volume)
    simpa only [ν, timeMeasure, ← Measure.prod_restrict] using h
  let τ := fun p : ℝ × EuStd => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) g p.1 (x p.2)
  have hτ : MemLp τ ∞ ν := by
    have h := traceTimeDerivMetric_comp_chartInverse_memLp_top (G := G) hG isCompact_Icc hreg α
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) (volume.prod volume)
    simpa only [τ, ν, timeMeasure, ← Measure.prod_restrict] using h.const_mul (1 / 2 : ℝ)
  have hφp : MemLp φ ∞ ν := hφ.continuous.memLp_top_of_hasCompactSupport hφc ν
  have hd (v : ℝ × EuStd) : MemLp (fun p => fderiv ℝ φ p v) ∞ ν :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hφc.fderiv_apply ℝ v) ν
  let Q := fun i j (p : ℝ × EuStd) => A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
  let L := fun p => ρ p * (τ p * U p + F p) * φ p
  let R := fun p => ρ p * U p * (fderiv ℝ φ p (1, 0) + τ p * φ p)
  let S := fun p => ρ p * F p * φ p
  let K := fun p => -(∑ i, ∑ j, Q i j p) + S p
  have hQ (i j) : Integrable (Q i j) ν :=
    (((hA i j).fun_mul (r := 2) (Lp.memLp (V i))).fun_mul (r := 2)
      (hd (0, EuclideanSpace.single j 1))).integrable (by norm_num)
  have hL : Integrable L ν :=
    ((hρ.fun_mul (r := 2)
      ((hτ.fun_mul (r := 2) (Lp.memLp U)).add (Lp.memLp F))).fun_mul
        (r := 2) hφp).integrable (by norm_num)
  have hR : Integrable R ν :=
    ((hρ.fun_mul (r := 2) (Lp.memLp U)).fun_mul (r := 2)
      ((hd (1, 0)).add (hτ.fun_mul (r := ∞) hφp))).integrable (by norm_num)
  have hS : Integrable S ν :=
    ((hρ.fun_mul (r := 2) (Lp.memLp F)).fun_mul (r := 2) hφp).integrable (by norm_num)
  have hsum : Integrable (fun p => ∑ i, ∑ j, Q i j p) ν :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hQ i j
  have hK : Integrable K ν := hsum.neg.add hS
  have hU := dirichletLocalSpacetimeLp_coeFn q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
  have hV : ∀ᵐ t ∂timeMeasure T, ∀ i,
      (fun z => V i (t, z)) =ᵐ[volume.restrict Ω]
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) : EuStd → ℝ) :=
    ae_all_iff.mpr fun i =>
      dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u
  have hF : ∀ᵐ t ∂timeMeasure T,
      (fun z => F (t, z)) =ᵐ[volume.restrict Ω] fun z => f t (x z) := by
    filter_upwards [Lp.uncurry_compLpL_coeFn (𝕜 := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2) f] with t ht
    exact Filter.EventuallyEq.trans ht (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2 (f t))
  have hsp (t : ℝ) (z v : EuStd) :
      fderiv ℝ (fun y => φ (t, y)) z v = fderiv ℝ φ (t, z) (0, v) := by
    have h := ((hφ.differentiable (by simp)) (t, z)).hasFDerivAt.comp z
      ((hasFDerivAt_const t z).prodMk (hasFDerivAt_id z))
    exact congrArg (fun L => L v) h.fderiv
  have hzero : (∫ p, R p ∂ν) + (∫ p, K p ∂ν) = 0 := by
    have h := integral_chart_test_of_heat_timeH1 q g hG hT hreg hCg hequiv Cv hCv0 hCvtop hvol
      u f w hwmass hwderiv α hΩ hΩc hΩs hφ hφc hφi
    refine Eq.trans ?_ h
    apply congrArg₂ (fun a b : ℝ => a + b)
    · rw [integral_prod _ hR]
      apply integral_congr_ae
      filter_upwards [hU] with t ht
      apply integral_congr_ae
      filter_upwards [ht] with z hz
      dsimp only [R]
      rw [hz]
      rfl
    · rw [integral_prod _ hK]
      have hQae : ∀ᵐ t ∂timeMeasure T, ∀ i j,
          Integrable (fun z => Q i j (t, z)) (volume.restrict Ω) :=
        ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hQ i j).prod_right_ae
      apply integral_congr_ae
      filter_upwards [hV, hF, hQae, hS.prod_right_ae] with t hvt hft hqt hst
      have hsumt : Integrable (fun z => ∑ i, ∑ j, Q i j (t, z)) (volume.restrict Ω) :=
        integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hqt i j
      change (∫ z in Ω, -(∑ i, ∑ j, Q i j (t, z)) + S (t, z)) = _
      rw [integral_add (f := fun z => -(∑ i, ∑ j, Q i j (t, z))) hsumt.neg hst, integral_neg,
        integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hqt i j)]
      apply congrArg₂ (fun a b : ℝ => a + b)
      · congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply integral_congr_ae
        filter_upwards [hvt i] with z hz
        simp only [Q, A, hz, weightedInvGramOnEuclid, densityOnEuclid, invGramOnEuclid,
          chartInvGramOnE, chartDensityOnE,
          hsp, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · apply integral_congr_ae
        filter_upwards [hft] with z hz
        dsimp only [S]
        rw [hz]
        rfl
  have htime : Integrable (fun p => ρ p * U p * fderiv ℝ φ p (1, 0)) ν :=
    ((hρ.fun_mul (r := 2) (Lp.memLp U)).fun_mul (r := 2)
      (hd (1, 0))).integrable (by norm_num)
  have hsum_int : (∫ p, ∑ i, ∑ j, Q i j p ∂ν) = ∑ i, ∑ j, ∫ p, Q i j p ∂ν := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hQ i j)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ fun j _ => hQ i j
  have heq : (∫ p, R p ∂ν) + (∫ p, K p ∂ν) =
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) + (∫ p, L p ∂ν) -
        ∑ i, ∑ j, ∫ p, Q i j p ∂ν := by
    rw [← integral_add hR hK, ← integral_add htime hL, ← hsum_int]
    rw [← integral_sub (f := fun p => ρ p * U p * fderiv ℝ φ p (1, 0) + L p)
      (htime.add hL) hsum]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by dsimp only [R, K, S, L]; ring
  rw [heq] at hzero
  linarith

theorem integral_spacetime_test_divergence_restrict_of_heat_timeH1
    (q : SmoothRiemannianMetric I_hs M) (g : ℝ → SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z))
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {S : Set ℝ} {Ω₀ : Set EuStd} (hΩ₀ : MeasurableSet Ω₀) (hsub : Ω₀ ⊆ Ω)
    {φ : ℝ × EuStd → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφi : tsupport φ ⊆ Ioo (0 : ℝ) T ×ˢ Ω)
    (hφs : tsupport φ ⊆ S ×ˢ Ω₀) :
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    let ν := ((timeMeasure T).restrict S).prod (volume.restrict Ω₀)
    (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
      (∑ i, ∑ j, ∫ p, A i j p * V i p *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
      ∫ p, ρ p * ((1 / 2) * traceTimeDerivMetric (I := I_hs) g p.1 (x p.2) * U p + F p) * φ p ∂ν := by
  intro ρ A x U V F ν
  have hbase := integral_spacetime_test_divergence_of_heat_timeH1 q g hG hT hreg hCg hequiv
    Cv hCv0 hCvtop hvol u f w hwmass hwderiv α hΩ hΩc hΩs hφ hφc hφi
  have hres (v : ℝ × EuStd) (C : ℝ × EuStd → ℝ) :
      (∫ p, C p * fderiv ℝ φ p v ∂(timeMeasure T).prod (volume.restrict Ω)) =
        ∫ p, C p * fderiv ℝ φ p v ∂ν := by
    apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀ hsub
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ φ p v)
      (fun hs => hp (hφs (tsupport_fderiv_apply_subset ℝ v hs))), mul_zero]
  have hresφ (C : ℝ × EuStd → ℝ) :
      (∫ p, C p * φ p ∂(timeMeasure T).prod (volume.restrict Ω)) = ∫ p, C p * φ p ∂ν := by
    apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀ hsub
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hp (hφs hs)), mul_zero]
  dsimp only at hbase
  simp_rw [hres, hresφ] at hbase
  exact hbase

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
