import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowReducedVolume
import DifferentialGeometry.Analysis.Integration.Integral.GradientCutoff
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl


noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set MeasureTheory Bundle
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff ENNReal NNReal _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
private local instance (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    MeasurableSpace L.M := borel L.M
private local instance (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    BorelSpace L.M := ⟨rfl⟩

private theorem backward_flow_limit_cutoff_flux_integrable_and_tendsto
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ} (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ} (hT : 1 ≤ T)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hlim : ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))))
    (μ : MeasureTheory.Measure (Icc (1 : ℝ) T)) [IsFiniteMeasure μ]
    (ψ : C(Icc (1 : ℝ) T, ℝ)) :
    let f : NNReal → Icc (1 : ℝ) T × L.M → ℝ := fun b z =>
      riemannianVolumeDensity (L.S.base.metric 0) (L.S.base.metric (1 - z.1)) z.2 * ψ z.1 *
        (L.S.base.metric (1 - z.1)).inner z.2
          (gradFun (L.S.base.metric (1 - z.1))
            (perelmanDensity (Module.finrank ℝ E) z.1 (fun y => ell (y, z.1))) z.2)
          (gradFun (L.S.base.metric (1 - z.1)) (fun y => Analysis.CutoffProfile.evalue
            ((b : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint y)) z.2);
    (∀ b, Integrable (f b)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0)))) ∧
      ∀ {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
        (a : ι → NNReal), Tendsto a l (𝓝 0) →
          Tendsto (fun i => ∫ z, |f (a i) z|
            ∂(μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0)))) l (𝓝 0) := by
  intro f
  let _ : NeZero (Module.finrank ℝ E) := neZero_finrank_of_isAncientKappaSolution F hF
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : SecondCountableTopology L.M := ChartedSpace.secondCountable_of_sigmaCompact H L.M
  let g := L.S.base.metric 0
  let h : Icc (1 : ℝ) T → SmoothRiemannianMetric I L.M := fun theta => L.S.base.metric (1 - theta)
  let ρ : Icc (1 : ℝ) T × L.M → ℝ := fun z => riemannianVolumeDensity g (h z.1) z.2
  let u : Icc (1 : ℝ) T → L.M → ℝ := fun theta =>
    perelmanDensity (Module.finrank ℝ E) theta (fun y => ell (y, theta))
  have ht (theta : Icc (1 : ℝ) T) : 1 - (theta : ℝ) ∈ Icc (1 - T) (0 : ℝ) :=
    ⟨sub_le_sub_left theta.property.2 1, sub_nonpos.mpr theta.property.1⟩
  have hconv' (theta : Icc (1 : ℝ) T) := hconv (1 - theta) (ht theta)
  have href (t : ℝ) (ht : t ∈ Icc (1 - T) (0 : ℝ)) :
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
        ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric := by
    obtain ⟨C, hC⟩ := hconv t ht
    refine ⟨C, fun i => ?_⟩
    rw [hC i]
    exact canonicalSourceData_referenceMetric_eq_limitMetric _ i
  have hm : Integrable (fun z => ρ z * u z.1 z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) g)) :=
    integrable_backward_flow_limit_perelmanDensity F hF p tau htau q L hescape Phi
      hconv' (fun theta => hcomplete (1 - theta) (ht theta)) ell hlim μ g
  have hw : Integrable (fun z => |ψ z.1| * (ρ z * u z.1 z.2))
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) g)) :=
    hm.bdd_mul (c := ‖ψ‖) (ψ.continuous.comp continuous_fst).abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_abs] using ψ.norm_coe_le_norm z.1)
  have hu0 (theta : Icc (1 : ℝ) T) (x : L.M) : 0 ≤ u theta x :=
    (mul_pos (prefactor_pos _ (zero_lt_one.trans_le theta.property.1)) (Real.exp_pos _)).le
  have hρ0 (z : Icc (1 : ℝ) T × L.M) : 0 ≤ ρ z := (riemannianVolumeDensity_pos _ _ _).le
  have hmc (t : ℝ) (ht : t ∈ Icc (1 - T) (0 : ℝ)) (x : L.M) (v : TangentSpace I x) :
      Tendsto (fun n => (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
        (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x v))
        atTop (𝓝 ((L.S.base.metric t).inner x v v)) := by
    obtain ⟨C, hC⟩ := href t ht
    exact C.tendsto_pullback_inner hC x v v
  have hgh (theta : Icc (1 : ℝ) T) (x : L.M) (v : TangentSpace I x) :
      g.inner x v v ≤ (h theta).inner x v v :=
    backward_flow_limit_metric_inner_antitoneOn F hF tau htau q L Phi
      (J := Icc (1 - T) (0 : ℝ))
      (fun _ ht => ht.2) hmc x v (ht theta) ⟨sub_nonpos.mpr hT, le_rfl⟩ (ht theta).2
  obtain ⟨C, hC⟩ := exists_backward_flow_limit_perelmanDensity_gradient_le_linear_distance
    F hF p tau htau q L Phi hT href
      hcomplete ell (fun w => hlim w.2 w.1)
  have hρc : Continuous ρ :=
    (riemannianVolumeDensity_family_continuousOn g L.S.base.metric
      L.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier).comp_continuous
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
      (fun z => ⟨show 1 - (z.1 : ℝ) ≤ 0 from sub_nonpos.mpr z.1.property.1, mem_univ _⟩)
  have huc : Continuous u.uncurry := by
    unfold u perelmanDensity perelmanDensityPrefactor Function.uncurry
    apply Continuous.mul
    · apply Continuous.rpow_const
        (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
      intro z
      exact Or.inl (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (ne_of_gt (zero_lt_one.trans_le z.1.property.1)))
    · exact Real.continuous_exp.comp (ell.continuous.comp continuous_swap).neg
  have hhc : Continuous (fun z : Icc (1 : ℝ) T × L.M => (⟨z.2, (h z.1).inner z.2⟩ :
      TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) :=
    L.isSolution.smoothMetric.metricCLMSection_continuousOn_carrier.comp_continuous
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
      (fun z => ⟨show 1 - (z.1 : ℝ) ≤ 0 from sub_nonpos.mpr z.1.property.1, mem_univ _⟩)
  have hw' : Integrable (fun z => |ρ z * ψ z.1| * u z.1 z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) g)) := by
    apply hw.congr
    filter_upwards [] with z
    rw [abs_mul, abs_of_nonneg (hρ0 z)]
    ring
  have hv := (hρc.mul (ψ.continuous.comp continuous_fst)).measurable
  constructor
  · intro b
    exact Analysis.integrable_mul_inner_grad_distance_cutoff
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) g)) b g h hhc
      (Eventually.of_forall fun z => hgh z.1) huc (Eventually.of_forall fun z => hu0 z.1 z.2)
      hv hw' L.basepoint C (Eventually.of_forall fun z => hC z.1 z.2)
  · intro ι l _ a ha
    exact Analysis.tendsto_integral_abs_mul_inner_grad_distance_cutoff
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) g)) a ha g h hhc
      (Eventually.of_forall fun z => hgh z.1) huc (Eventually.of_forall fun z => hu0 z.1 z.2)
      hv hw' L.basepoint C (Eventually.of_forall fun z => hC z.1 z.2)

theorem integrable_backward_flow_limit_perelmanDensity_cutoff_flux
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ} (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ} (hT : 1 ≤ T)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hlim : ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))))
    (μ : MeasureTheory.Measure (Icc (1 : ℝ) T)) [IsFiniteMeasure μ]
    (ψ : C(Icc (1 : ℝ) T, ℝ))
    (b : NNReal) :
    Integrable (fun z : Icc (1 : ℝ) T × L.M =>
      riemannianVolumeDensity (L.S.base.metric 0) (L.S.base.metric (1 - z.1)) z.2 * ψ z.1 *
        (L.S.base.metric (1 - z.1)).inner z.2
          (gradFun (L.S.base.metric (1 - z.1))
            (perelmanDensity (Module.finrank ℝ E) z.1 (fun y => ell (y, z.1))) z.2)
          (gradFun (L.S.base.metric (1 - z.1)) (fun y => Analysis.CutoffProfile.evalue
            ((b : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint y)) z.2))
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0))) := by
  exact (backward_flow_limit_cutoff_flux_integrable_and_tendsto.{u, uE, uH, 0}
    F hF p tau htau q L hescape Phi hT hconv hcomplete ell hlim μ ψ).1 b

theorem tendsto_integral_abs_backward_flow_limit_perelmanDensity_cutoff_flux
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ} (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ} (hT : 1 ≤ T)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hlim : ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))))
    (μ : MeasureTheory.Measure (Icc (1 : ℝ) T)) [IsFiniteMeasure μ]
    (ψ : C(Icc (1 : ℝ) T, ℝ))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ≥0) (ha : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ z : Icc (1 : ℝ) T × L.M,
      |riemannianVolumeDensity (L.S.base.metric 0) (L.S.base.metric (1 - z.1)) z.2 * ψ z.1 *
        (L.S.base.metric (1 - z.1)).inner z.2
          (gradFun (L.S.base.metric (1 - z.1))
            (perelmanDensity (Module.finrank ℝ E) z.1 (fun y => ell (y, z.1))) z.2)
          (gradFun (L.S.base.metric (1 - z.1)) (fun y => Analysis.CutoffProfile.evalue
            ((a i : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint y)) z.2)|
      ∂(μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0)))) l (𝓝 0) := by
  exact (backward_flow_limit_cutoff_flux_integrable_and_tendsto
    F hF p tau htau q L hescape Phi hT hconv hcomplete ell hlim μ ψ).2 a ha

theorem tendsto_integral_backward_flow_limit_perelmanDensity_cutoff_flux
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ} (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ} (hT : 1 ≤ T)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hlim : ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))))
    (μ : MeasureTheory.Measure (Icc (1 : ℝ) T)) [IsFiniteMeasure μ]
    (ψ : C(Icc (1 : ℝ) T, ℝ))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ≥0) (ha : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ theta : Icc (1 : ℝ) T, ψ theta *
      ∫ x : L.M, (L.S.base.metric (1 - theta)).inner x
        (gradFun (L.S.base.metric (1 - theta))
          (perelmanDensity (Module.finrank ℝ E) theta (fun y => ell (y, theta))) x)
        (gradFun (L.S.base.metric (1 - theta)) (fun y => Analysis.CutoffProfile.evalue
          ((a i : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint y)) x)
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric (1 - theta)) ∂μ)
      l (𝓝 0) := by
  let g : Icc (1 : ℝ) T → SmoothRiemannianMetric I L.M := fun theta => L.S.base.metric (1 - theta)
  let V : ι → Icc (1 : ℝ) T × L.M → ℝ := fun i z =>
    (g z.1).inner z.2
      (gradFun (g z.1) (perelmanDensity (Module.finrank ℝ E) z.1 (fun y => ell (y, z.1))) z.2)
      (gradFun (g z.1) (fun y => Analysis.CutoffProfile.evalue
        ((a i : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint y)) z.2)
  let w : ι → Icc (1 : ℝ) T × L.M → ℝ := fun i z =>
    riemannianVolumeDensity (L.S.base.metric 0) (g z.1) z.2 * ψ z.1 * V i z
  have hi (i : ι) : Integrable (w i)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0))) :=
    integrable_backward_flow_limit_perelmanDensity_cutoff_flux F hF p tau htau q L hescape
      Phi hT hconv hcomplete ell hlim μ ψ (a i)
  have habs : Tendsto (fun i => ∫ z, |w i z|
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0))) l (𝓝 0) :=
    tendsto_integral_abs_backward_flow_limit_perelmanDensity_cutoff_flux F hF p tau htau q L hescape
      Phi hT hconv hcomplete ell hlim μ ψ a ha
  have hlimw : Tendsto (fun i => ∫ z, w i z
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0))) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) habs
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (w i)
  have heq (i : ι) : (∫ z, w i z
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0))) =
      ∫ theta, ψ theta * ∫ x, V i (theta, x)
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (g theta) ∂μ := by
    have hf : Integrable (fun z : Icc (1 : ℝ) T × L.M =>
        riemannianVolumeDensity (L.S.base.metric 0) (g z.1) z.2 • (ψ z.1 * V i z))
        (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0))) := by
      convert hi i using 1
      funext z
      simp only [w, smul_eq_mul, mul_assoc]
    calc
      _ = ∫ z, riemannianVolumeDensity (L.S.base.metric 0) (g z.1) z.2 • (ψ z.1 * V i z)
          ∂μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric 0)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [w, smul_eq_mul, mul_assoc]
      _ = ∫ theta, ∫ x, ψ theta * V i (theta, x)
          ∂riemannianVolumeMeasure (I := I) (M := L.M) (g theta) ∂μ :=
        integral_prod_volumeDensity_smul μ (L.S.base.metric 0) g (fun z => ψ z.1 * V i z) hf
      _ = _ := by simp only [integral_const_mul]
  simp_rw [heq] at hlimw
  exact hlimw


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
