import DifferentialGeometry.Analysis.Integration.Integral.CutoffProfile
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityIntegrability
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityContinuity
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeTightness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAsymptoticReducedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowReducedLength
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Volume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Scaling

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped _root_.Manifold ContDiff ENNReal _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩
private local instance (P : PointedRiemannianManifold.{u, uE, uH} I) :
    MeasurableSpace P.M := borel P.M
private local instance (P : PointedRiemannianManifold.{u, uE, uH} I) :
    BorelSpace P.M := ⟨rfl⟩

theorem lintegral_perelmanDensity_eq_asymptoticReducedVolume_of_backward_flow_limit
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {theta : ℝ} (htheta : 0 < theta)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) {phi : ℕ → ℕ}
    (hescape : Tendsto (tau ∘ phi) atTop atTop)
    (Phi : PointedRiemannianConvergenceMaps
      ((backwardFlowSequence F tau htau q).atTime (1 - theta)) P phi)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (hcomplete : MetricComplete P) (ell : P.M → ℝ)
    (hlim : ∀ x, Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (phi i) * theta))
      atTop (𝓝 (ell x))) :
    (∫⁻ x, ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) theta ell x)
      ∂riemannianVolumeMeasure (I := I) (M := P.M) P.metric) =
        asymptoticReducedVolume F.S 0 p := by
  let _ : NeZero (Module.finrank ℝ E) := neZero_finrank_of_isAncientKappaSolution F hF
  let _ : ConnectedSpace F.M := hF.connected
  let X := (backwardFlowSequence F tau htau q).atTime (1 - theta)
  let sigma : ℕ → ℝ := fun i => tau i * theta
  have hsigma (i : ℕ) : 0 < sigma i := mul_pos (htau i) htheta
  let gs := fun i => scaleMetric (sigma i)⁻¹ (inv_pos.mpr (hsigma i))
    (F.S.base.metric (-sigma i))
  have hmetric0 (i : ℕ) : (X.obj i).metric =
      scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-sigma i)) := by
    change ((backwardFlowSequence F tau htau q).term i).S.base.metric (1 - theta) = _
    rw [backwardFlowSequence_metric]
    congr 2
    dsimp only [sigma]
    ring
  have hmetric (i : ℕ) : (X.obj i).metric = scaleMetric theta htheta (gs i) := by
    rw [hmetric0]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [gs, sigma, scaleMetric_inner]
    field_simp
  let fs : ∀ i, (X.obj i).M → ℝ≥0∞ := fun i x => ENNReal.ofReal
    (perelmanDensity (Module.finrank ℝ E) theta (fun y => redLength F.S 0 p y (sigma i)) x)
  let μ : ℕ → Measure F.M := fun i =>
    riemannianVolumeMeasure (I := I) (M := F.M) (X.obj i).metric
  have hnonneg (i : ℕ) (x : F.M) : 0 ≤ redLength F.S 0 p x (sigma i) := by
    obtain ⟨B, hB⟩ := hF.globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg F.S 0 (hsigma i).le
    intro t ht y
    simpa only [zero_sub] using (hB (-t) (neg_nonpos.mpr ht.1) y).1
  have hmeas (i : ℕ) : Measurable (fs i) :=
    ENNReal.measurable_ofReal.comp
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_redLength_of_ancient F hF p (hsigma i)).neg)).measurable
  have hbound (i : ℕ) (x : F.M) : fs i x ≤
      ENNReal.ofReal (perelmanDensityPrefactor (Module.finrank ℝ E) theta) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnonneg i x))
  have htotal : Tendsto (fun i => ∫⁻ x, fs (phi i) x ∂μ (phi i)) atTop
      (𝓝 (asymptoticReducedVolume F.S 0 p)) := by
    have ht := ancient_reducedVolume_tendsto_rescaled F hF p hescape htheta
    apply ht.congr'
    apply Eventually.of_forall
    intro i
    dsimp only [Function.comp_apply]
    rw [intrinsicReducedVolume_eq_lintegral_perelmanDensity_scaled F.S 0 p (htau (phi i)) htheta]
    simp only [zero_sub]
    change _ = ∫⁻ x, fs (phi i) x ∂riemannianVolumeMeasure (I := I) (M := F.M) (X.obj (phi i)).metric
    rw [hmetric0]
  apply Phi.lintegral_eq_of_tendsto_of_tightness C hcanonical hcomplete fs hmeas
    (fun K _ => ⟨_, ENNReal.ofReal_ne_top,
      Eventually.of_forall (fun i x _ => hbound (phi i) (Phi.map i x))⟩)
    (fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp (hlim x).neg))) htotal
  intro ε hε
  obtain ⟨N, hN⟩ := ancient_exp_neg_redLength_uniform_tightness F hF
    (ell P.basepoint + 1) hε
  refine ⟨Real.sqrt theta * N, ?_⟩
  have hbase : ∀ᶠ i in atTop,
      redLength F.S 0 p (q (phi i)) (sigma (phi i)) ≤ ell P.basepoint + 1 := by
    filter_upwards [(hlim P.basepoint).eventually
      (gt_mem_nhds (lt_add_one (ell P.basepoint)))] with i hi
    have hbp : Phi.map i P.basepoint = q (phi i) := Phi.basepoint_map i
    rw [hbp] at hi
    exact hi.le
  filter_upwards [hbase] with i hi
  let T := {x : F.M | (N : ℝ) ≤ (riemannianEDistOf (gs (phi i)) (q (phi i)) x).toReal}
  have hsubset : (riemannianBallOf (gs (phi i)) (q (phi i)) (N : ℝ))ᶜ ⊆ T := by
    intro x hx
    have hn : ENNReal.ofReal (N : ℝ) ≤
        riemannianEDistOf (gs (phi i)) (q (phi i)) x := le_of_not_gt hx
    have hd := ENNReal.toReal_mono
      (riemannianEDistOf_ne_top (gs (phi i)) (q (phi i)) x) hn
    change (N : ℝ) ≤ (riemannianEDistOf (gs (phi i)) (q (phi i)) x).toReal
    simpa only [ENNReal.toReal_ofReal (Nat.cast_nonneg N)] using hd
  have hpref : perelmanDensityPrefactor (Module.finrank ℝ E) 1 ≤ 1 := by
    change (4 * Real.pi * 1) ^ (-(Module.finrank ℝ E : ℝ) / 2) ≤ 1
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num)
  change (∫⁻ x in (riemannianBallOf (I := I) (M := F.M) (X.obj (phi i)).metric (q (phi i))
      (Real.sqrt theta * N))ᶜ, fs (phi i) x ∂μ (phi i)) ≤ ε
  dsimp only [μ, fs]
  rw [hmetric, riemannianBallOf_scaleMetric]
  have hscale := setLIntegral_perelmanDensity_scaleMetric (gs (phi i)) htheta zero_lt_one
    (fun y => redLength F.S 0 p y (sigma (phi i)))
    (riemannianBallOf (gs (phi i)) (q (phi i)) (N : ℝ))ᶜ
  rw [mul_one] at hscale
  rw [hscale]
  calc
    _ ≤ ∫⁻ x in T, ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) 1
        (fun y => redLength F.S 0 p y (sigma (phi i))) x)
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (gs (phi i)) := lintegral_mono_set hsubset
    _ ≤ ∫⁻ x in T, ENNReal.ofReal (Real.exp (-redLength F.S 0 p x (sigma (phi i))))
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (gs (phi i)) := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_of_le_one_left (Real.exp_pos _).le hpref
    _ ≤ ε := hN p (q (phi i)) (sigma (phi i)) (hsigma (phi i)) hi

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set MeasureTheory
open DifferentialGeometry.PDE.RicciFlow.Entropy
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff NNReal _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

theorem exists_backward_flow_reducedLength_limit_with_mass
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (hescape : Tendsto tau atTop atTop) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A)
    {T : ℝ} (hT : 1 ≤ T) :
    let X := backwardFlowSequence F tau htau q
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) (phi : ℕ → ℕ),
      StrictMono phi ∧ ∃ Phi : PointedCGHMaps (I := I) X (L.atTime 0) phi,
        ConnectedSpace L.M ∧ (∀ t : ℝ, t ≤ 0 → MetricComplete (L.atTime t)) ∧
        (∀ t : ℝ, t ≤ 0 → ∃ C : MetricConvergenceData (I := I) (Phi.atTime (I := I) (X := X) (L := L) t),
          (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I)
            (Phi.atTime (I := I) (X := X) (L := L) t) k) ∧
          (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)) ∧
        ∃ (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M),
          (∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
            ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
              ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
                (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner
                  (Phi.map i x) (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w)) ∧
          (∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
            ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ i ≥ N,
              ∀ t ∈ Icc a b,
                metricDerivNormSupOn K r (G i t) (L.S.base.metric t) R < epsilon) ∧
        ∃ ell : C(L.M × Icc (1 : ℝ) T, ℝ),
          (∀ z, 0 ≤ ell z) ∧ ell (L.basepoint, ⟨1, le_rfl, hT⟩) ≤ A ∧
          (∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
            ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R,
            ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R,
            ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
              (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|)) ∧
          (∀ S : Set (L.M × Icc (1 : ℝ) T), IsCompact S → TendstoUniformlyOn
            (fun i z => redLength F.S 0 p (Phi.map i z.1) (tau (phi i) * z.2)) ell atTop S) ∧
          ∀ theta : Icc (1 : ℝ) T,
            (∫⁻ x, ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) theta
              (fun y => ell (y, theta)) x)
              ∂riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric (1 - theta))) =
                asymptoticReducedVolume F.S 0 p := by
  let _ : NeZero (Module.finrank ℝ E) := neZero_finrank_of_isAncientKappaSolution F hF
  obtain ⟨L, phi, hphi, Phi, hconnected, hcomplete, hconv,
      R, G, hG, hmetric, ell, hnonneg, hbaseLimit, hLip, hpotential⟩ :=
    exists_backward_flow_reducedLength_limit_with_uniform_metric_convergence F hF p tau htau q hbase hT
  refine ⟨L, phi, hphi, Phi, hconnected, hcomplete, hconv,
    R, G, hG, hmetric, ell, hnonneg, hbaseLimit, hLip, hpotential, ?_⟩
  intro theta
  have htheta : 0 < (theta : ℝ) := zero_lt_one.trans_le theta.property.1
  have ht : 1 - (theta : ℝ) ≤ 0 := sub_nonpos.mpr theta.property.1
  obtain ⟨C, hcanonical, _⟩ := hconv (1 - theta) ht
  apply lintegral_perelmanDensity_eq_asymptoticReducedVolume_of_backward_flow_limit F hF
    p tau htau q htheta (L.atTime (1 - theta)) (hescape.comp hphi.tendsto_atTop)
    (Phi.atTime (I := I) (X := backwardFlowSequence F tau htau q) (L := L) (1 - theta))
    C hcanonical (hcomplete (1 - theta) ht) (fun y => ell (y, theta))
  intro x
  change Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (phi i) * (theta : ℝ)))
    atTop (𝓝 (ell (x, theta)))
  have hh := (hpotential {(x, theta)} isCompact_singleton).tendsto_at (mem_singleton (x, theta))
  exact hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped _root_.Manifold ContDiff ENNReal _root_.Topology
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

theorem integrable_backward_flow_limit_perelmanDensity
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {subseq : ℕ → ℕ} (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ}
    (hconv : ∀ theta : Icc (1 : ℝ) T,
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) (1 - theta)),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) (1 - theta)) i)
    (hcomplete : ∀ theta : Icc (1 : ℝ) T, MetricComplete (L.atTime (1 - theta)))
    (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hlim : ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))))
    (μ : MeasureTheory.Measure (Icc (1 : ℝ) T)) [IsFiniteMeasure μ]
    (R : SmoothRiemannianMetric I L.M) :
    Integrable (fun z : Icc (1 : ℝ) T × L.M =>
      riemannianVolumeDensity R (L.S.base.metric (1 - z.1)) z.2 *
        perelmanDensity (Module.finrank ℝ E) z.1 (fun y => ell (y, z.1)) z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) := by
  have hρ := riemannianVolumeDensity_family_continuousOn R L.S.base.metric
    L.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier
  have hρc : Continuous (fun z : Icc (1 : ℝ) T × L.M =>
      riemannianVolumeDensity R (L.S.base.metric (1 - z.1)) z.2) :=
    hρ.comp_continuous
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
      (fun z => ⟨show 1 - (z.1 : ℝ) ≤ 0 from sub_nonpos.mpr z.1.property.1, mem_univ _⟩)
  have hu : Continuous (fun z : Icc (1 : ℝ) T × L.M =>
      perelmanDensity (Module.finrank ℝ E) z.1 (fun y => ell (y, z.1)) z.2) := by
    unfold perelmanDensity perelmanDensityPrefactor
    apply Continuous.mul
    · apply Continuous.rpow_const
        (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
      intro z
      exact Or.inl (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (ne_of_gt (zero_lt_one.trans_le z.1.property.1)))
    · exact Real.continuous_exp.comp (ell.continuous.comp continuous_swap).neg
  have hw := (hρc.mul hu).aestronglyMeasurable
    (μ := μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R))
  apply integrable_prod_volumeDensity_smul_of_lintegral_norm_le μ R
    (fun theta => L.S.base.metric (1 - theta))
    (fun z => perelmanDensity (Module.finrank ℝ E) z.1 (fun y => ell (y, z.1)) z.2) hw
    (C := 1) ENNReal.one_ne_top
  filter_upwards [] with theta
  have htheta : 0 < (theta : ℝ) := zero_lt_one.trans_le theta.property.1
  have hnonneg (x : L.M) : 0 ≤ perelmanDensity (Module.finrank ℝ E) theta
      (fun y => ell (y, theta)) x := by
    exact (mul_pos (prefactor_pos _ htheta) (Real.exp_pos _)).le
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
  obtain ⟨C, hcanonical⟩ := hconv theta
  have hmass := lintegral_perelmanDensity_eq_asymptoticReducedVolume_of_backward_flow_limit F hF
    p tau htau q htheta (L.atTime (1 - theta)) hescape
    (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) (1 - theta))
    C hcanonical (hcomplete theta) (fun y => ell (y, theta)) (hlim theta)
  exact hmass.le.trans (ancient_asymptoticReducedVolume_le_one F hF p)
theorem tendsto_integral_backward_flow_limit_perelmanDensity_cutoff
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ} (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ}
    (hconv : ∀ theta : Icc (1 : ℝ) T,
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) (1 - theta)),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) (1 - theta)) i)
    (hcomplete : ∀ theta : Icc (1 : ℝ) T, MetricComplete (L.atTime (1 - theta)))
    (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hlim : ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))))
    (μ : MeasureTheory.Measure (Icc (1 : ℝ) T)) [IsFiniteMeasure μ]
    (R : SmoothRiemannianMetric I L.M)
    (ψ : C(Icc (1 : ℝ) T, ℝ))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → NNReal) (ha : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ z : Icc (1 : ℝ) T × L.M,
      Analysis.CutoffProfile.evalue
        ((a i : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint z.2) *
      (ψ z.1 * (riemannianVolumeDensity R (L.S.base.metric (1 - z.1)) z.2 *
        perelmanDensity (Module.finrank ℝ E) z.1 (fun y => ell (y, z.1)) z.2))
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) l
      (𝓝 ((∫ theta, ψ theta ∂μ) * (asymptoticReducedVolume F.S 0 p).toReal)) := by
  let _ := riemannianVolumeMeasure_sigmaFinite R
  let g : Icc (1 : ℝ) T → SmoothRiemannianMetric I L.M := fun theta => L.S.base.metric (1 - theta)
  let ρ : Icc (1 : ℝ) T × L.M → ℝ := fun z => riemannianVolumeDensity R (g z.1) z.2
  let u : Icc (1 : ℝ) T → L.M → ℝ := fun theta =>
    perelmanDensity (Module.finrank ℝ E) theta (fun y => ell (y, theta))
  have hm : Integrable (fun z => ρ z * u z.1 z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) :=
    integrable_backward_flow_limit_perelmanDensity F hF p tau htau q L hescape Phi
      hconv hcomplete ell hlim μ R
  have hw : Integrable (fun z => ψ z.1 * (ρ z * u z.1 z.2))
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) :=
    hm.bdd_mul (c := ‖ψ‖) (ψ.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun z => ψ.norm_coe_le_norm z.1)
  have hmass (theta : Icc (1 : ℝ) T) :
      (∫ x, ρ (theta, x) * u theta x
        ∂riemannianVolumeMeasure (I := I) (M := L.M) R) =
        (asymptoticReducedVolume F.S 0 p).toReal := by
    have he := integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul R (g theta) (u theta)
    change (∫ x, u theta x ∂riemannianVolumeMeasure (I := I) (M := L.M) (g theta)) =
      (∫ x, ρ (theta, x) * u theta x ∂riemannianVolumeMeasure (I := I) (M := L.M) R) at he
    rw [← he]
    have hu : Continuous (u theta) := by
      unfold u perelmanDensity
      exact continuous_const.mul (Real.continuous_exp.comp
        (ell.continuous.comp (continuous_id.prodMk continuous_const)).neg)
    have hu0 (x : L.M) : 0 ≤ u theta x :=
      (mul_pos (prefactor_pos _ (zero_lt_one.trans_le theta.property.1)) (Real.exp_pos _)).le
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hu0) hu.aestronglyMeasurable]
    obtain ⟨C, hC⟩ := hconv theta
    exact congrArg ENNReal.toReal
      (lintegral_perelmanDensity_eq_asymptoticReducedVolume_of_backward_flow_limit F hF
        p tau htau q (zero_lt_one.trans_le theta.property.1) (L.atTime (1 - theta)) hescape
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) (1 - theta))
        C hC (hcomplete theta) (fun y => ell (y, theta)) (hlim theta))
  have htotal : (∫ z, ψ z.1 * (ρ z * u z.1 z.2)
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) =
      (∫ theta, ψ theta ∂μ) * (asymptoticReducedVolume F.S 0 p).toReal := by
    rw [integral_prod _ hw]
    simp_rw [integral_const_mul, hmass]
    exact integral_mul_const _ _
  have h := Analysis.CutoffProfile.tendsto_integral_evalue_smul
    ((DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist (L.S.base.metric 0) L.basepoint).comp continuous_snd).aemeasurable
    (Eventually.of_forall fun z => riemannianEDistOf_ne_top (L.S.base.metric 0) L.basepoint z.2)
    hw a ha
  rw [htotal] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
