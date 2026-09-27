import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthEquicontinuity
import DifferentialGeometry.Analysis.Calculus.Derivative.CompactSpatialBound
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ v ∈ K, ∀ t ∈ Icc a c,
      ‖(fderiv ℝ (fun z : E × ℝ =>
        redLength ((U).term (phi (co.φ k))).S 0 p
          (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) z.2) (v, t)).comp
            (ContinuousLinearMap.inl ℝ E ℝ)‖ ≤ B := by
  obtain ⟨C, Dt, hC, _hDt, hmodulus⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmodulus
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : RiemannianBundle (TangentSpace I : P.M → Type _) := ⟨R.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : P.M → Type _) :=
    ⟨R.inner, R.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let _ : PseudoEMetricSpace P.M := PseudoEMetricSpace.ofRiemannianMetric I P.M
  have hedist (y w : P.M) : edist y w = riemannianEDistOf R y w :=
    IsRiemannianManifold.out (I := I) y w
  have hchart : LocallyLipschitzOn W (extChartAt I x).symm := by
    intro v hv
    have hdiff : ContMDiffWithinAt 𝓘(ℝ, E) I 1
        (extChartAt I x).symm (range I) v :=
      contMDiffWithinAt_extChartAt_symm_range x (hWt hv)
    obtain ⟨L, V, hV, hLV⟩ := hdiff.exists_lipschitzOnWith I.convex_range
    exact ⟨L, V, nhdsWithin_mono v (hWt.trans (extChartAt_target_subset_range x)) hV, hLV⟩
  obtain ⟨B, hB, hbound⟩ :=
    Analysis.Calculus.exists_norm_fderiv_comp_inl_le_of_edist_bound
      hW hK hKW hchart hWJ
      (fun k : {k : ℕ // N ≤ k} => fun z : P.M × ℝ =>
        redLength ((U).term (phi (co.φ k.1))).S 0 p (Phi.map (co.φ k.1) z.1) z.2)
      hC zero_lt_one (by
        intro k y hy w hw t ht hdist
        simpa only [Real.dist_eq, hedist, sub_self, abs_zero, mul_zero, add_zero] using
          hN k.1 k.2 y hy w hw t ht t ht hdist)
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop N] with k hk
  exact hbound ⟨k, hk⟩

theorem eventually_memLp_fderiv_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (μ : Measure (E × ℝ)) [IsFiniteMeasure (μ.restrict (K ×ˢ Icc a c))]
    (pExp : ℝ≥0∞) :
    ∀ᶠ k in atTop, MemLp (fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ =>
        redLength ((U).term (phi (co.φ k))).S 0 p
          (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) z).comp
            (ContinuousLinearMap.inl ℝ E ℝ)) pExp (μ.restrict (K ×ˢ Icc a c)) := by
  obtain ⟨B, _hB, hbound⟩ :=
    exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
      x hW hK hKW hWt hWJ
  filter_upwards [hbound] with k hk
  have hm : Measurable (fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ =>
        redLength ((U).term (phi (co.φ k))).S 0 p
          (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) z).comp
            (ContinuousLinearMap.inl ℝ E ℝ)) :=
    (((ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ).flip
      (ContinuousLinearMap.inl ℝ E ℝ)).continuous.measurable).comp
        (measurable_fderiv ℝ _)
  apply MemLp.of_bound hm.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem (hK.measurableSet.prod measurableSet_Icc)] with z hz
  exact hk z.1 hz.1 z.2 hz.2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem memLp_fderiv_poleEndpoint_redLength_limit_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (μ : Measure (E × ℝ)) [IsFiniteMeasure (μ.restrict (K ×ˢ Icc a c))]
    (pExp : ℝ≥0∞) :
    MemLp (fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)) pExp (μ.restrict (K ×ˢ Icc a c)) := by
  obtain ⟨C, Dt, hC, _hDt, hmodulus⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  have hlim : ∀ y ∈ J, ∀ w ∈ J, ∀ t ∈ Icc a c,
      riemannianEDistOf R y w < ENNReal.ofReal 1 →
      |ell (y, t) - ell (w, t)| ≤ C * (riemannianEDistOf R y w).toReal := by
    intro y hy w hw t ht hdist
    apply le_of_tendsto ((hconv y hy t ht).sub (hconv w hw t ht)).abs
    filter_upwards [hrho.eventually hmodulus] with k hk
    simpa only [sub_self, abs_zero, mul_zero, add_zero] using
      hk y hy w hw t ht t ht hdist
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : RiemannianBundle (TangentSpace I : P.M → Type _) := ⟨R.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : P.M → Type _) :=
    ⟨R.inner, R.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let _ : PseudoEMetricSpace P.M := PseudoEMetricSpace.ofRiemannianMetric I P.M
  have hedist (y w : P.M) : edist y w = riemannianEDistOf R y w :=
    IsRiemannianManifold.out (I := I) y w
  have hchart : LocallyLipschitzOn W (extChartAt I x).symm := by
    intro v hv
    have hdiff : ContMDiffWithinAt 𝓘(ℝ, E) I 1
        (extChartAt I x).symm (range I) v :=
      contMDiffWithinAt_extChartAt_symm_range x (hWt hv)
    obtain ⟨L, V, hV, hLV⟩ := hdiff.exists_lipschitzOnWith I.convex_range
    exact ⟨L, V, nhdsWithin_mono v (hWt.trans (extChartAt_target_subset_range x)) hV, hLV⟩
  obtain ⟨B, _hB, hbound⟩ :=
    Analysis.Calculus.exists_norm_fderiv_comp_inl_le_of_edist_bound
      hW hK hKW hchart hWJ (fun _ : Unit => ell) hC zero_lt_one (by
        intro _ y hy w hw t ht hdist
        simpa only [Real.dist_eq, hedist] using hlim y hy w hw t ht hdist)
  have hm : Measurable (fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)) :=
    (((ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ).flip
      (ContinuousLinearMap.inl ℝ E ℝ)).continuous.measurable).comp
        (measurable_fderiv ℝ _)
  apply MemLp.of_bound hm.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem (hK.measurableSet.prod measurableSet_Icc)] with z hz
  exact hbound () z.1 hz.1 z.2 hz.2

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
