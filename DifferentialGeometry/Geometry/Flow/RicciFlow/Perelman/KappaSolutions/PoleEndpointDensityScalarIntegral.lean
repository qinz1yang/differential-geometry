import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointScalarContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.VolumeConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [I.Boundaryless] in
private theorem continuousOn_chartDensity_of_gram
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D' : RealTimeInterval} (G : MetricConnectionFamilyOn (I := I) (M := M) D')
    (x : M) {S : Set (ℝ × E)} (hG : ContinuousOn (chartGramOp G x) S) :
    ContinuousOn (fun z : ℝ × E =>
      chartDensity (G.metric z.1) x ((extChartAt I x).symm z.2)) S := by
  classical
  let e := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  let density : (E →L[ℝ] E) → ℝ := fun A =>
    Real.sqrt (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
      inner ℝ (A (e i)) (e j)).det
  have hmatrix : Continuous (fun A : E →L[ℝ] E =>
      Matrix.of fun i j : Fin (Module.finrank ℝ E) => inner ℝ (A (e i)) (e j)) :=
    continuous_matrix fun i j =>
      (continuous_id.clm_apply continuous_const).inner continuous_const
  have hd : Continuous density := Real.continuous_sqrt.comp hmatrix.matrix_det
  have hc := hd.comp_continuousOn hG
  simpa only [density, Function.comp_def, e, chartDensity_eq_sqrt_det_chartGramOp] using hc

theorem continuousOn_poleEndpoint_chartDensity
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (k : ℕ) {a c : ℝ} (ha : 1 ≤ a) (x : P.M) {K : Set E}
    (hKt : K ⊆ (extChartAt I x).target) :
    ContinuousOn (fun z : E × ℝ =>
      chartDensity (gSeqExt Phi R bf hsrc htgt k (1 - z.2)) x
        ((extChartAt I x).symm z.1)) (K ×ˢ Icc a c) := by
  let G : MetricConnectionFamilyOn (I := I) (M := P.M) (Y).D :=
    (lcMetricFamily (I := I) (M := P.M)
      (fun t => gSeqExt Phi R bf hsrc htgt k t)).restrict (Y).D
  have hgram : ContinuousOn (chartGramOp G x) ((Y).D.carrier ×ˢ K) :=
    continuousOn_chartGramOp_gSeqExt Phi R bf hsrc htgt k x hKt
  have hd := continuousOn_chartDensity_of_gram G x hgram
  have hpair : ContinuousOn (fun z : E × ℝ => (1 - z.2, z.1)) (K ×ˢ Icc a c) :=
    (continuousOn_const.sub continuousOn_snd).prodMk continuousOn_fst
  have hmaps : MapsTo (fun z : E × ℝ => (1 - z.2, z.1))
      (K ×ˢ Icc a c) ((Y).D.carrier ×ˢ K) := by
    intro z hz
    refine ⟨?_, hz.1⟩
    change 1 - z.2 ∈ ancientTimeInterval.carrier
    rw [ancientTimeInterval_carrier]
    change 1 - z.2 ≤ 0
    linarith [hz.2.1]
  simpa only [G, MetricConnectionFamily.restrict_metric, lcMetricFamily,
    Function.comp_def] using hd.comp hpair hmaps

namespace HalfLineMetricConvergenceData

theorem tendstoUniformlyOn_poleEndpoint_chartDensity
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c : ℝ} (ha : 1 ≤ a) (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target) :
    TendstoUniformlyOn
      (fun k (z : E × ℝ) =>
        chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
          ((extChartAt I x).symm z.1))
      (fun z => chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1))
      atTop (K ×ˢ Icc a c) := by
  let C : Set (E × ℝ) := K ×ˢ Icc a c
  obtain ⟨n, hn⟩ := exists_nat_ge (c - 1)
  let cw := HalfLineMetricConvergenceData.atWindow Phi co n
  have hcarrier : Icc (-(n : ℝ)) 0 ⊆ (Y).D.carrier := by
    intro s hs
    change s ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, mem_Iic] using hs.2
  have htau (z : C) : 1 - z.val.2 ∈ Icc (-(n : ℝ)) 0 := by
    exact ⟨by linarith [z.property.2.2], by linarith [z.property.2.1]⟩
  have hstationary : TendstoUniformly (fun _ : ℕ => fun z : C => z.val.1)
      (fun z : C => z.val.1) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro epsilon hepsilon
    exact Eventually.of_forall fun _ z => by simpa only [dist_self] using hepsilon
  have hd := cw.tendstoUniformly_chartDensity_of_subset_carrier
    Phi R bf hsrc htgt (-(n : ℝ)) 0 x hKt hK hcarrier
    htau (Eventually.of_forall fun _ z => z.property.1)
    (fun z => z.property.1) hstationary
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  filter_upwards [hrho.eventually ((Metric.tendstoUniformly_iff.mp hd) epsilon hepsilon)]
    with k hk
  intro z hz
  simpa only [cw, HalfLineMetricConvergenceData.atWindow, Function.comp_apply] using hk ⟨z, hz⟩

theorem continuousOn_poleEndpoint_chartDensity_limit
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c : ℝ} (ha : 1 ≤ a) (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target) :
    ContinuousOn (fun z : E × ℝ =>
      chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)) (K ×ˢ Icc a c) := by
  have hu := tendstoUniformlyOn_poleEndpoint_chartDensity
    F hcar hreg b hbmem tau q hsigma Phi R co (c := c) ha id tendsto_id x hK hKt
  apply hu.continuousOn
  exact (Eventually.of_forall fun k => continuousOn_poleEndpoint_chartDensity
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt (co.φ k) ha x hKt).frequently

theorem integrableOn_and_tendsto_integral_poleEndpoint_chartDensity_mul_scalar
    [NeZero (Module.finrank ℝ E)]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c : ℝ} (ha : 1 ≤ a) (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
    let ν := (modelHaar (E := E)).prod (volume : Measure ℝ)
    let f := fun k (z : E × ℝ) =>
      w z * chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1) *
      ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
    let f₀ := fun z : E × ℝ =>
      w z * chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1) *
        metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
    IntegrableOn f₀ (K ×ˢ Icc a c) ν ∧
      (∀ᶠ k in atTop, IntegrableOn (f k) (K ×ˢ Icc a c) ν) ∧
      Tendsto (fun k => ∫ z in K ×ˢ Icc a c, f k z ∂ν) atTop
        (𝓝 (∫ z in K ×ˢ Icc a c, f₀ z ∂ν)) := by
  let ν := (modelHaar (E := E)).prod (volume : Measure ℝ)
  let C : Set (E × ℝ) := K ×ˢ Icc a c
  let density : ℕ → E × ℝ → ℝ := fun k z =>
    chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
      ((extChartAt I x).symm z.1)
  let density₀ : E × ℝ → ℝ := fun z =>
    chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
  let scalar : ℕ → E × ℝ → ℝ := fun k z =>
    ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
  let scalar₀ : E × ℝ → ℝ := fun z =>
    metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
  have hC : IsCompact C := hK.prod isCompact_Icc
  have hDensity : TendstoUniformlyOn density density₀ atTop C :=
    tendstoUniformlyOn_poleEndpoint_chartDensity
      F hcar hreg b hbmem tau q hsigma Phi R co ha rho hrho x hK hKt
  have hDensityCont (k : ℕ) : ContinuousOn (density k) C :=
    continuousOn_poleEndpoint_chartDensity
      F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt (co.φ (rho k)) ha x hKt
  have hDensity₀ : ContinuousOn density₀ C :=
    continuousOn_poleEndpoint_chartDensity_limit
      F hcar hreg b hbmem tau q hsigma Phi R co ha x hK hKt
  have hScalar : TendstoUniformlyOn scalar scalar₀ atTop C := by
    let J : Set P.M := (extChartAt I x).symm '' K
    have hJ : IsCompact J :=
      hK.image_of_continuousOn ((continuousOn_extChartAt_symm x).mono hKt)
    have hu := tendstoUniformlyOn_poleEndpoint_scalar
      F hcar hreg b hbmem tau q hsigma Phi R co (c := c) ha hJ
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro epsilon hepsilon
    filter_upwards [hrho.eventually (hu epsilon hepsilon)] with k hk
    intro z hz
    exact hk (z.2, (extChartAt I x).symm z.1) ⟨hz.2, mem_image_of_mem _ hz.1⟩
  have hScalarCont : ∀ᶠ k in atTop, ContinuousOn (scalar k) C := by
    simpa only [Function.comp_apply] using
      PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart
        F hcar hreg b hbmem tau q hsigma Phi (co.φ ∘ rho)
        (co.strictMono.tendsto_atTop.comp hrho) x hK hKt (c := c) ha
  have hScalar₀ : ContinuousOn scalar₀ C := hScalar.continuousOn hScalarCont.frequently
  have hSourceInt : ∀ᶠ k in atTop,
      Integrable (fun z => w z * density k z * scalar k z) (ν.restrict C) :=
    hScalarCont.mono fun k hk => ((hw.mul (hDensityCont k)).mul hk).integrableOn_compact hC
  have hTargetInt : Integrable (fun z => w z * density₀ z * scalar₀ z) (ν.restrict C) :=
    ((hw.mul hDensity₀).mul hScalar₀).integrableOn_compact hC
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hDensity₀
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn hScalar₀
  let BD := max B 0 + 1
  let BS := max L 0 + 1
  have hBD : 0 ≤ BD := by
    dsimp [BD]
    positivity
  have hbound : ∀ᶠ k in atTop, ∀ᵐ z ∂ν.restrict C,
      ‖w z * density k z * scalar k z‖ ≤ ‖w z‖ * BD * BS := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hDensity 1 zero_lt_one,
      Metric.tendstoUniformlyOn_iff.mp hScalar 1 zero_lt_one] with k hd hs
    filter_upwards [ae_restrict_mem hC.measurableSet] with z hz
    have hdclose : ‖density k z - density₀ z‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hd z hz
    have hsclose : ‖scalar k z - scalar₀ z‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hs z hz
    have hdtriangle : ‖density k z‖ ≤ ‖density k z - density₀ z‖ + ‖density₀ z‖ := by
      calc
        ‖density k z‖ = ‖(density k z - density₀ z) + density₀ z‖ := by rw [sub_add_cancel]
        _ ≤ ‖density k z - density₀ z‖ + ‖density₀ z‖ := norm_add_le _ _
    have hstriangle : ‖scalar k z‖ ≤ ‖scalar k z - scalar₀ z‖ + ‖scalar₀ z‖ := by
      calc
        ‖scalar k z‖ = ‖(scalar k z - scalar₀ z) + scalar₀ z‖ := by rw [sub_add_cancel]
        _ ≤ ‖scalar k z - scalar₀ z‖ + ‖scalar₀ z‖ := norm_add_le _ _
    have hdB : ‖density k z‖ ≤ BD := by
      dsimp only [BD]
      apply hdtriangle.trans
      exact (add_le_add hdclose.le ((hB z hz).trans (le_max_left B 0))).trans_eq
        (add_comm 1 (max B 0))
    have hsB : ‖scalar k z‖ ≤ BS := by
      dsimp only [BS]
      apply hstriangle.trans
      exact (add_le_add hsclose.le ((hL z hz).trans (le_max_left L 0))).trans_eq
        (add_comm 1 (max L 0))
    rw [norm_mul, norm_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hdB (norm_nonneg _)) hsB (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) hBD)
  have hDomInt : Integrable (fun z => ‖w z‖ * BD * BS) (ν.restrict C) :=
    ((hw.norm.mul continuousOn_const).mul continuousOn_const).integrableOn_compact hC
  have hPointwise : ∀ᵐ z ∂ν.restrict C,
      Tendsto (fun k => w z * density k z * scalar k z) atTop
        (𝓝 (w z * density₀ z * scalar₀ z)) := by
    filter_upwards [ae_restrict_mem hC.measurableSet] with z hz
    exact (tendsto_const_nhds.mul (hDensity.tendsto_at hz)).mul (hScalar.tendsto_at hz)
  exact ⟨hTargetInt, hSourceInt,
    tendsto_integral_filter_of_dominated_convergence (fun z => ‖w z‖ * BD * BS)
      (hSourceInt.mono fun _ hk => hk.aestronglyMeasurable) hbound hDomInt hPointwise⟩

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
