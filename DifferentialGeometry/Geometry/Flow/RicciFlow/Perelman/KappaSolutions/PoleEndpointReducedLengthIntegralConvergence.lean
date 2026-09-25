import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthContinuity
import DifferentialGeometry.Analysis.Integration.Integral.DominatedConvergence
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set MeasureTheory
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

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

namespace HalfLineMetricConvergenceData

private theorem integrable_limit_and_integral_convergence
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 0 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (hKJ : MapsTo (extChartAt I x).symm K J)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (volume : Measure ℝ)
    IntegrableOn (fun z => w z * ell ((extChartAt I x).symm z.1, z.2))
      (K ×ˢ Icc a c) ν ∧
    Tendsto (fun k => ∫ z in K ×ˢ Icc a c, w z *
      redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2 ∂ν) atTop
      (𝓝 (∫ z in K ×ˢ Icc a c, w z * ell ((extChartAt I x).symm z.1, z.2) ∂ν)) := by
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (volume : Measure ℝ)
  let C : Set (E × ℝ) := K ×ˢ Icc a c
  let f : ℕ → E × ℝ → ℝ := fun k z =>
    redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
  let f₀ : E × ℝ → ℝ := fun z => ell ((extChartAt I x).symm z.1, z.2)
  have hC : IsCompact C := hK.prod isCompact_Icc
  have hcoord : ContinuousOn
      (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2)) C :=
    (((continuousOn_extChartAt_symm x).mono hKt).comp continuous_fst.continuousOn
      (fun _ hz => hz.1)).prodMk continuous_snd.continuousOn
  have hcoordJ : MapsTo (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2))
      C (J ×ˢ Icc a c) := fun _ hz => ⟨hKJ hz.1, hz.2⟩
  have hcontinuous := eventually_continuousOn_poleEndpoint_redLength_on_compact_time_interval
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
  have hmeas : ∀ᶠ k in atTop,
      AEStronglyMeasurable (fun z => w z * f k z) (ν.restrict C) := by
    filter_upwards [hrho.eventually hcontinuous] with k hk
    have hf : ContinuousOn (f k) C := by
      simpa only [f, Function.comp_def] using hk.comp hcoord hcoordJ
    exact (hw.mul hf).aestronglyMeasurable hC.measurableSet
  obtain ⟨V, _hV, hupper⟩ :=
    exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
  have hnonneg (k : ℕ) (z : E × ℝ) (hz : z ∈ C) : 0 ≤ f k z := by
    obtain ⟨B, hB⟩ := (hancient (phi (co.φ (rho k)))).globalScalarBound
    have hscalar : ∀ s ∈ Icc 0 z.2, ∀ y,
        0 ≤ ((U).term (phi (co.φ (rho k)))).S.scalar (0 - s) y := by
      intro s hs y
      have hmem : -s ∈ ancientTimeInterval.carrier := by
        rw [ancientTimeInterval_carrier]
        exact Set.mem_Iic.mpr (by linarith [hs.1])
      simpa only [zero_sub] using (hB (-s) hmem y).1
    change 0 ≤ lCost ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2 /
        (2 * Real.sqrt z.2)
    exact div_nonneg
      (lCost_nonneg_of_scalar_nonneg _ 0 (ha.trans_le hz.2.1).le hscalar _ _)
      (by positivity)
  have hbound : ∀ᶠ k in atTop, ∀ᵐ z ∂ν.restrict C,
      ‖w z * f k z‖ ≤ ‖w z‖ * V := by
    filter_upwards [hrho.eventually hupper] with k hk
    filter_upwards [ae_restrict_mem hC.measurableSet] with z hz
    rw [norm_mul, Real.norm_of_nonneg (hnonneg k z hz)]
    exact mul_le_mul_of_nonneg_left
      (hk _ (hKJ hz.1) _ hz.2) (norm_nonneg _)
  have hintegrable : Integrable (fun z => ‖w z‖ * V) (ν.restrict C) :=
    (hw.norm.mul continuousOn_const).integrableOn_compact hC
  have hlimit : ∀ᵐ z ∂ν.restrict C,
      Tendsto (fun k => w z * f k z) atTop (𝓝 (w z * f₀ z)) := by
    filter_upwards [ae_restrict_mem hC.measurableSet] with z hz
    exact tendsto_const_nhds.mul (hconv _ (hKJ hz.1) _ hz.2)
  exact ⟨integrable_of_dominated_convergence
    (fun z => ‖w z‖ * V) hmeas hbound hintegrable hlimit,
    tendsto_integral_filter_of_dominated_convergence
      (fun z => ‖w z‖ * V) hmeas hbound hintegrable hlimit⟩

theorem tendsto_integral_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 0 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (hKJ : MapsTo (extChartAt I x).symm K J)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (volume : Measure ℝ)
    Tendsto (fun k => ∫ z in K ×ˢ Icc a c, w z *
      redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2 ∂ν) atTop
      (𝓝 (∫ z in K ×ˢ Icc a c, w z * ell ((extChartAt I x).symm z.1, z.2) ∂ν)) := by
  exact (integrable_limit_and_integral_convergence
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hK hKt hKJ w hw).2

theorem integrableOn_poleEndpoint_redLength_limit_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 0 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (hKJ : MapsTo (extChartAt I x).symm K J)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (volume : Measure ℝ)
    IntegrableOn (fun z => w z * ell ((extChartAt I x).symm z.1, z.2))
      (K ×ˢ Icc a c) ν := by
  exact (integrable_limit_and_integral_convergence
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hK hKt hKJ w hw).1

theorem eventually_integrableOn_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 0 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (hKJ : MapsTo (extChartAt I x).symm K J)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (volume : Measure ℝ)
    ∀ᶠ k in atTop, IntegrableOn (fun z : E × ℝ => w z *
      redLength ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) z.2) (K ×ˢ Icc a c) ν := by
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (volume : Measure ℝ)
  have hcoord : ContinuousOn
      (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2)) (K ×ˢ Icc a c) :=
    (((continuousOn_extChartAt_symm x).mono hKt).comp continuous_fst.continuousOn
      (fun _ hz => hz.1)).prodMk continuous_snd.continuousOn
  have hcoordJ : MapsTo (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2))
      (K ×ˢ Icc a c) (J ×ˢ Icc a c) := fun _ hz => ⟨hKJ hz.1, hz.2⟩
  filter_upwards [eventually_continuousOn_poleEndpoint_redLength_on_compact_time_interval
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase]
    with k hk
  exact (hw.mul (hk.comp hcoord hcoordJ)).integrableOn_compact (hK.prod isCompact_Icc)

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
