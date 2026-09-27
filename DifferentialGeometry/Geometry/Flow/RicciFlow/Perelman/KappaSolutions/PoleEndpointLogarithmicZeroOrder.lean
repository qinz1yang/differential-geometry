import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityScalarIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthIntegralConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

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

namespace HalfLineMetricConvergenceData

theorem integrable_and_tendsto_integral_poleEndpoint_chartDensity_mul_sub_redLength
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 ≤ a)
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
    (c₀ : ℝ) (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (volume : Measure ℝ)
    let Fk := fun k (z : E × ℝ) =>
      chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1) * w z *
        (c₀ - redLength ((U).term (phi (co.φ (rho k)))).S 0 p
          (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2)
    let F₀ := fun z : E × ℝ =>
      chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1) * w z *
        (c₀ - ell ((extChartAt I x).symm z.1, z.2))
    (∀ᶠ k in atTop, IntegrableOn (Fk k) (K ×ˢ Icc a c) ν) ∧
      IntegrableOn F₀ (K ×ˢ Icc a c) ν ∧
      Tendsto (fun k => ∫ z in K ×ˢ Icc a c, Fk k z ∂ν) atTop
        (𝓝 (∫ z in K ×ˢ Icc a c, F₀ z ∂ν)) := by
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (volume : Measure ℝ)
  let C : Set (E × ℝ) := K ×ˢ Icc a c
  let f : ℕ → E × ℝ → ℝ := fun k z =>
    redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
  let f₀ : E × ℝ → ℝ := fun z => ell ((extChartAt I x).symm z.1, z.2)
  let r : ℕ → E × ℝ → ℝ := fun k z =>
    chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
      ((extChartAt I x).symm z.1)
  let r₀ : E × ℝ → ℝ := fun z =>
    chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
  let G := fun k z => r k z * w z * (c₀ - f k z)
  let G₀ := fun z => r₀ z * w z * (c₀ - f₀ z)
  change (∀ᶠ k in atTop, IntegrableOn (G k) C ν) ∧
    IntegrableOn G₀ C ν ∧
      Tendsto (fun k => ∫ z in C, G k z ∂ν) atTop (𝓝 (∫ z in C, G₀ z ∂ν))
  have hC : IsCompact C := hK.prod isCompact_Icc
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hcoord : ContinuousOn
      (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2)) C :=
    (((continuousOn_extChartAt_symm x).mono hKt).comp continuous_fst.continuousOn
      (fun _ hz => hz.1)).prodMk continuous_snd.continuousOn
  have hcoordJ : MapsTo (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2))
      C (J ×ˢ Icc a c) := fun _ hz => ⟨hKJ hz.1, hz.2⟩
  have hf : ∀ᶠ k in atTop, ContinuousOn (f k) C := by
    filter_upwards [hrho.eventually
      (eventually_continuousOn_poleEndpoint_redLength_on_compact_time_interval
        F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
        (c := c) ha0 hbase)] with k hk
    simpa only [f, Function.comp_def] using hk.comp hcoord hcoordJ
  have hr (k : ℕ) : ContinuousOn (r k) C :=
    continuousOn_poleEndpoint_chartDensity F hcar hreg b hbmem tau q hsigma
      Phi R bf hsrc htgt (co.φ (rho k)) ha x hKt
  have hr₀ : ContinuousOn r₀ C :=
    continuousOn_poleEndpoint_chartDensity_limit F hcar hreg b hbmem tau q hsigma
      Phi R co ha x hK hKt
  have hru : TendstoUniformlyOn r r₀ atTop C :=
    tendstoUniformlyOn_poleEndpoint_chartDensity F hcar hreg b hbmem tau q hsigma
      Phi R co ha rho hrho x hK hKt
  have hsource : ∀ᶠ k in atTop, IntegrableOn (G k) C ν := by
    filter_upwards [hf] with k hk
    exact ((hr k).mul hw |>.mul (continuousOn_const.sub hk)).integrableOn_compact hC
  obtain ⟨V, _hV, hupper⟩ :=
    exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha0 hbase
  let M := max V 0
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
      (lCost_nonneg_of_scalar_nonneg _ 0 (ha0.trans_le hz.2.1).le hscalar _ _)
      (by positivity)
  let bound : E × ℝ → ℝ := fun z =>
    (‖r₀ z‖ + 1) * ‖w z‖ * (‖c₀‖ + M)
  have hbound : ∀ᶠ k in atTop, ∀ᵐ z ∂ν.restrict C, ‖G k z‖ ≤ bound z := by
    filter_upwards [hrho.eventually hupper,
      Metric.tendstoUniformlyOn_iff.mp hru 1 zero_lt_one] with k hk hkr
    filter_upwards [ae_restrict_mem hC.measurableSet] with z hz
    have hrf : ‖r k z - r₀ z‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hkr z hz
    have hrbound : ‖r k z‖ ≤ ‖r₀ z‖ + 1 := by
      have ht := norm_add_le (r k z - r₀ z) (r₀ z)
      rw [sub_add_cancel] at ht
      linarith
    have hfbound : ‖f k z‖ ≤ M := by
      rw [Real.norm_of_nonneg (hnonneg k z hz)]
      exact (hk _ (hKJ hz.1) _ hz.2).trans (le_max_left _ _)
    have hsub : ‖c₀ - f k z‖ ≤ ‖c₀‖ + M :=
      (norm_sub_le _ _).trans (add_le_add le_rfl hfbound)
    dsimp only [G, bound]
    rw [norm_mul, norm_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hrbound (norm_nonneg _)) hsub
      (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))
  have hboundInt : Integrable bound (ν.restrict C) :=
    (((hr₀.norm.add continuousOn_const).mul hw.norm).mul
      continuousOn_const).integrableOn_compact hC
  have hlimit : ∀ᵐ z ∂ν.restrict C,
      Tendsto (fun k => G k z) atTop (𝓝 (G₀ z)) := by
    filter_upwards [ae_restrict_mem hC.measurableSet] with z hz
    exact ((hru.tendsto_at hz).mul tendsto_const_nhds).mul
      (tendsto_const_nhds.sub (hconv _ (hKJ hz.1) _ hz.2))
  have hmeas : ∀ᶠ k in atTop, AEStronglyMeasurable (G k) (ν.restrict C) :=
    hsource.mono fun _ hk => hk.aestronglyMeasurable
  exact ⟨hsource, integrable_of_dominated_convergence bound hmeas hbound hboundInt hlimit,
    tendsto_integral_filter_of_dominated_convergence bound hmeas hbound hboundInt hlimit⟩

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
