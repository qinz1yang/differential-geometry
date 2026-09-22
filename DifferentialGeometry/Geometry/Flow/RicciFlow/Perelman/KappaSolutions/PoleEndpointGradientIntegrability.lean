import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSpatialDerivativeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GradientCoefficients
import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineWindow

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
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

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [I.Boundaryless] in
private theorem integrableOn_reflected_chartGradientBilin
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    {Dg : RealTimeInterval} (G : MetricConnectionFamilyOn (I := I) (M := N) Dg)
    (x : N) {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x).target)
    {a c : ℝ}
    (hG : ContinuousOn (chartGramOp G x) (Icc (1 - c) (1 - a) ×ˢ K))
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c))
    (d : E × ℝ → E →L[ℝ] ℝ) (μ : Measure (E × ℝ))
    (hd : MemLp d 2 (μ.restrict (K ×ˢ Icc a c))) :
    IntegrableOn (fun z =>
      (w z • chartGradientBilin (G.metric (1 - z.2)) x
        ((extChartAt I x).symm z.1)) (d z) (d z)) (K ×ˢ Icc a c) μ := by
  let C := K ×ˢ Icc a c
  let T := Icc (1 - c) (1 - a) ×ˢ K
  let r : E × ℝ → ℝ × E := fun z => (1 - z.2, z.1)
  let r' : ℝ × E → E × ℝ := fun z => (z.2, 1 - z.1)
  let w' : ℝ × E → ℝ := fun z => w (r' z)
  let B := fun z : E × ℝ =>
    w z • chartGradientBilin (G.metric (1 - z.2)) x ((extChartAt I x).symm z.1)
  have hr : Continuous r := (continuous_const.sub continuous_snd).prodMk continuous_fst
  have hr' : Continuous r' := continuous_snd.prodMk (continuous_const.sub continuous_fst)
  have hrC : MapsTo r C T := by
    intro z hz
    exact ⟨⟨by dsimp [r]; linarith [hz.2.2],
      by dsimp [r]; linarith [hz.2.1]⟩, hz.1⟩
  have hrT : MapsTo r' T C := by
    intro z hz
    exact ⟨hz.2, ⟨by dsimp [r']; linarith [hz.1.2],
      by dsimp [r']; linarith [hz.1.1]⟩⟩
  have hw' : ContinuousOn w' T := hw.comp hr'.continuousOn hrT
  have hB : ContinuousOn B C := by
    have hb := (Geometry.Curvature.continuousOn_smul_chartGradientBilin
      G x (fun z hz => hKt hz.2) hG w' hw').comp hr.continuousOn hrC
    simpa only [B, w', r, r', Function.comp_def, sub_sub_cancel, Prod.eta] using hb
  have hC : IsCompact C := hK.prod isCompact_Icc
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn hB
  apply MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable B (C := L) ?_ ?_ hd hd
  · intro u v
    have heval : ContinuousOn (fun z => B z u v) C :=
      (hB.clm_apply continuousOn_const).clm_apply continuousOn_const
    exact heval.aestronglyMeasurable_of_subset_isCompact hC hC.measurableSet Subset.rfl
  · filter_upwards [ae_restrict_mem hC.measurableSet] with z hz
    exact hL z hz

namespace HalfLineMetricConvergenceData

theorem eventually_integrableOn_poleEndpoint_redLength_gradient_quadratic
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
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (μ : Measure (E × ℝ)) [IsFiniteMeasure (μ.restrict (K ×ˢ Icc a c))]
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
    ∀ᶠ k in atTop,
      let d := fun z : E × ℝ =>
        (fderiv ℝ (fun v : E × ℝ =>
          redLength ((U).term (phi (co.φ (rho k)))).S 0 p
            (Phi.map (co.φ (rho k)) ((extChartAt I x).symm v.1)) v.2) z).comp
              (ContinuousLinearMap.inl ℝ E ℝ)
      IntegrableOn (fun z =>
        (w z • chartGradientBilin
          (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
            ((extChartAt I x).symm z.1)) (d z) (d z)) (K ×ˢ Icc a c) μ := by
  have hmem := eventually_memLp_fderiv_poleEndpoint_redLength_chart (c := c)
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    x hW hK hKW hWt hWJ μ 2
  have hKt : K ⊆ (extChartAt I x).target := hKW.trans hWt
  have hcarrier : Icc (1 - c) (1 - a) ⊆ (Y).D.carrier := by
    intro t ht
    change t ≤ 0
    linarith only [ht.2, ha]
  filter_upwards [hrho.eventually hmem] with k hk
  let Gk : MetricConnectionFamilyOn (I := I) (M := P.M) (Y).D :=
    (lcMetricFamily (I := I) (M := P.M)
      (fun t => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) t)).restrict (Y).D
  have hgram : ContinuousOn (chartGramOp Gk x) (Icc (1 - c) (1 - a) ×ˢ K) :=
    (continuousOn_chartGramOp_gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) x hKt).mono
      (fun z hz => ⟨hcarrier hz.1, hz.2⟩)
  exact integrableOn_reflected_chartGradientBilin Gk x hK hKt hgram w hw _ μ hk

theorem integrableOn_poleEndpoint_redLength_limit_gradient_quadratic
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
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
    let d₀ := fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    IntegrableOn (fun z =>
      (w z • chartGradientBilin (co.gInf (1 - z.2)) x
        ((extChartAt I x).symm z.1)) (d₀ z) (d₀ z)) (K ×ˢ Icc a c) μ := by
  have hmem := memLp_fderiv_poleEndpoint_redLength_limit_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hW hK hKW hWt hWJ μ 2
  have hKt : K ⊆ (extChartAt I x).target := hKW.trans hWt
  obtain ⟨n, hn⟩ := exists_nat_ge (c - 1)
  have hwindow : Icc (1 - c) (1 - a) ⊆ Icc (-(n : ℝ)) 0 := by
    intro t ht
    constructor <;> linarith only [ht.1, ht.2, hn, ha]
  let cw := (flowMetricConvergenceDataOfHalfLineWindow Phi R bf hsrc htgt
    co.φ co.strictMono co.gInf n (co.convergenceOn n).convergence).restrict Phi hwindow
  have hcarrier : Icc (1 - c) (1 - a) ⊆ (Y).D.carrier := by
    intro t ht
    change t ≤ 0
    linarith only [ht.2, ha]
  let GInf : MetricConnectionFamilyOn (I := I) (M := P.M) (Y).D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict (Y).D
  have hgram : ContinuousOn (chartGramOp GInf x) (Icc (1 - c) (1 - a) ×ˢ K) :=
    cw.continuousOn_chartGramOp Phi R bf hsrc htgt (1 - c) (1 - a) x hKt hK hcarrier
  exact integrableOn_reflected_chartGradientBilin GInf x hK hKt hgram w hw _ μ hmem

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
