import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointLipschitz
import DifferentialGeometry.Analysis.Calculus.Derivative.LocallyLipschitz


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

theorem locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
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
    (x : P.M) {W : Set E} (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    LocallyLipschitzOn (Icc a c ×ˢ W)
      (fun v : ℝ × E => ell ((extChartAt I x).symm v.2, v.1)) := by
  have hlip := locallyLipschitzOn_poleEndpoint_redLength_limit_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hWt hWJ
  have hswap : LipschitzWith 1 (Prod.swap : ℝ × E → E × ℝ) := by
    intro u v
    simp only [Prod.edist_eq, Prod.fst_swap, Prod.snd_swap, ENNReal.coe_one, one_mul]
    exact le_of_eq (max_comm _ _)
  have hmap : MapsTo (Prod.swap : ℝ × E → E × ℝ)
      (Icc a c ×ˢ W) (W ×ˢ Icc a c) := fun _ hz => ⟨hz.2, hz.1⟩
  apply locallyLipschitzOn_iff_restrict.mpr
  exact hlip.restrict.comp (hswap.lipschitzOnWith.mapsToRestrict hmap).locallyLipschitz

theorem ae_locallyLipschitzOn_poleEndpoint_redLength_limit_time_slice
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
    (x : P.M) {W : Set E} (hW : MeasurableSet W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a ≤ a') (hcc : c' ≤ c) :
    ∀ᵐ y ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).restrict W,
      LocallyLipschitzOn (Icc a' c')
        (fun t : ℝ => ell ((extChartAt I x).symm y, t)) := by
  have hlip := locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hWt hWJ
  filter_upwards [ae_restrict_mem hW] with y hy
  have hmap : MapsTo (fun t : ℝ => (t, y)) (Icc a' c') (Icc a c ×ˢ W) := by
    intro t ht
    exact ⟨⟨haa.trans ht.1, ht.2.trans hcc⟩, hy⟩
  apply locallyLipschitzOn_iff_restrict.mpr
  exact hlip.restrict.comp
    ((LipschitzWith.prodMk_right y).lipschitzOnWith.mapsToRestrict hmap).locallyLipschitz

theorem ae_differentiableAt_poleEndpoint_redLength_limit_slices
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
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c) :
    ∀ᵐ z ∂(volume.restrict (Ioc a' c')).prod
        ((DifferentialGeometry.Integral.Measure.modelHaar (E := E)).restrict W),
      DifferentiableAt ℝ (fun t : ℝ => ell ((extChartAt I x).symm z.2, t)) z.1 ∧
      DifferentiableAt ℝ (fun y : E => ell ((extChartAt I x).symm y, z.1)) z.2 := by
  have hlip := locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hWt hWJ
  have hopen : LocallyLipschitzOn (Ioo a c ×ˢ W)
      (fun v : ℝ × E => ell ((extChartAt I x).symm v.2, v.1)) :=
    hlip.mono fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩
  have hdiff := hopen.ae_differentiableAt_of_isOpen
    (μ := (volume : Measure ℝ).prod
      (DifferentialGeometry.Integral.Measure.modelHaar (E := E)))
    (isOpen_Ioo.prod hW)
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_of_ae hdiff,
    ae_restrict_mem (measurableSet_Ioc.prod hW.measurableSet)] with z hz hzs
  have hzO : z ∈ Ioo a c ×ˢ W :=
    ⟨⟨haa.trans hzs.1.1, hzs.1.2.trans_lt hcc⟩, hzs.2⟩
  have hd : DifferentiableAt ℝ
      (fun v : ℝ × E => ell ((extChartAt I x).symm v.2, v.1)) z := hz hzO
  have ht := hd.comp z.1 (show DifferentiableAt ℝ (fun t : ℝ => (t, z.2)) z.1 from
    differentiableAt_id.prodMk (differentiableAt_const z.2))
  have hs := hd.comp z.2 (show DifferentiableAt ℝ (fun y : E => (z.1, y)) z.2 from
    (differentiableAt_const z.1).prodMk differentiableAt_id)
  exact ⟨ht, hs⟩

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
