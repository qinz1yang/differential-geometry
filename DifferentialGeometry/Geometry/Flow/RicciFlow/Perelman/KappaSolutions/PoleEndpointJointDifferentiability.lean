import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthEquicontinuity
import DifferentialGeometry.Geometry.Metric.ChartLipschitz.Joint
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

theorem ae_eventually_differentiableAt_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod volume,
      z ∈ W ×ˢ Ioo a c → ∀ᶠ k in atTop,
        DifferentiableAt ℝ (fun v : E × ℝ =>
          redLength ((U).term (phi (co.φ k))).S 0 p
            (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) z := by
  obtain ⟨C, Dt, hC, hDt, hmodulus⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmodulus
  have hdiff (k : ℕ) :
      ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod volume,
        N ≤ k → z ∈ W ×ˢ Ioo a c →
          DifferentiableAt ℝ (fun v : E × ℝ =>
            redLength ((U).term (phi (co.φ k))).S 0 p
              (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) z := by
    by_cases hk : N ≤ k
    · have hlip : LocallyLipschitzOn (W ×ˢ Ioo a c)
          (fun v : E × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
            (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) := by
        apply Geometry.Riemannian.locallyLipschitzOn_chart_prod_of_edist_bound
          R x hWt hWJ (J := Ioo a c)
          (f := fun z : P.M × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
            (Phi.map (co.φ k) z.1) z.2) hC hDt zero_lt_one
        intro y hy w hw s hs t ht hdist
        simpa only [Real.dist_eq] using hN k hk y hy w hw s ⟨hs.1.le, hs.2.le⟩
          t ⟨ht.1.le, ht.2.le⟩ hdist
      filter_upwards [hlip.ae_differentiableAt_of_isOpen (hW.prod isOpen_Ioo)] with z hz
      exact fun _ hzw => hz hzw
    · exact Filter.Eventually.of_forall fun _ h _ => False.elim (hk h)
  filter_upwards [ae_all_iff.mpr hdiff] with z hz
  intro hzw
  filter_upwards [eventually_ge_atTop N] with k hk
  exact hz k hk hzw

theorem ae_differentiableAt_poleEndpoint_redLength_limit_chart
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
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod volume,
      z ∈ W ×ˢ Ioo a c →
        DifferentiableAt ℝ
          (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z := by
  obtain ⟨C, Dt, hC, hDt, hmodulus⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  have hlim : ∀ y ∈ J, ∀ w ∈ J, ∀ s ∈ Icc a c, ∀ t ∈ Icc a c,
      riemannianEDistOf R y w < ENNReal.ofReal 1 →
      |ell (y, s) - ell (w, t)| ≤
        C * (riemannianEDistOf R y w).toReal + Dt * |s - t| := by
    intro y hy w hw s hs t ht hdist
    apply le_of_tendsto ((hconv y hy s hs).sub (hconv w hw t ht)).abs
    filter_upwards [hrho.eventually hmodulus] with k hk
    exact hk y hy w hw s hs t ht hdist
  have hlip : LocallyLipschitzOn (W ×ˢ Ioo a c)
      (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) := by
    apply Geometry.Riemannian.locallyLipschitzOn_chart_prod_of_edist_bound
      R x hWt hWJ hC hDt zero_lt_one
    intro y hy w hw s hs t ht hdist
    simpa only [Real.dist_eq] using hlim y hy w hw s ⟨hs.1.le, hs.2.le⟩
      t ⟨ht.1.le, ht.2.le⟩ hdist
  exact hlip.ae_differentiableAt_of_isOpen (hW.prod isOpen_Ioo)

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
