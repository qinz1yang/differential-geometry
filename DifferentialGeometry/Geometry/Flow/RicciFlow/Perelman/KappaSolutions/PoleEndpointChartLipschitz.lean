import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthEquicontinuity
import DifferentialGeometry.Geometry.Metric.ChartLipschitz.CompactInverse


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal NNReal

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

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_eventually_lipschitzOnWith_poleEndpoint_redLength_in_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) (a : P.M) {J : Set P.M} (hJ : IsCompact J)
    (hchart : J ⊆ (chartAt H a).source) {A δ T : ℝ} (hδ : 1 ≤ δ)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A) :
    ∃ L : ℝ≥0, ∀ᶠ k in atTop, ∀ t ∈ Icc δ T, ∀ y ∈ J, ∃ s : Set E,
      s ∈ 𝓝 (extChartAt I a y) ∧
      LipschitzOnWith L
        (fun v => redLength ((U).term (phi (co.φ k))).S 0 p
          (Phi.map (co.φ k) ((extChartAt I a).symm v)) t) s := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨s, _, z, hz⟩ := (hancient 0).notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric s) z (by norm_num : 0 < 4) _ hz⟩
  let : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let : T3Space P.M := inferInstance
  let : RiemannianBundle (fun x : P.M => TangentSpace I x) := ⟨R.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : P.M => TangentSpace I x) :=
    ⟨R.inner, R.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace P.M := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I) (M := P.M)
  have hedist (x y : P.M) : edist x y = riemannianEDistOf R x y :=
    IsRiemannianManifold.out (I := I) x y
  have hchartExt : J ⊆ (extChartAt I a).source := by
    simpa only [extChartAt_source] using hchart
  have hcoords : IsCompact ((extChartAt I a) '' J) :=
    hJ.image_of_continuousOn ((continuousOn_extChartAt (I := I) a).mono hchartExt)
  have htarget : (extChartAt I a) '' J ⊆ (extChartAt I a).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (extChartAt I a).map_source (hchartExt hy)
  obtain ⟨B, V, hV, hJV, hVt, hVc, hLipInv⟩ :=
    Geometry.Riemannian.exists_lipschitzOnWith_extChartAt_symm_near_isCompact a hcoords htarget
  let K : Set P.M := (extChartAt I a).symm '' closure V
  have hK : IsCompact K :=
    hVc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) a).mono hVt)
  obtain ⟨C, hC, hdiff⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hK hδ hbase
  refine ⟨⟨C, hC⟩ * B, ?_⟩
  filter_upwards [hdiff] with k hk
  intro t ht y hy
  let r : ℝ := (2 * ((B : ℝ) + 1))⁻¹
  have hr : 0 < r := by dsimp only [r]; positivity
  let s : Set E := V ∩ Metric.ball (extChartAt I a y) r
  have hs : s ∈ 𝓝 (extChartAt I a y) :=
    inter_mem (hV.mem_nhds (hJV (mem_image_of_mem _ hy))) (Metric.ball_mem_nhds _ hr)
  refine ⟨s, hs, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro u hu v hv
  have huV : u ∈ closure V := subset_closure hu.1
  have hvV : v ∈ closure V := subset_closure hv.1
  have hd : dist ((extChartAt I a).symm u) ((extChartAt I a).symm v) ≤
      (B : ℝ) * dist u v := hLipInv.dist_le_mul u huV v hvV
  have huv : dist u v < 2 * r := by
    calc
      dist u v ≤ dist u (extChartAt I a y) + dist (extChartAt I a y) v :=
        dist_triangle _ _ _
      _ < 2 * r := by
        have hu' : dist u (extChartAt I a y) < r := hu.2
        have hv' : dist v (extChartAt I a y) < r := hv.2
        rw [dist_comm (extChartAt I a y) v]
        linarith
  have hscale : 2 * ((B : ℝ) + 1) * r = 1 := by
    dsimp only [r]
    exact mul_inv_cancel₀ (by positivity)
  have hsmall : dist ((extChartAt I a).symm u) ((extChartAt I a).symm v) < 1 := by
    have hmul := mul_le_mul_of_nonneg_left huv.le B.coe_nonneg
    nlinarith only [hd, hmul, hscale, hr]
  have hedsmall : riemannianEDistOf R ((extChartAt I a).symm u)
      ((extChartAt I a).symm v) < ENNReal.ofReal 1 := by
    rw [← hedist, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hsmall
  have hpoint := hk ((extChartAt I a).symm u) (mem_image_of_mem _ huV)
    ((extChartAt I a).symm v) (mem_image_of_mem _ hvV) t ht hedsmall
  rw [← hedist, edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hpoint
  have hfinal := hpoint.trans (mul_le_mul_of_nonneg_left hd hC)
  change _ ≤ C * (B : ℝ) * dist u v
  simpa only [Real.dist_eq, mul_assoc] using hfinal

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
