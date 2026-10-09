import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTailEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseDistanceControl

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (times : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < times i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem times q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem times q hsigma

omit [I.Boundaryless] in
private theorem metric_inner_at_later_time_le_of_ancient
    (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hG : IsAncientKappaSolution kappa G)
    {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0) (x : G.M) (v : TangentSpace I x) :
    (G.S.base.metric t).inner x v v ≤ (G.S.base.metric s).inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 G.M := IsManifold.of_le (n := ∞) (by decide)
  have hRic : ∀ r ∈ Ioo s t, ∀ y : G.M, ∀ w : TangentSpace I y,
      0 ≤ G.S.ricciAt r y (vec2 w w) := by
    intro r hr y w
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (G.S.base.metric r) y).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hG.nonnegativeCurvatureOperator r (hr.2.le.trans ht) y n c a b
  exact metric_inner_antitoneOn_of_ricci_nonnegative_interior G.S G.isSolution
    (fun _ hr => hr.2.trans ht) (fun _ hr => hr.2.trans_le ht) hRic x v
    ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

namespace HalfLineMetricConvergenceData

theorem exists_compact_eventual_poleEndpoint_minimizer_capture_on_time_interval
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J)
    {δ T A D : ℝ} (hδ : 1 < δ) (hD : 0 ≤ D)
    (hcost : ∀ᶠ k in atTop, ∀ tau ∈ Icc δ T, ∀ y ∈ J,
      redLength ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) y) tau ≤ A)
    (hdist : ∀ᶠ k in atTop, ∀ y ∈ J,
      riemannianEDistOf (((Y).term (phi (co.φ k))).S.base.metric 0)
        (q (phi (co.φ k))) (Phi.map (co.φ k) y) ≤ ENNReal.ofReal D) :
    ∃ K : Set P.M, IsCompact K ∧ J ⊆ K ∧
      ∀ᶠ k in atTop, ∀ tau ∈ Icc δ T, ∀ y ∈ J,
        ∀ alpha : ℝ → F.M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
        IsLRegularizedGeodesicOn ((U).term (phi (co.φ k))).S 0 alpha
          (Ioc 0 (Real.sqrt tau)) →
        alpha 0 = p →
        alpha (Real.sqrt tau) = Phi.map (co.φ k) y →
        lRegularizedAction ((U).term (phi (co.φ k))).S 0 alpha 0 (Real.sqrt tau) =
          lCost ((U).term (phi (co.φ k))).S 0 p
            (Phi.map (co.φ k) y) tau →
        alpha '' Icc (max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt tau / 2))
          (Real.sqrt tau) ⊆ Phi.map (co.φ k) '' K := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := (hF 0).notFlat
    exact DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) y (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t y) hy⟩
  let L : ℝ := Real.sqrt T * Real.sqrt (2 * Real.exp (24 * A) * A)
  have hL : 0 ≤ L := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨C, _, hreference⟩ :=
    HalfLineMetricConvergenceData.exists_canonicalMetricConvergenceData
      Phi co (t := 0) le_rfl
  obtain ⟨hcompact, k0, hcapture⟩ := exists_pointed_inverse_distance_control
    C hreference hcomplete (D + L) (add_nonneg hD hL) 1 zero_lt_one
  let K0 := riemannianClosedBallOf (co.gInf 0) P.basepoint (2 * (D + L))
  have hK0 : IsCompact K0 := by
    simpa only [one_add_one_eq_two] using hcompact
  refine ⟨J ∪ K0, hJ.union hK0, subset_union_left, ?_⟩
  filter_upwards [hcost, hdist, eventually_ge_atTop k0] with k hcostk hdistk hk
  intro tau htau y hy alpha halpha hgeo hstart hend haction
  have htaupos : 0 < tau := (zero_lt_one.trans hδ).trans_le htau.1
  have haction' : lRegularizedAction ((U).term (phi (co.φ k))).S 0 alpha 0 (Real.sqrt tau) =
      lCost ((U).term (phi (co.φ k))).S 0 (alpha 0)
        (alpha (Real.sqrt tau)) tau := by
    simpa only [hstart, hend] using haction
  have hcost' : redLength ((U).term (phi (co.φ k))).S 0
      (alpha 0) (alpha (Real.sqrt tau)) tau ≤ A := by
    simpa only [hstart, hend] using hcostk tau htau y hy
  have hdist' : riemannianEDistOf (((Y).term (phi (co.φ k))).S.base.metric 0)
      (q (phi (co.φ k))) (alpha (Real.sqrt tau)) ≤ ENNReal.ofReal D := by
    simpa only [hend] using hdistk y hy
  rintro z ⟨s, hs, rfl⟩
  have hsHalf : s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau) :=
    ⟨(le_max_right _ _).trans hs.1, hs.2⟩
  have htail := (hF (phi (co.φ k))).riemannianEDist_endpoint_le_exp_redLength_on_half_tail
    alpha halpha
    (alpha 0) htaupos hsHalf
    (fun r hr ↦ hgeo r ⟨hr.1, hr.2.le⟩) haction' hcost'
  have htail0 : riemannianEDistOf (((Y).term (phi (co.φ k))).S.base.metric 0)
      (alpha s) (alpha (Real.sqrt tau)) ≤ ENNReal.ofReal L := by
    calc
      _ ≤ riemannianEDistOf (((U).term (phi (co.φ k))).S.base.metric (-tau))
          (alpha s) (alpha (Real.sqrt tau)) := by
          rw [poleEndpointRescaledFlowSeq_metric_eq_shift, zero_sub]
          exact edistOf_mono _ _
            (metric_inner_at_later_time_le_of_ancient
              ((U).term (phi (co.φ k))) (hF (phi (co.φ k)))
              (by linarith [htau.1]) (by norm_num)) _ _
      _ ≤ ENNReal.ofReal
          (Real.sqrt tau * Real.sqrt (2 * Real.exp (24 * A) * A)) := htail
      _ ≤ ENNReal.ofReal L := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt htau.2) (Real.sqrt_nonneg _))
  have hball : alpha s ∈ riemannianClosedBallOf
      (((Y).term (phi (co.φ k))).S.base.metric 0) (q (phi (co.φ k)))
      (D + L) := by
    change riemannianEDistOf _ _ _ ≤ _
    calc
      _ ≤ riemannianEDistOf (((Y).term (phi (co.φ k))).S.base.metric 0)
          (q (phi (co.φ k))) (alpha (Real.sqrt tau)) +
          riemannianEDistOf (((Y).term (phi (co.φ k))).S.base.metric 0)
            (alpha (Real.sqrt tau)) (alpha s) := riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal D + ENNReal.ofReal L := by
        apply add_le_add hdist'
        exact (riemannianEDistOf_comm
          (((Y).term (phi (co.φ k))).S.base.metric 0)
          (alpha (Real.sqrt tau)) (alpha s)).trans_le htail0
      _ = ENNReal.ofReal (D + L) := (ENNReal.ofReal_add hD hL).symm
  obtain ⟨htarget, hinverse⟩ := (hcapture k hk).1 (alpha s) hball
  have hinverse' : (Phi.partialDiffeomorph (co.φ k)).symm (alpha s) ∈ K0 := by
    rw [one_add_one_eq_two] at hinverse
    exact hinverse
  exact ⟨(Phi.partialDiffeomorph (co.φ k)).symm (alpha s), Or.inr hinverse',
    (Phi.partialDiffeomorph (co.φ k)).right_inv' htarget⟩


theorem exists_compact_eventual_poleEndpoint_minimizer_capture_of_basepoint_bound
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J)
    {δ T A : ℝ} (hδ : 1 < δ)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A) :
    ∃ K : Set P.M, IsCompact K ∧ J ⊆ K ∧
      ∀ᶠ k in atTop, ∀ tau ∈ Icc δ T, ∀ y ∈ J,
        ∀ alpha : ℝ → F.M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
        IsLRegularizedGeodesicOn ((U).term (phi (co.φ k))).S 0 alpha
          (Ioc 0 (Real.sqrt tau)) →
        alpha 0 = p →
        alpha (Real.sqrt tau) = Phi.map (co.φ k) y →
        lRegularizedAction ((U).term (phi (co.φ k))).S 0 alpha 0 (Real.sqrt tau) =
          lCost ((U).term (phi (co.φ k))).S 0 p
            (Phi.map (co.φ k) y) tau →
        alpha '' Icc (max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt tau / 2))
          (Real.sqrt tau) ⊆ Phi.map (co.φ k) '' K := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := (hF 0).notFlat
    exact DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) y (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t y) hy⟩
  let coW := HalfLineMetricConvergenceData.atWindow Phi co 1
  have hcarrier : Icc (-((1 : ℕ) : ℝ)) 0 ⊆ (Y).D.carrier := by
    intro t ht
    exact ht.2
  have hG := FlowMetricConvergenceData.metric_cont (Φ := Phi) hcarrier coW
  obtain ⟨D, hD, N, hdist⟩ :=
    FlowMetricConvergenceData.exists_eventually_edist_map_le_on_compact
      Phi R hR bf hsrc htgt coW hG hJ
  have hdistEv : ∀ᶠ k in atTop, ∀ y ∈ J,
      riemannianEDistOf (((Y).term (phi (co.φ k))).S.base.metric 0)
        (q (phi (co.φ k))) (Phi.map (co.φ k) y) ≤ ENNReal.ofReal D := by
    filter_upwards [eventually_ge_atTop N] with k hk
    exact hdist k hk 0 (by norm_num)
  obtain ⟨V, _hV, hcost⟩ :=
    exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
      F hcar hreg b hbmem times q hsigma Phi R hR co kappa hF p hJ
        (zero_lt_one.trans hδ) hbase
  exact exists_compact_eventual_poleEndpoint_minimizer_capture_on_time_interval
    F hcar hreg b hbmem times q hsigma Phi co hcomplete kappa hF p hJ hδ hD.le
    (hcost.mono fun _ hk tau htau y hy ↦ hk y hy tau htau) hdistEv

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
