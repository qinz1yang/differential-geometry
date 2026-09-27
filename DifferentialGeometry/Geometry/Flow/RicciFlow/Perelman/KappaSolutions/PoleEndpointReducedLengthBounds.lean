import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthTimeRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedDistanceBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
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

namespace HalfLineMetricConvergenceData

theorem exists_eventually_poleEndpoint_redLength_le_on_compact
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A : ℝ}
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ᶠ k in atTop, ∀ y ∈ J,
      redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) y) 1 ≤ V := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨s, _hs, z, hz⟩ := (hancient 0).notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric s) z (by norm_num : 0 < 4) _ hz⟩
  let coW := HalfLineMetricConvergenceData.atWindow Phi co 1
  have hcarrier : Icc (-((1 : ℕ) : ℝ)) 0 ⊆ (Y).D.carrier := by
    intro t ht
    exact ht.2
  have hG := FlowMetricConvergenceData.metric_cont (Φ := Phi) hcarrier coW
  obtain ⟨B, hB, N, hdist⟩ :=
    FlowMetricConvergenceData.exists_eventually_edist_map_le_on_compact
      Phi R hR bf hsrc htgt coW hG hJ
  refine ⟨(Real.sqrt A + Real.sqrt 3 / 2 * B) ^ 2, sq_nonneg _, ?_⟩
  filter_upwards [hbase, eventually_ge_atTop N] with k hk hkN
  intro y hy
  have hdistY : riemannianEDistOf
      (((Y).term (phi (co.φ k))).S.base.metric 0)
      (q (phi (co.φ k))) (Phi.map (co.φ k) y) ≤ ENNReal.ofReal B :=
    hdist k hkN 0 (by norm_num) y hy
  have hshift : ((Y).term (phi (co.φ k))).S.base.metric 0 =
      ((U).term (phi (co.φ k))).S.base.metric (-1) := by
    simpa only [zero_sub] using poleEndpointRescaledFlowSeq_metric_eq_shift
      F hcar hreg b hbmem tau q hsigma (phi (co.φ k)) 0
  have hdistU : riemannianEDistOf (((U).term (phi (co.φ k))).S.base.metric (-1))
      (q (phi (co.φ k))) (Phi.map (co.φ k) y) ≤ ENNReal.ofReal B := by
    rw [hshift] at hdistY
    exact hdistY
  apply redLength_le_of_rescaled_distance_le
    ((U).term (phi (co.φ k))) (hancient (phi (co.φ k))) p
    (q (phi (co.φ k))) (Phi.map (co.φ k) y) zero_lt_one hB.le hk
  calc
    _ = ENNReal.ofReal (Real.sqrt ((1 : ℝ)⁻¹)) *
        riemannianEDistOf (((U).term (phi (co.φ k))).S.base.metric (-1))
          (q (phi (co.φ k))) (Phi.map (co.φ k) y) :=
      edistOf_scale _ _ _ _ _
    _ ≤ ENNReal.ofReal B := by
      simpa only [inv_one, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using hdistU

theorem exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 0 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ᶠ k in atTop, ∀ y ∈ J, ∀ t ∈ Icc a c,
      redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) y) t ≤ V := by
  obtain ⟨V, hV, hcost⟩ :=
    exists_eventually_poleEndpoint_redLength_le_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ hbase
  refine ⟨max (c ^ 2) ((1 / a) ^ 2) * V, ?_, ?_⟩
  · exact mul_nonneg ((sq_nonneg c).trans (le_max_left _ _)) hV
  · filter_upwards [hcost] with k hk
    intro y hy t ht
    have htpos : 0 < t := ha.trans_le ht.1
    have hcpos : 0 < c := htpos.trans_le ht.2
    have hratio := ancient_redLength_le_mul_time_ratio
      ((U).term (phi (co.φ k))) (hancient (phi (co.φ k)))
      p (Phi.map (co.φ k) y) zero_lt_one htpos
    simp only [div_one] at hratio
    have hmax : max (t ^ 2) ((1 / t) ^ 2) ≤ max (c ^ 2) ((1 / a) ^ 2) := by
      apply max_le
      · exact ((sq_le_sq₀ htpos.le hcpos.le).mpr ht.2).trans (le_max_left _ _)
      · exact ((sq_le_sq₀ (one_div_pos.mpr htpos).le
          (one_div_pos.mpr ha).le).mpr (one_div_le_one_div_of_le ha ht.1)).trans
          (le_max_right _ _)
    exact hratio.trans ((mul_le_mul_of_nonneg_left (hk y hy)
      ((sq_nonneg t).trans (le_max_left _ _))).trans
      (mul_le_mul_of_nonneg_right hmax hV))

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
