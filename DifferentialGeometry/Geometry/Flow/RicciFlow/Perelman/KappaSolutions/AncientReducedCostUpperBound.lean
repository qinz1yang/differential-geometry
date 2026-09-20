import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.MetricUpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance costUpperTopology : TopologicalSpace F.M := F.topology
private local instance costUpperCharted : ChartedSpace H F.M := F.charted
private local instance costUpperSmooth : IsManifold I ∞ F.M := F.smooth
private local instance costUpperT2 : T2Space F.M := F.t2
private local instance costUpperTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle
private local instance costUpperSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancient_lCost_le_earlier_distance_sq_div_add
    {kappa R : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hR : PointedFlowScalarBounded F R)
    {T r : ℝ} (hT : T ≤ 0) (hr : 0 < r) (p q : F.M) :
    lCost F.S T p q (r ^ 2) ≤
      (riemannianEDistOf (I := I) (F.S.base.metric (T - r ^ 2)) p q).toReal ^ 2 /
        (2 * r) + 2 * R * r ^ 3 := by
  let : ConnectedSpace F.M := hF.connected
  have htime (u : ℝ) : T - u ^ 2 ∈ ancientTimeInterval.carrier := by
    change T - u ^ 2 ≤ 0
    nlinarith [sq_nonneg u]
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric (T - r ^ 2)) :=
    ⟨hF.complete (T - r ^ 2) (htime r)⟩
  apply lCost_le_riemannianEDistOf_sq_div_add_of_metric_le F.S F.isSolution
    (F.S.base.metric (T - r ^ 2)) hcomplete hr (fun u _ => htime u)
  · intro u hu z v
    have hu2 : u ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hu.1 hr.le).mpr hu.2
    exact hF.metric_inner_le (by linarith) (htime u) z v
  · intro u hu z
    exact hR (T - u) (by change T - u ≤ 0; linarith [hu.1]) z

theorem exists_ancient_lCost_upper_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ R : ℝ, 0 ≤ R ∧ PointedFlowScalarBounded F R ∧
      ∀ T ≤ 0, ∀ r > 0, ∀ p q : F.M,
      lCost F.S T p q (r ^ 2) ≤
        (riemannianEDistOf (I := I) (F.S.base.metric (T - r ^ 2)) p q).toReal ^ 2 /
          (2 * r) + 2 * R * r ^ 3 := by
  obtain ⟨R, hR⟩ := hF.globalScalarBound
  have hRnonneg : 0 ≤ R := (hR 0 (by change (0 : ℝ) ≤ 0; rfl) F.basepoint).1.trans
    (hR 0 (by change (0 : ℝ) ≤ 0; rfl) F.basepoint).2
  exact ⟨R, hRnonneg, hR, fun T hT r hr p q =>
    ancient_lCost_le_earlier_distance_sq_div_add F hF hR hT hr p q⟩

theorem ancient_lCost_shifted_le_distance_sq_div_add
    {kappa R : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hR : PointedFlowScalarBounded F R)
    {d s : ℝ} (hd : 0 < d) (hs : Real.sqrt d < s) (p q : F.M) :
    let r := Real.sqrt (s ^ 2 - d)
    lCost F.S (-d) p q (r ^ 2) ≤
      (riemannianEDistOf (I := I) (F.S.base.metric (-(s ^ 2))) p q).toReal ^ 2 /
        (2 * r) + 2 * R * r ^ 3 := by
  let r := Real.sqrt (s ^ 2 - d)
  have hspos : 0 < s := (Real.sqrt_nonneg d).trans_lt hs
  have hpos : 0 < s ^ 2 - d := by
    have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg d) hspos.le).mpr hs
    rw [Real.sq_sqrt hd.le] at hsq
    exact sub_pos.mpr hsq
  have hr : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r ^ 2 = s ^ 2 - d := Real.sq_sqrt hpos.le
  have htime : -d - r ^ 2 = -(s ^ 2) := by rw [hr2]; ring
  have h := ancient_lCost_le_earlier_distance_sq_div_add F hF hR
    (neg_nonpos.mpr hd.le) hr p q
  rw [htime] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
