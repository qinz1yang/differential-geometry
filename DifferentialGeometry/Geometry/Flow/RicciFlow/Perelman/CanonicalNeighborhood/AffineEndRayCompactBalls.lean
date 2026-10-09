import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BasepointDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactSubradius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Geometry.Curvature CheegerGromovCompactness Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem NormalizedSequence.basepoint_distance_and_compact_ball_on_affine_endRay
    {eps kappa sigma : ℝ} {pinching : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma pinching)
    (Q : PointedRiemannianManifold.{u, 0, 0} I3) (hconnected : ConnectedSpace Q.M)
    (chi : ℕ → ℕ) (F : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) Q chi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (L : ℝ)
    (hcapture : ∀ A : ℝ, A < L → ∃ K : Set Q.M, IsCompact K ∧ ∀ᶠ i in atTop,
      riemannianBallOf ((X.term (chi i)).S.base.metric 0) (X.term (chi i)).basepoint A ⊆ F.map i '' K)
    (gamma : ∀ i, ℝ → (X.term (chi i)).M) (length start : ℕ → ℝ) (ell : ℝ)
    (hstart : ∀ i, start i ∈ Icc 0 (length i))
    (hzero : ∀ i, gamma i 0 = (X.term (chi i)).basepoint)
    (hsegment : ∀ i, ∀ s ∈ Icc 0 (length i), ∀ t ∈ Icc 0 (length i),
      metricDistance ((X.term (chi i)).S.base.metric 0) (gamma i s) (gamma i t) = |s - t|)
    (hlen : Tendsto length atTop (𝓝 L))
    (htail : Tendsto (fun i => length i - start i) atTop (𝓝 ell)) :
    letI := hconnected
    letI : RiemannianBundle (fun x : Q.M => TangentSpace I3 x) := Q.riemBundle
    letI : IsContinuousRiemannianBundle ThreeSpace (fun x : Q.M => TangentSpace I3 x) := Q.riemBundle_cont
    letI : TopologicalSpace.MetrizableSpace Q.M := Manifold.metrizableSpace I3 Q.M
    letI : T3Space Q.M := inferInstance
    letI : MetricSpace Q.M := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I3)
    ∀ (E : UniformSpace.Completion Q.M) (ray : EndRay E), ray.length = ell →
      (∀ r : ℝ, r < ell → TendstoUniformlyOn
        (fun i (s : Ico 0 ell) => (F.partialDiffeomorph i).symm
          (gamma i (start i + (length i - start i) * s / ell)))
        (fun s : Ico 0 ell => ray.point (ell - s)) atTop {s | (s : ℝ) ≤ r}) →
      ∀ s ∈ Ioo 0 ell,
        metricDistance Q.metric Q.basepoint (ray.point s) = L - s ∧
        ∀ r : ℝ, r < s → IsCompact (riemannianClosedBallOf Q.metric (ray.point s) r) := by
  let : ConnectedSpace Q.M := hconnected
  let : RiemannianBundle (fun x : Q.M => TangentSpace I3 x) := Q.riemBundle
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : Q.M => TangentSpace I3 x) := Q.riemBundle_cont
  let : TopologicalSpace.MetrizableSpace Q.M := Manifold.metrizableSpace I3 Q.M
  let : T3Space Q.M := inferInstance
  let : MetricSpace Q.M := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I3)
  intro E ray hray huniform s hs
  have hell : 0 < ell := hray ▸ ray.length_pos
  have hellL : ell ≤ L := le_of_tendsto_of_tendsto htail hlen
    (Eventually.of_forall fun i => by linarith [(hstart i).1])
  have hd : 0 < L - s := by linarith [hs.2]
  obtain ⟨A, hdA, hAL⟩ := exists_between (show L - s < L by linarith [hs.1])
  let b := fun i => start i + (length i - start i) * (ell - s) / ell
  have hb : ∀ i, b i ∈ Icc 0 (length i) := by
    intro i
    have hpos : 0 ≤ (length i - start i) * (ell - s) / ell :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr (hstart i).2) (by linarith [hs.2])) hell.le
    have hle : (length i - start i) * (ell - s) / ell ≤ length i - start i := by
      apply (div_le_iff₀ hell).mpr
      exact mul_le_mul_of_nonneg_left (by linarith [hs.1]) (sub_nonneg.mpr (hstart i).2)
    dsimp only [b]
    constructor <;> linarith [(hstart i).1]
  have hbLim : Tendsto b atTop (𝓝 (L - s)) := by
    have hstartLim := hlen.sub htail
    simp only [sub_sub_cancel] at hstartLim
    have hfrac := (htail.mul_const (ell - s)).div_const ell
    have hfracEq : ell * (ell - s) / ell = ell - s := by field_simp
    rw [hfracEq] at hfrac
    have hh := hstartLim.add hfrac
    have heq : L - ell + (ell - s) = L - s := by ring
    simpa only [b, heq] using hh
  have ht : ell - s ∈ Ico 0 ell := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  let t : Ico 0 ell := ⟨ell - s, ht⟩
  have hq : Tendsto (fun i => (F.partialDiffeomorph i).symm (gamma i (b i))) atTop
      (𝓝 (ray.point s)) := by
    have hh := (huniform (ell - s) ht.2).tendsto_at
      (show t ∈ {q : Ico 0 ell | (q : ℝ) ≤ ell - s} from by change ell-s≤ell-s; exact le_rfl)
    simpa only [b, t, sub_sub_cancel] using hh
  have hbase := F.basepoint_distance_eq_of_tendsto_inverse_segment C href (fun i => X.connected (chi i)) hd hdA
    (hcapture A hAL) gamma length b hzero hsegment (Eventually.of_forall hb) hbLim (ray.point s) hq
  refine ⟨hbase, ?_⟩
  intro r hrs
  by_cases hrneg : r < 0
  · have heq : riemannianClosedBallOf Q.metric (ray.point s) r = {ray.point s} := by
      ext x
      change riemannianEDistOf Q.metric (ray.point s) x ≤ ENNReal.ofReal r ↔ x = ray.point s
      rw [ENNReal.ofReal_eq_zero.mpr hrneg.le]
      change edist (ray.point s) x ≤ 0 ↔ x = ray.point s
      rw [le_zero_iff, edist_eq_zero]
      exact eq_comm
    rw [heq]
    exact isCompact_singleton
  have hr : 0 ≤ r := le_of_not_gt hrneg
  obtain ⟨B, hB, hBL⟩ := exists_between (show L-s+r<L by linarith)
  have hBpos : 0 < B := by linarith
  have hcompact := F.isCompact_closedBall_of_compact_source_ball_capture C href hBpos
    (show L-s+r<B from hB) (hcapture B hBL)
  apply hcompact.of_isClosed_subset
    (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist Q.metric (ray.point s)) continuous_const)
  intro x hx
  have hbDist : riemannianEDistOf Q.metric Q.basepoint (ray.point s) = ENNReal.ofReal (L-s) := by
    rw [← hbase, ENNReal.ofReal_toReal (riemannianEDistOf_ne_top Q.metric _ _)]
  calc
    riemannianEDistOf Q.metric Q.basepoint x ≤
        riemannianEDistOf Q.metric Q.basepoint (ray.point s) + riemannianEDistOf Q.metric (ray.point s) x :=
      riemannianEDistOf_triangle Q.metric _ _ _
    _ ≤ ENNReal.ofReal (L-s) + ENNReal.ofReal r := by rw [hbDist]; exact add_le_add le_rfl hx
    _ = ENNReal.ofReal (L-s+r) := (ENNReal.ofReal_add hd.le hr).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
