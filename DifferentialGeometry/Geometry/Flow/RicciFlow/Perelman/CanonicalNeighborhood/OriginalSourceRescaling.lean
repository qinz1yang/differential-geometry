import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRescaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer
import Mathlib.Order.Filter.Finite
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.LocalInverseCapture

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metricSpace RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

theorem RealizedFiniteHorn.exists_original_source_rescaled_ball_capture
    {X : FlowSequence.{u}} (H : RealizedFiniteHorn X) (angles : EndAngles H.horn)
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length) (hzero : Tendsto d atTop (𝓝 0))
    (C : AnnularConvergence H.horn angles ray d) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ i in atTop,
      ∃ hQ : 0 < metricScalarAt H.metric (ray.point (d i)),
        let g := scaleMetric (metricScalarAt H.metric (ray.point (d i))) hQ H.metric
        let K := riemannianClosedBallOf g (ray.point (d i)) R
        IsCompact K ∧ ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 2 →
          ∀ᶠ j in atTop, K ⊆ (H.maps j).source ∧
            Nonempty (MetricComparisonOn (fun _ => g)
              (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d i))) hQ
                ((X.term (H.subseq j)).S.base.metric 0)) (H.maps j) K {0} order eps) ∧
            riemannianClosedBallOf
              (scaleMetric (metricScalarAt H.metric (ray.point (d i))) hQ
                ((X.term (H.subseq j)).S.base.metric 0))
              (H.maps j (ray.point (d i))) (R / 4) ⊆ (H.maps j) '' K ∧
            MapsTo (H.maps j) (riemannianClosedBallOf g (ray.point (d i)) (R / 8))
              (riemannianClosedBallOf
                (scaleMetric (metricScalarAt H.metric (ray.point (d i))) hQ
                  ((X.term (H.subseq j)).S.base.metric 0))
                (H.maps j (ray.point (d i))) (R / 4)) := by
  obtain ⟨c, hc, hlower⟩ := finite_horn_two_scale_lower_bound H.horn ray d hd hzero
  let R := Real.sqrt c / 4
  have hR : 0 < R := div_pos (Real.sqrt_pos.mpr hc) (by norm_num)
  have hscalar := ray.metricScalarAt_tendsto_atTop H.horn (Eventually.of_forall hd) hzero
  refine ⟨R, hR, ?_⟩
  filter_upwards [hlower, hscalar.eventually_ge_atTop 1,
    C.annuli (1 / 2) (3 / 2) (by norm_num) (by norm_num)] with i hci hQi hi
  have hQ : 0 < metricScalarAt H.metric (ray.point (d i)) := zero_lt_one.trans_le hQi
  let g := scaleMetric (metricScalarAt H.metric (ray.point (d i))) hQ H.metric
  let K := riemannianClosedBallOf g (ray.point (d i)) R
  have hroot : 0 < Real.sqrt (metricScalarAt H.metric (ray.point (d i))) :=
    Real.sqrt_pos.mpr hQ
  have hKmetric : K = Metric.closedBall (ray.point (d i))
      (R / Real.sqrt (metricScalarAt H.metric (ray.point (d i)))) := by
    ext w
    change riemannianEDistOf g (ray.point (d i)) w ≤ ENNReal.ofReal R ↔ _
    dsimp only [g]
    rw [edistOf_scale, H.horn.edist_eq_ofReal_dist,
      ← ENNReal.ofReal_mul hroot.le, ENNReal.ofReal_le_ofReal_iff hR.le,
      Metric.mem_closedBall, dist_comm w (ray.point (d i)), le_div_iff₀ hroot]
    constructor <;> intro h <;> nlinarith
  have hK : IsCompact K := by
    apply hi.1.of_isClosed_subset
    · rw [hKmetric]
      exact Metric.isClosed_closedBall
    · intro w hw
      have hdist : metricDistance g (ray.point (d i)) w ≤ R := by
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hw).trans_eq
          (ENNReal.toReal_ofReal hR.le)
      have hhalf : metricDistance g (ray.point (d i)) w < (1 / 2) * Real.sqrt c := by
        have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
        dsimp only [R] at hdist
        linarith
      have hrad := radial_ratio_mem_Ioo_of_rescaled_distance_lt H.horn ray hQ
        (hd i) (by norm_num : (0 : ℝ) < 1 / 2) hci w hhalf
      exact ⟨by linarith [hrad.1], by linarith [hrad.2]⟩
  refine ⟨hQ, hK, ?_⟩
  intro order eps heps hepshalf
  filter_upwards [H.convergence K hK order eps heps] with j hj
  obtain ⟨cmp⟩ := hj.2
  let scaled := cmp.staticRescaleOfOneLe (t := 0) (by simp)
    (metricScalarAt H.metric (ray.point (d i)))
    (metricScalarAt H.metric (ray.point (d i))) hQi hQ heps.le
    (eta := 0) (delta := eps) (by rw [div_self hQ.ne']; simp) (by simp)
  refine ⟨hj.1, ⟨scaled⟩, ?_, ?_⟩
  · apply closedBall_subset_image_of_metric_lower_crossModel g
      (scaleMetric (metricScalarAt H.metric (ray.point (d i))) hQ
        ((X.term (H.subseq j)).S.base.metric 0))
      (H.maps j) (ray.point (d i)) (L := 2) hR (by norm_num) (by linarith) hK hj.1
    intro w hw v
    have hlo := (scaled.equivalence 0 (by simp) w hw v).1
    rw [scaled.pullback_eq 0 w hw (fun _ => v)] at hlo
    have hpos := metric_inner_self_nonneg g w v
    change (1 - eps) * g.inner w v v ≤ _ at hlo
    nlinarith
  · intro w hw
    have hup : ∀ y ∈ K, ∀ v : TangentSpace I3 y,
        (scaleMetric (metricScalarAt H.metric (ray.point (d i))) hQ
          ((X.term (H.subseq j)).S.base.metric 0)).inner (H.maps j y)
            (mfderiv I3 I3 (H.maps j) y v) (mfderiv I3 I3 (H.maps j) y v) ≤
          (2 : ℝ) ^ 2 * g.inner y v v := by
      intro y hy v
      have h := (scaled.equivalence 0 (by simp) y hy v).2
      rw [scaled.pullback_eq 0 y hy (fun _ => v)] at h
      have hpos := metric_inner_self_nonneg g y v
      change _ ≤ (1 + eps) * g.inner y v v at h
      nlinarith
    have hp : ray.point (d i) ∈ riemannianClosedBallOf g (ray.point (d i)) (R / 8) := by
      change riemannianEDistOf g (ray.point (d i)) (ray.point (d i)) ≤ _
      rw [riemannianEDistOf_self]
      exact bot_le
    have hmapdist := crossModel_edist_le_of_metric_upper g
      (scaleMetric (metricScalarAt H.metric (ray.point (d i))) hQ
        ((X.term (H.subseq j)).S.base.metric 0))
      (H.maps j) (ray.point (d i)) (L := 2) (by norm_num)
      (rho := R / 8) (by positivity) (by linarith) hj.1 hup hp hw
    change riemannianEDistOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d i))) hQ
        ((X.term (H.subseq j)).S.base.metric 0))
      (H.maps j (ray.point (d i))) (H.maps j w) ≤ ENNReal.ofReal (R / 4)
    exact hmapdist.trans (by
      have h := mul_le_mul' (le_rfl : ENNReal.ofReal (2 : ℝ) ≤ ENNReal.ofReal 2) hw
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
      simpa only [show (2 : ℝ) * (R / 8) = R / 4 by ring] using h)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metricSpace RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

theorem RealizedFiniteHorn.exists_original_source_rescaled_diagonal
    {X : FlowSequence.{u}} (H : RealizedFiniteHorn X) (angles : EndAngles H.horn)
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length) (hzero : Tendsto d atTop (𝓝 0))
    (C : AnnularConvergence H.horn angles ray d) (lowerIndex : ℕ → ℕ) :
    ∃ N : ℕ, ∃ R : ℝ, ∃ j : ℕ → ℕ, 0 < R ∧ StrictMono j ∧
      StrictMono (H.subseq ∘ j) ∧ (∀ i, lowerIndex i ≤ j i) ∧
      ∃ hQ : ∀ n, 0 < metricScalarAt H.metric (ray.point (d (N + n))),
        let g := fun n => scaleMetric
          (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric
        let K := fun n => riemannianClosedBallOf (g n) (ray.point (d (N + n))) R
        (∀ n, IsCompact (K n)) ∧ ∀ i n : ℕ, n ≤ i →
          K n ⊆ (H.maps (j i)).source ∧
          Nonempty (MetricComparisonOn (fun _ => g n)
            (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
              ((X.term (H.subseq (j i))).S.base.metric 0)) (H.maps (j i)) (K n) {0} i
                (1 / ((i : ℝ) + 2))) ∧
          riemannianClosedBallOf
            (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
              ((X.term (H.subseq (j i))).S.base.metric 0))
            (H.maps (j i) (ray.point (d (N + n)))) (R / 4) ⊆ (H.maps (j i)) '' K n ∧
          MapsTo (H.maps (j i))
            (riemannianClosedBallOf (g n) (ray.point (d (N + n))) (R / 8))
            (riemannianClosedBallOf
              (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
                ((X.term (H.subseq (j i))).S.base.metric 0))
              (H.maps (j i) (ray.point (d (N + n)))) (R / 4)) := by
  classical
  obtain ⟨R, hR, hcapture⟩ := H.exists_original_source_rescaled_ball_capture
    angles ray d hd hzero C
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcapture
  have htail := fun n => hN (N + n) (Nat.le_add_right N n)
  choose hQ hK hdata using htail
  let g := fun n => scaleMetric
    (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric
  let K := fun n => riemannianClosedBallOf (g n) (ray.point (d (N + n))) R
  let P (i j : ℕ) : Prop := lowerIndex i ≤ j ∧ ∀ n ≤ i,
    K n ⊆ (H.maps j).source ∧
    Nonempty (MetricComparisonOn (fun _ => g n)
      (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
        ((X.term (H.subseq j)).S.base.metric 0)) (H.maps j) (K n) {0} i
          (1 / ((i : ℝ) + 2))) ∧
    riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
        ((X.term (H.subseq j)).S.base.metric 0))
      (H.maps j (ray.point (d (N + n)))) (R / 4) ⊆ (H.maps j) '' K n ∧
    MapsTo (H.maps j)
      (riemannianClosedBallOf (g n) (ray.point (d (N + n))) (R / 8))
      (riemannianClosedBallOf
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
          ((X.term (H.subseq j)).S.base.metric 0))
        (H.maps j (ray.point (d (N + n)))) (R / 4))
  have hP : ∀ i, ∀ᶠ j in atTop, P i j := by
    intro i
    have heps : 0 < 1 / ((i : ℝ) + 2) := by positivity
    have hepshalf : 1 / ((i : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hfinite : ∀ᶠ j in atTop, ∀ n ∈ Finset.range (i + 1),
        K n ⊆ (H.maps j).source ∧
        Nonempty (MetricComparisonOn (fun _ => g n)
          (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
            ((X.term (H.subseq j)).S.base.metric 0)) (H.maps j) (K n) {0} i
              (1 / ((i : ℝ) + 2))) ∧
        riemannianClosedBallOf
          (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
            ((X.term (H.subseq j)).S.base.metric 0))
          (H.maps j (ray.point (d (N + n)))) (R / 4) ⊆ (H.maps j) '' K n ∧
        MapsTo (H.maps j)
          (riemannianClosedBallOf (g n) (ray.point (d (N + n))) (R / 8))
          (riemannianClosedBallOf
            (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
              ((X.term (H.subseq j)).S.base.metric 0))
            (H.maps j (ray.point (d (N + n)))) (R / 4)) := by
      rw [eventually_all_finset]
      intro n hn
      exact hdata n i _ heps hepshalf
    filter_upwards [eventually_ge_atTop (lowerIndex i), hfinite] with j hj hji
    exact ⟨hj, fun n hn => hji n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))⟩
  obtain ⟨j, hj, hji⟩ := extraction_forall_of_eventually hP
  exact ⟨N, R, j, hR, hj, H.strictMono.comp hj, fun i => (hji i).1,
    hQ, hK, fun i n hn => (hji i).2 n hn⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact RealizedFiniteHorn.metricSpace
  RealizedFiniteHorn.charted RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact

variable {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
  (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ) (N : ℕ) (j : ℕ → ℕ)
  (hQ : ∀ i, 0 < metricScalarAt H.metric (ray.point (d (N + i))))

def RealizedFiniteHorn.rescaledSourceSeq : PointedRiemannianSeq.{u, 0, 0} I3 where
  obj i := { (X.term (H.subseq (j i))).atTime 0 with
    basepoint := H.maps (j i) (ray.point (d (N + i)))
    metric := scaleMetric (metricScalarAt H.metric (ray.point (d (N + i)))) (hQ i)
      ((X.term (H.subseq (j i))).S.base.metric 0) }

theorem RealizedFiniteHorn.exists_compact_rescaled_inverse_image
    {R : ℝ} (hR : 0 < R)
    (hcompare : ∀ i,
      let g := scaleMetric (metricScalarAt H.metric (ray.point (d (N + i)))) (hQ i) H.metric
      let K := riemannianClosedBallOf g (ray.point (d (N + i))) R
      K ⊆ (H.maps (j i)).source ∧ Nonempty (MetricComparisonOn (fun _ => g)
        (fun _ => (H.rescaledSourceSeq ray d N j hQ).obj i |>.metric)
        (H.maps (j i)) K {0} 0 (1 / ((i : ℝ) + 2))))
    {Q : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (G : PointedRiemannianConvergenceMaps (H.rescaledSourceSeq ray d N j hQ) Q rho)
    (D : MetricConvergenceData G)
    (hD : ∀ i, D.domain i = CanonicalMetricCompactness.canonicalSourceData G i) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : Set Q.M, IsCompact K ∧ ∀ᶠ k in atTop,
      K ⊆ G.source k ∧ ∀ w ∈ riemannianClosedBallOf
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + rho k))))
          (hQ (rho k)) H.metric) (ray.point (d (N + rho k))) r,
        H.maps (j (rho k)) w ∈ (G.partialDiffeomorph k).target ∧
        (G.partialDiffeomorph k).symm (H.maps (j (rho k)) w) ∈ K ∧
        G.map k ((G.partialDiffeomorph k).symm (H.maps (j (rho k)) w)) =
          H.maps (j (rho k)) w := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have href : ∀ i, (D.domain i).referenceMetric = (D.domain i).limitMetric := by
    intro i
    rw [hD i]
    rfl
  obtain ⟨s, hs, K, hK, hcapture⟩ :=
    G.exists_local_inverse_compact_capture D href Q.basepoint
  let r := min (R / 8) (s / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r ≤ R / 8 := min_le_left _ _
  have hrs : r ≤ s / 2 := min_le_right _ _
  refine ⟨r, hr, K, hK, ?_⟩
  filter_upwards [hcapture] with k hk
  refine ⟨hk.1, ?_⟩
  intro w hw
  let i := rho k
  let g := scaleMetric (metricScalarAt H.metric (ray.point (d (N + i)))) (hQ i) H.metric
  let target := (H.rescaledSourceSeq ray d N j hQ).obj i |>.metric
  obtain ⟨hsource, ⟨cmp⟩⟩ := hcompare i
  have heps : 1 / ((i : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have hup : ∀ y ∈ riemannianClosedBallOf g (ray.point (d (N + i))) R,
      ∀ v : TangentSpace I3 y, target.inner (H.maps (j i) y)
        (mfderiv I3 I3 (H.maps (j i)) y v) (mfderiv I3 I3 (H.maps (j i)) y v) ≤
          (2 : ℝ) ^ 2 * g.inner y v v := by
    intro y hy v
    have h := (cmp.equivalence 0 (by simp) y hy v).2
    rw [cmp.pullback_eq 0 y hy (fun _ => v)] at h
    have hpos := metric_inner_self_nonneg g y v
    change target.inner (H.maps (j i) y)
      (mfderiv I3 I3 (H.maps (j i)) y v) (mfderiv I3 I3 (H.maps (j i)) y v) ≤
        (1 + 1 / ((i : ℝ) + 2)) * g.inner y v v at h
    nlinarith
  have hp : ray.point (d (N + i)) ∈ riemannianClosedBallOf g
      (ray.point (d (N + i))) r := by
    change riemannianEDistOf g _ _ ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have hmapdist := crossModel_edist_le_of_metric_upper g target (H.maps (j i))
    (ray.point (d (N + i))) (L := 2) (by norm_num) hr.le
    (show 3 * r < R by linarith) hsource hup hp hw
  have hyball : H.maps (j i) w ∈ riemannianClosedBallOf target
      ((H.rescaledSourceSeq ray d N j hQ).obj i).basepoint s := by
    change riemannianEDistOf target (H.maps (j i) (ray.point (d (N + i))))
      (H.maps (j i) w) ≤ ENNReal.ofReal s
    refine hmapdist.trans ?_
    calc ENNReal.ofReal 2 * riemannianEDistOf g (ray.point (d (N + i))) w
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal r := mul_le_mul' le_rfl hw
      _ = ENNReal.ofReal (2 * r) := (ENNReal.ofReal_mul (by norm_num)).symm
      _ ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal (by linarith)
  apply hk.2 (H.maps (j i) w)
  have hbase : G.map k Q.basepoint =
      ((H.rescaledSourceSeq ray d N j hQ).obj i).basepoint := G.basepoint_map k
  change H.maps (j i) w ∈ riemannianClosedBallOf target (G.map k Q.basepoint) s
  exact hbase.symm ▸ hyball

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
