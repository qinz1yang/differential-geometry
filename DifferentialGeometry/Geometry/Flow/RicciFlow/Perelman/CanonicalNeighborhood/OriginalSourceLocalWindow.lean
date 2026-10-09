import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OriginalSourceRescaling

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle RealizedFiniteHorn.metricSpace
  RealizedFiniteHorn.charted RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact

theorem RealizedFiniteHorn.exists_rescaled_local_window_threshold
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ H : RealizedFiniteHorn X.toFlowSequence, ∀ x : ℕ → H.space,
              ∀ hQ : ∀ n, 1 ≤ metricScalarAt H.metric (x n),
                ∃ threshold : ℕ → ℕ, ∀ n j, threshold n ≤ j →
                  |metricScalarAt ((X.term (H.subseq j)).S.base.metric 0) (H.maps j (x n)) /
                    metricScalarAt H.metric (x n) - 1| < 1 / ((n : ℝ) + 2) ∧
                  ∀ hzero : (0 : ℝ) ∈ (X.interval (H.subseq j)).carrier,
                    let S := parabolicSolution (X.term (H.subseq j)).S 0
                      (metricScalarAt H.metric (x n)) (zero_lt_one.trans_le (hQ n)) hzero
                    Icc (-(c / 3)) 0 ⊆
                      (parabolicInterval (X.interval (H.subseq j)) 0
                        (metricScalarAt H.metric (x n)) hzero).carrier ∧
                    ∀ y : (X.term (H.subseq j)).M, ∀ t ∈ Icc (-(c / 3)) 0,
                      y ∈ riemannianClosedBallOf (S.base.metric 0) (H.maps j (x n))
                        (c / Real.sqrt 3) →
                      S.scalar t y ≤ 12 ∧
                      Real.sqrt (FlowMetricBall.rmNormSq S t y) ≤ C * (3 + 13 * Phi 1) := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hbound⟩ :=
    exists_rescaled_local_curvature_cylinder hmod
  refine ⟨epsStar, c, C, hepsStar, hc, hC, ?_⟩
  intro eps heps hepsStar' sigma hsigma Phi hPhi X H x hQ
  obtain ⟨scalarThreshold, hscalar⟩ := H.exists_center_scalar_threshold x
    (fun n => zero_lt_one.trans_le (hQ n)) (fun n => 1 / ((n : ℝ) + 2)) (fun _ => by positivity)
  obtain ⟨propThreshold, hprop⟩ := eventually_atTop.1
    (hbound eps heps hepsStar' sigma hsigma Phi hPhi X)
  refine ⟨fun n => max (scalarThreshold n) propThreshold, ?_⟩
  intro n j hj
  have hclose := hscalar n j ((le_max_left _ _).trans hj)
  refine ⟨hclose, ?_⟩
  have hq : 0 < metricScalarAt H.metric (x n) := zero_lt_one.trans_le (hQ n)
  have herr : 1 / ((n : ℝ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < (n : ℝ) + 2)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have habs : |(X.term (H.subseq j)).S.scalar 0 (H.maps j (x n))| ≤
      2 * metricScalarAt H.metric (x n) := by
    have h := abs_lt.mp (hclose.trans_le herr)
    have hlo : 0 < metricScalarAt ((X.term (H.subseq j)).S.base.metric 0)
        (H.maps j (x n)) := by
      have hdiv : 0 < metricScalarAt ((X.term (H.subseq j)).S.base.metric 0)
          (H.maps j (x n)) / metricScalarAt H.metric (x n) := by linarith [h.1]
      exact (div_pos_iff.mp hdiv).resolve_right (by intro h'; linarith [h'.2]) |>.1
    have hhi : metricScalarAt ((X.term (H.subseq j)).S.base.metric 0)
        (H.maps j (x n)) ≤ 2 * metricScalarAt H.metric (x n) := by
      rw [← div_le_iff₀ hq]
      linarith [h.2]
    change |metricScalarAt ((X.term (H.subseq j)).S.base.metric 0) (H.maps j (x n))| ≤ _
    rw [abs_of_pos hlo]
    exact hhi
  exact hprop (H.subseq j)
    (((le_max_right _ _).trans hj).trans (H.strictMono.id_le j))
    _ hq (hQ n) (H.maps j (x n)) habs

theorem RealizedFiniteHorn.exists_original_source_local_solutions
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, ∃ hc : 0 < c, 0 < epsStar ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ H : RealizedFiniteHorn X.toFlowSequence, ∀ x : ℕ → H.space,
              ∀ hQ : ∀ n, 1 ≤ metricScalarAt H.metric (x n),
                ∃ threshold : ℕ → ℕ, ∀ n j, threshold n ≤ j →
                  ∃ S : SolutionOn (I := I3) (M := (X.term (H.subseq j)).M)
                    (RealTimeInterval.closed (-(c / 6)) 0 (by linarith)),
                    IsSolutionOn S ∧
                    (∀ t, S.base.metric t =
                      scaleMetric (metricScalarAt H.metric (x n))
                        (zero_lt_one.trans_le (hQ n))
                        ((X.term (H.subseq j)).S.base.metric
                          (t / metricScalarAt H.metric (x n)))) ∧
                    (∀ t ∈ Icc (-(c / 6)) 0, RiemannianMetricComplete (S.base.metric t)) ∧
                    |S.scalar 0 (H.maps j (x n)) - 1| < 1 / ((n : ℝ) + 2) ∧
                    ∀ y : (X.term (H.subseq j)).M, ∀ t ∈ Icc (-(c / 6)) 0,
                      y ∈ riemannianClosedBallOf (S.base.metric 0) (H.maps j (x n))
                        (c / Real.sqrt 3) →
                      S.scalar t y ≤ 12 ∧
                      Real.sqrt (FlowMetricBall.rmNormSq S t y) ≤ C * (3 + 13 * Phi 1) := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hbound⟩ :=
    RealizedFiniteHorn.exists_rescaled_local_window_threshold hmod
  refine ⟨epsStar, c, C, hc, hepsStar, hC, ?_⟩
  intro eps heps hepsStar' sigma hsigma Phi hPhi X H x hQ
  obtain ⟨threshold, hthreshold⟩ :=
    hbound eps heps hepsStar' sigma hsigma Phi hPhi X H x hQ
  refine ⟨threshold, ?_⟩
  intro n j hj
  let q := metricScalarAt H.metric (x n)
  have hq : 0 < q := zero_lt_one.trans_le (hQ n)
  have hzero : (0 : ℝ) ∈ (X.interval (H.subseq j)).carrier := by
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos (H.subseq j)], le_rfl⟩
  let P := parabolicSolution (X.term (H.subseq j)).S 0 q hq hzero
  let D := RealTimeInterval.closed (-(c / 6)) 0 (by linarith : -(c / 6) ≤ 0)
  obtain ⟨hcenter, hlocal⟩ := hthreshold n j hj
  obtain ⟨hwindow, hcurv⟩ := hlocal hzero
  have hcarrier : D.carrier ⊆ (parabolicInterval (X.interval (H.subseq j)) 0 q hzero).carrier := by
    intro t ht
    exact hwindow ⟨by have htleft : -(c / 6) ≤ t := ht.1; linarith, ht.2⟩
  have hreg : D.regular ⊆ (parabolicInterval (X.interval (H.subseq j)) 0 q hzero).regular := by
    have hleft := hwindow (show -(c / 3) ∈ Icc (-(c / 3)) 0 by
      exact ⟨le_rfl, by linarith⟩)
    change parabolicTime 0 q (-(c / 3)) ∈ (X.interval (H.subseq j)).carrier at hleft
    rw [X.carrier_eq] at hleft
    intro t ht
    change parabolicTime 0 q t ∈ (X.interval (H.subseq j)).regular
    rw [X.regular_eq]
    simp only [parabolicTime, zero_add] at hleft ⊢
    have htleft : -(c / 6) < t := ht.1
    have hlt : -(c / 3) / q < t / q := (div_lt_div_iff_of_pos_right hq).mpr (by linarith)
    exact ⟨hleft.1.trans_lt hlt, div_neg_of_neg_of_pos ht.2 hq⟩
  refine ⟨P.timeRestrict D, isSolutionOn_timeRestrict
    (parabolicSolution_isSolutionOn _ (X.term (H.subseq j)).isSolution 0 q hq hzero)
      hcarrier hreg, ?_, ?_, ?_, ?_⟩
  · intro t
    change scaleMetric q hq ((X.term (H.subseq j)).S.base.metric (0 + t / q)) = _
    rw [zero_add]
  · intro t ht
    have htcarrier := hcarrier ht
    change parabolicTime 0 q t ∈ (X.interval (H.subseq j)).carrier at htcarrier
    have hcomplete : RiemannianMetricComplete
        ((X.term (H.subseq j)).S.base.metric (parabolicTime 0 q t)) :=
      ⟨MetricComplete.complete ((X.term (H.subseq j)).atTime (parabolicTime 0 q t))
        (X.complete (H.subseq j) (parabolicTime 0 q t) htcarrier)⟩
    exact hcomplete.scaleMetric q hq
  · change |P.scalar 0 (H.maps j (x n)) - 1| < _
    rw [parabolicSolution_scalar]
    change |q⁻¹ * (X.term (H.subseq j)).S.scalar (parabolicTime 0 q 0) (H.maps j (x n)) - 1| < _
    rw [parabolicTime_zero]
    change |q⁻¹ * metricScalarAt ((X.term (H.subseq j)).S.base.metric 0) (H.maps j (x n)) - 1| < _
    simpa only [q, div_eq_inv_mul] using hcenter
  · intro y t ht hy
    exact hcurv y t ⟨by linarith [ht.1], ht.2⟩ hy

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
