import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckAlternativesLocalPullCompact
import DifferentialGeometry.Geometry.Metric.PullbackScaling

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

theorem exists_neckAlternatives_or_isCompact_of_survivor_maps :
    ∃ D : ℝ, 0 < D ∧ ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
      {R θ t₀ qs qW L : ℝ} (hR : 0 < R) {eps C1 C2 : ℝ} (_ : qs ≤ R * qW) (_ : 0 < L)
      {W : TopologicalSpace.Opens (H.stageAt t).Carrier}
      {h : ℝ → SmoothRiemannianMetric ThreeModel W}
      (a : Icc (0 : ℝ) H.horizon) (_ : (a : ℝ) = t - θ / R)
      (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
        (H.stage j.val).Carrier)
      (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)),
      (∀ j, Injective (f j)) →
      (∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
        (t : ℝ) + s / R ∈ H.stageDomain j.val →
          h s = scaleMetric R hR
            (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j))) →
      (∀ v : Icc (0 : ℝ) H.horizon, (v : ℝ) < t₀ → H.time (H.activeStage v) < v →
        ∀ p : (H.stageAt v).Carrier, qs < metricScalarAt (H.stageMetric (H.activeStage v) v) p →
          ∃ Wt : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2 p,
            Wt.capTubeHasNeckChart eps) →
      ∀ {s : ℝ}, s ∈ Icc (-θ) 0 → (t : ℝ) + s / R < t₀ →
      (∀ hv : (t : ℝ) + s / R ∈ Icc (0 : ℝ) H.horizon,
        H.time (H.activeStage ⟨_, hv⟩) < (t : ℝ) + s / R) →
      ∀ z : W, IsCompact (riemannianClosedBallOf (h 0) z 1) →
      (∀ y ∈ riemannianClosedBallOf (h 0) z 1, ∀ u : TangentSpace ThreeModel y,
        (h 0).inner y u u ≤ L ^ 2 * (h s).inner y u u) →
      qW < metricScalarAt (h s) z →
      L * (max (2 * |C1|) C2 + (D + 2 * eps⁻¹) * Real.sqrt (max (2 * |C1|) C2)) <
        Real.sqrt (metricScalarAt (h s) z) →
      Nonempty (SpatialNeck (h s) eps z) ∨
        (∃ w : W, Nonempty (SpatialNeck (h s) eps w) ∧
          metricScalarAt (h s) z ≤ max (2 * |C1|) C2 * metricScalarAt (h s) w ∧
          metricScalarAt (h s) w ≤ max (2 * |C1|) C2 * metricScalarAt (h s) z ∧
          riemannianEDistOf (h s) z w <
            ENNReal.ofReal (max (2 * |C1|) C2 / Real.sqrt (metricScalarAt (h s) z))) ∨
        IsCompact (connectedComponent z) := by
  obtain ⟨D, hD, hcore⟩ :=
    exists_neckAlternatives_or_isCompact_localPull_of_spatialCanonicalWitness.{u}
  refine ⟨D, hD, ?_⟩
  intro H t R θ t₀ qs qW L hR eps C1 C2 hqs hL W h a ha f hf hinj hp hwit s hs hst₀ hreg z
    hcpt hlower hz hsmall
  have hsR : s / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR.le
  have hθR : -θ / R ≤ s / R := div_le_div_of_nonneg_right hs.1 hR.le
  have hlo : (a : ℝ) ≤ (t : ℝ) + s / R := by
    rw [ha, sub_eq_add_neg, ← neg_div]
    linarith
  let v : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) + s / R, a.2.1.trans hlo, (by linarith : (t : ℝ) + s / R ≤ t).trans t.2.2⟩
  have hav : a ≤ v := hlo
  have hvt : v ≤ t := show (t : ℝ) + s / R ≤ t by linarith
  have hreg' := hreg v.2
  let j : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hs1 : h s = localPullMetric (scaleMetric R hR (H.stageMetric j.val v)) (f j) (hf j) := by
    rw [hp s hs j (H.activeStage_mem v), localPullMetric_scaleMetric]
  have hsc : metricScalarAt (h s) z =
      metricScalarAt (scaleMetric R hR (H.stageMetric j.val v)) (f j z) := by
    rw [hs1, metricScalarAt_localPull]
  have hqz : qs < metricScalarAt (H.stageMetric (H.activeStage v) v) (f j z) := by
    have h1 : R * qW < R * metricScalarAt (h s) z := mul_lt_mul_of_pos_left hz hR
    rw [hsc, metricScalarAt_scaleMetric, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at h1
    exact hqs.trans_lt h1
  obtain ⟨Wt, hWt⟩ := hwit v hst₀ hreg' (f j z) hqz
  have key := hcore (scaleMetric R hR (H.stageMetric j.val v)) (h 0) (hf j) (hinj j) z
    zero_lt_one hL hcpt (fun y hy u => by rw [← hs1]; exact hlower y hy u) (Wt.scaleMetric R hR)
    (hWt.scaleMetric (c := R) (hc := hR)) (by rw [one_mul, ← hsc]; exact hsmall)
  rw [← hs1] at key
  exact key

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
