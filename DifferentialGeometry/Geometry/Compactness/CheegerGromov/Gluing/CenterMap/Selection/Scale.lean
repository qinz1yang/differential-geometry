import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Uniform.HatBounds

import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.ExponentialBallCovering
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Transition.Refinement
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.MetricCompactness.Inputs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.AtomWeights.Convergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.AtomWeights.Subsequence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Transition.Pairwise
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Source.Cover
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

noncomputable local instance centerMapModelModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance centerMapModelModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance centerMapModelModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance centerMapModelModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem normalChart_image_closedBall_subset_expMapC2_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < metricCoerciveExpRadius (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    (NormalCoordinates.normalChartAt (I := I) Y.metric c) '' Metric.closedBall c R ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric c) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := P.ms
  let : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  rintro a ⟨q, hq, rfl⟩
  have hdist_le : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    calc
      riemannianEDist I c q =
          (letI : EMetricSpace Y.M := Y.emetricSpace (I := I); edist c q) := by rfl
      _ = ENNReal.ofReal (dist c q) := P.realizes c q
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]; exact ENNReal.ofReal_ne_top
  have hsmall : (riemannianEDist I c q).toReal < metricCoerciveExpRadius (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact lt_of_le_of_lt hdist_le hR
  obtain ⟨v, hv_target, _hv_dom, hv_len, hy_eq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  have hchart : NormalCoordinates.normalChartAt (I := I) Y.metric c q = v := by
    have hsymm : (NormalCoordinates.normalChartAt (I := I) Y.metric c).symm v = q := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Y.metric c hv_target]
      exact hy_eq.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) Y.metric c).right_inv hv_target
  rw [Metric.mem_ball, dist_zero_right, hchart]
  have hsq : Real.sqrt (Y.metric.inner c v v) < metricCoerciveExpRadius (I := I) Y.metric c := by
    rw [hv_len]; exact hsmall
  exact norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric c hsq

theorem normalChart_image_closedBall_subset_ball_of_coercive_bound
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R σ : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < metricCoerciveExpRadius (I := I) Y.metric c)
    (hσ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R / Real.sqrt (metricCoerciveConst (I := I) Y.metric c) < σ) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    (NormalCoordinates.normalChartAt (I := I) Y.metric c) '' Metric.closedBall c R ⊆
      Metric.ball (0 : E) σ := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := P.ms
  let : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  rintro a ⟨q, hq, rfl⟩
  have hdist_le : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    calc
      riemannianEDist I c q =
          (letI : EMetricSpace Y.M := Y.emetricSpace (I := I); edist c q) := by rfl
      _ = ENNReal.ofReal (dist c q) := P.realizes c q
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]; exact ENNReal.ofReal_ne_top
  have hsmall : (riemannianEDist I c q).toReal < metricCoerciveExpRadius (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact lt_of_le_of_lt hdist_le hR
  obtain ⟨v, hv_target, _hv_dom, hv_len, hy_eq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  have hchart : NormalCoordinates.normalChartAt (I := I) Y.metric c q = v := by
    have hsymm : (NormalCoordinates.normalChartAt (I := I) Y.metric c).symm v = q := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Y.metric c hv_target]
      exact hy_eq.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) Y.metric c).right_inv hv_target
  rw [Metric.mem_ball, dist_zero_right, hchart]
  have hcoerc : 0 < metricCoerciveConst (I := I) Y.metric c := metricCoerciveConst_pos (I := I) Y.metric c
  have hsc : 0 < Real.sqrt (metricCoerciveConst (I := I) Y.metric c) := Real.sqrt_pos.mpr hcoerc
  have hcle : metricCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2 ≤ Y.metric.inner c v v :=
    metricCoerciveConst_le (I := I) Y.metric c v
  have hsqrt_le :
      Real.sqrt (metricCoerciveConst (I := I) Y.metric c) * ‖v‖ ≤
        Real.sqrt (Y.metric.inner c v v) := by
    have hrw : Real.sqrt (metricCoerciveConst (I := I) Y.metric c) * ‖v‖
        = Real.sqrt (metricCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2) := by
      rw [Real.sqrt_mul (le_of_lt hcoerc), Real.sqrt_sq (norm_nonneg v)]
    rw [hrw]
    exact Real.sqrt_le_sqrt hcle
  have hgc_le : Real.sqrt (Y.metric.inner c v v) ≤ R := by
    rw [hv_len, hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact hdist_le
  have hbound : ‖v‖ ≤ R / Real.sqrt (metricCoerciveConst (I := I) Y.metric c) := by
    rw [le_div_iff₀ hsc]
    calc ‖v‖ * Real.sqrt (metricCoerciveConst (I := I) Y.metric c)
        = Real.sqrt (metricCoerciveConst (I := I) Y.metric c) * ‖v‖ := by ring
      _ ≤ Real.sqrt (Y.metric.inner c v v) := hsqrt_le
      _ ≤ R := hgc_le
  exact lt_of_le_of_lt hbound hσ

theorem normalChart_image_hatSourceCage_subset_expMapC2_ball (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        metricCoerciveExpRadius (I := I) (X.obj (L.φ n)).metric (center gamma)) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ n)).metric (center gamma)) := by
  let : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  let : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  let : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  let : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  let : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  refine Set.Subset.trans
    (Set.image_mono
      (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter)) ?_
  exact normalChart_image_closedBall_subset_expMapC2_ball (I := I) (X.obj (L.φ n)) (P (L.φ n))
    (c := center gamma) (R := 4 * L.lamInf (gamma : Nat)) hR

theorem normalChart_image_hatSourceCage_subset_ball_of_coercive_bound (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (sigma : Fin (pb.A r) -> Real)
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        metricCoerciveExpRadius (I := I) (X.obj (L.φ n)).metric (center gamma))
    (hσ :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) /
          Real.sqrt (metricCoerciveConst (I := I) (X.obj (L.φ n)).metric (center gamma)) <
        sigma gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.ball (0 : E) (sigma gamma) := by
  let : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  let : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  let : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  let : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  let : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  refine Set.Subset.trans
    (Set.image_mono
      (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter)) ?_
  exact normalChart_image_closedBall_subset_ball_of_coercive_bound (I := I) (X.obj (L.φ n)) (P (L.φ n))
    (c := center gamma) (R := 4 * L.lamInf (gamma : Nat)) (σ := sigma gamma) hR hσ

theorem hUx_of_sigma (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M) (σ : Fin (pb.A r) -> Real)
    (hσ : forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)) :
    forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) (σ gamma) ⊆
        Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)) := by
  intro gamma k
  exact Metric.ball_subset_ball (hσ gamma k)

def SigmaScaleAt (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (σ : Fin (pb.A r) -> Real) (n : Nat) : Prop :=
  forall gamma : Fin (pb.A r),
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) /
        Real.sqrt (metricCoerciveConst (I := I) (X.obj (L.φ n)).metric (x gamma n)) < σ gamma ∧
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ n)).metric (x gamma n)

def SigmaScaleTail (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (σ : Fin (pb.A r) -> Real) : Prop :=
  ∀ᶠ n in Filter.atTop, SigmaScaleAt (I := I) hd P L pb r x σ n

def SigmaScaleField (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M) (σ : Fin (pb.A r) -> Real) : Prop :=
  forall gamma : Fin (pb.A r), forall k : Nat,
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) /
        Real.sqrt (metricCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) < σ gamma ∧
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)

theorem SigmaScaleField.at {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ) (n : Nat) :
    SigmaScaleAt (I := I) hd P L pb r x σ n := fun gamma => hfield gamma n

theorem SigmaScaleField.to_tail {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ) :
    SigmaScaleTail (I := I) hd P L pb r x σ :=
  Filter.Eventually.of_forall hfield.at

theorem SigmaScaleTail.subseq {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (htail : SigmaScaleTail (I := I) hd P L pb r x σ)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    SigmaScaleTail (I := I) hd P (L.subseq hψ) pb r
      (fun gamma k => x gamma (ψ k)) σ := by
  filter_upwards [hψ.tendsto_atTop.eventually htail] with n hn
  intro gamma
  exact hn gamma

theorem SigmaScaleTail.exists_field
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (htail : SigmaScaleTail (I := I) hd P L pb r x σ) :
    ∃ ψ : Nat → Nat, ∃ hψ : StrictMono ψ,
      SigmaScaleField (I := I) hd P (L.subseq hψ) pb r
        (fun gamma k => x gamma (ψ k)) σ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
  let ψ : Nat → Nat := fun k => k + N
  have hψ : StrictMono ψ := by
    intro k l hkl
    exact Nat.add_lt_add_right hkl N
  refine ⟨ψ, hψ, ?_⟩
  intro gamma k
  exact hN (ψ k) (by simp only [ψ]; omega) gamma

theorem SigmaScaleField.metricCoerciveExpRadius {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M} {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ)
    (gamma : Fin (pb.A r)) (k : Nat) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) <
      metricCoerciveExpRadius (I := I) (X.obj (L.φ k)).metric (x gamma k) := by
  let : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  let : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
  obtain ⟨hlo, hhi⟩ := hfield gamma k
  have hsc : 0 < Real.sqrt (metricCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) :=
    Real.sqrt_pos.mpr (metricCoerciveConst_pos (I := I) (X.obj (L.φ k)).metric (x gamma k))
  have h1 : 4 * L.lamInf (gamma : Nat) /
      Real.sqrt (metricCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) <
      expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k) := lt_of_lt_of_le hlo hhi
  rw [div_lt_iff₀ hsc] at h1
  exact h1.trans_eq (mul_comm _ _)

theorem NormalRadiusProfile.sigmaCenterTail
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {D : Real} (hD : 0 < D)
    (h16 : (16 : Real) < h.ratio * D)
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesDistance)
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    SigmaScaleTail (I := I) hd P L pb r
      (fun gamma k => seqCenterD hd P L k (gamma : Nat))
      (fun gamma => 8 * L.lamInf (gamma : Nat)) := by
  have hwin : ∀ᶠ n in Filter.atTop, ∀ gamma ∈ Finset.range (pb.A r),
      L.lamInf gamma / 2 ≤
        hd.lambda D (seqRadius hd D P (L.φ n) gamma) :=
    (Filter.eventually_all_finset _).mpr fun gamma _ =>
      (L.lambda_window hd hD P gamma).mono fun _ hgamma => by
        simpa only [NetLimitData.lamInf] using hgamma.1
  filter_upwards [hwin] with n hn
  intro gamma
  let : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  have : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hx : hd.dist (L.φ n) (seqCenterD hd P L n (gamma : Nat))
      (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (gamma : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n),
      ← seqCenterD_dist_eq hd P L n (gamma : Nat)]
  let : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  let : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  let : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  let : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  constructor
  · have hhalf : (1 / 2 : Real) ≤ metricCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat)) :=
      hb.half_le_metricCoerciveConst (L.φ n) (seqCenterD hd P L n (gamma : Nat))
    have hsqrt_half : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
      have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
      have hn := Real.sqrt_nonneg (1 / 2 : Real)
      nlinarith
    have hsqrt : (1 / 2 : Real) < Real.sqrt (metricCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) :=
      hsqrt_half.trans_le (Real.sqrt_le_sqrt hhalf)
    have hsc : 0 < Real.sqrt (metricCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) :=
      Real.sqrt_pos.mpr (metricCoerciveConst_pos (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat)))
    have hlam : 0 < L.lamInf (gamma : Nat) :=
      hd.lambda_pos hD (L.rInf (gamma : Nat))
    apply (div_lt_iff₀ hsc).2
    have hfour : (4 : Real) < 8 * Real.sqrt (metricCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) := by
      nlinarith
    calc
      4 * L.lamInf (gamma : Nat) <
          (8 * Real.sqrt (metricCoerciveConst (I := I)
            (X.obj (L.φ n)).metric
              (seqCenterD hd P L n (gamma : Nat)))) *
            L.lamInf (gamma : Nat) :=
        mul_lt_mul_of_pos_right hfour hlam
      _ = (8 * L.lamInf (gamma : Nat)) *
          Real.sqrt (metricCoerciveConst (I := I) (X.obj (L.φ n)).metric
            (seqCenterD hd P L n (gamma : Nat))) := by ring
  · calc
      8 * L.lamInf (gamma : Nat) =
          16 * (L.lamInf (gamma : Nat) / 2) := by ring
      _ ≤ 16 * hd.lambda D
          (seqRadius hd D P (L.φ n) (gamma : Nat)) :=
        mul_le_mul_of_nonneg_left
          (hn (gamma : Nat) (Finset.mem_range.mpr gamma.isLt)) (by norm_num)
      _ ≤ expMapC2Radius (I := I) (X.obj (L.φ n)).metric
          (seqCenterD hd P L n (gamma : Nat)) :=
        (h.mul_lambda_lt_exp (D := D) (c := 16)
          (R := seqRadius hd D P (L.φ n) (gamma : Nat)) hD h16 hx).le


end CheegerGromovCompactness
end DifferentialGeometry
