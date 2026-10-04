import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseDistanceControl
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Aligned

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open GC.MetricGeometry
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem MetricConvergenceData.eventually_pointedBallApprox
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (P : ProperMetricOn L)
    (Q : ∀ k, ProperMetricOn (X.obj (subseq k)))
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    let : MetricSpace L.M := P.alignedMetricSpace L
    let : ∀ k, MetricSpace (X.obj (subseq k)).M :=
      fun k => (Q k).alignedMetricSpace (X.obj (subseq k))
    ∀ᶠ k in atTop,
      ∃ f : PointedBallApprox (X.obj (subseq k)).basepoint L.basepoint R ε,
        ∀ x, f.toFun x = (Phi.partialDiffeomorph k).symm x.val := by
  have hcomplete : MetricComplete L := P.metric_complete L
  let : MetricSpace L.M := P.alignedMetricSpace L
  let : ∀ k, MetricSpace (X.obj (subseq k)).M :=
    fun k => (Q k).alignedMetricSpace (X.obj (subseq k))
  have hPL (x y : L.M) : riemannianEDistOf L.metric x y = ENNReal.ofReal (dist x y) :=
    P.realizes x y
  have hQX (k : ℕ) (x y : (X.obj (subseq k)).M) :
      riemannianEDistOf (X.obj (subseq k)).metric x y = ENNReal.ofReal (dist x y) :=
    (Q k).realizes x y
  have hR : 0 < R := hε.trans hεR
  let δ := ε / (4 * R + 1)
  have hden : 0 < 4 * R + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδ1 : δ < 1 := (div_lt_one hden).mpr (by linarith)
  have hbudget : δ * (4 * R + 1) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨_, N, hN⟩ := exists_pointed_inverse_distance_control C href hcomplete R hR.le δ hδ
  have hforward := Phi.eventually_image_closed_ball_subset C href hcomplete
    L.basepoint (A := R - ε) (L := 1 + δ) (by linarith) (by linarith)
  filter_upwards [eventually_ge_atTop N, hforward] with k hk hf
  have hcontrol := hN k hk
  have hball (x : BallCarrier (X.obj (subseq k)).basepoint R) :
      x.val ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint R := by
    change riemannianEDistOf _ _ _ ≤ ENNReal.ofReal R
    rw [hQX, ENNReal.ofReal_le_ofReal_iff hR.le, dist_comm]
    exact x.property
  let f : PointedBallApprox (X.obj (subseq k)).basepoint L.basepoint R ε := {
    error_pos := hε
    error_lt_radius := hεR
    toFun := fun x => (Phi.partialDiffeomorph k).symm x.val
    basepoint := by
      change (Phi.partialDiffeomorph k).symm (X.obj (subseq k)).basepoint = L.basepoint
      rw [← Phi.basepoint_map k]
      exact (Phi.partialDiffeomorph k).left_inv (Phi.base_mem k)
    distortion := by
      intro x y
      have hd := hcontrol.2 x.val (hball x) y.val (hball y)
      simp only [hPL, hQX, ← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + δ),
        ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith : 0 ≤ 1 + δ) dist_nonneg)] at hd
      have ha : dist x.val y.val ≤ 2 * R := by
        have ht := dist_triangle x.val (X.obj (subseq k)).basepoint y.val
        rw [dist_comm (X.obj (subseq k)).basepoint y.val] at ht
        linarith [x.property, y.property]
      have hb : dist ((Phi.partialDiffeomorph k).symm x.val)
          ((Phi.partialDiffeomorph k).symm y.val) ≤ 4 * R := by
        have hmul := mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ 1 + δ)
        nlinarith [mul_nonneg (sub_nonneg.mpr hδ1.le) hR.le]
      have hda := mul_le_mul_of_nonneg_left ha hδ.le
      have hdb := mul_le_mul_of_nonneg_left hb hδ.le
      apply abs_lt.mpr
      constructor <;> nlinarith [mul_nonneg hδ.le hR.le]
    coverage := by
      intro y hy
      have hyball : y ∈ riemannianClosedBallOf L.metric L.basepoint (R - ε) := by
        change riemannianEDistOf _ _ _ ≤ ENNReal.ofReal (R - ε)
        rw [hPL, ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ R - ε), dist_comm]
        exact hy
      have himage := hf.2 (mem_image_of_mem (Phi.map k) hyball)
      change riemannianEDistOf (X.obj (subseq k)).metric (Phi.map k L.basepoint)
        (Phi.map k y) ≤ ENNReal.ofReal ((1 + δ) * (R - ε)) at himage
      rw [show Phi.map k L.basepoint = (X.obj (subseq k)).basepoint from Phi.basepoint_map k, hQX,
        ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith) (by linarith))] at himage
      have hx : dist (Phi.map k y) (X.obj (subseq k)).basepoint ≤ R := by
        rw [dist_comm]
        nlinarith [mul_nonneg hδ.le hε.le]
      refine ⟨⟨Phi.map k y, hx⟩, ?_⟩
      change dist y ((Phi.partialDiffeomorph k).symm (Phi.map k y)) < ε
      have hleft : (Phi.partialDiffeomorph k).symm (Phi.map k y) = y :=
        (Phi.partialDiffeomorph k).left_inv (hf.1 hyball)
      rw [hleft, dist_self]
      exact hε }
  exact ⟨f, fun _ => rfl⟩


theorem MetricConvergenceData.pointedGHConverges
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (P : ProperMetricOn L)
    (Q : ∀ k, ProperMetricOn (X.obj (subseq k))) :
    let : MetricSpace L.M := P.alignedMetricSpace L
    let : ∀ k, MetricSpace (X.obj (subseq k)).M :=
      fun k => (Q k).alignedMetricSpace (X.obj (subseq k))
    PointedGHConverges (fun k => (X.obj (subseq k)).basepoint) L.basepoint := by
  let : MetricSpace L.M := P.alignedMetricSpace L
  let : ∀ k, MetricSpace (X.obj (subseq k)).M :=
    fun k => (Q k).alignedMetricSpace (X.obj (subseq k))
  have : ProperSpace L.M := by
    constructor
    intro x r
    have hc : @IsCompact L.M P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (letI : MetricSpace L.M := P.ms; Metric.closedBall x r) := by
      let : MetricSpace L.M := P.ms
      let : ProperSpace L.M := P.proper
      exact isCompact_closedBall x r
    rw [P.top_eq L] at hc
    exact hc
  refine ⟨inferInstance, fun R ε hε hεR => ?_⟩
  filter_upwards [C.eventually_pointedBallApprox href P Q hε hεR] with k hk
  exact ⟨hk.choose⟩

theorem MetricConvergenceData.pointedGHConverges_of_complete_connected
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconn : ConnectedSpace L.M)
    (hsource : ∀ k, MetricComplete (X.obj (subseq k)))
    (hsourceConn : ∀ k, ConnectedSpace (X.obj (subseq k)).M) :
    let : MetricSpace L.M := (properMetricOn L hcomplete hconn).alignedMetricSpace L
    let : ∀ k, MetricSpace (X.obj (subseq k)).M := fun k =>
      (properMetricOn (X.obj (subseq k)) (hsource k) (hsourceConn k)).alignedMetricSpace
        (X.obj (subseq k))
    PointedGHConverges (fun k => (X.obj (subseq k)).basepoint) L.basepoint :=
  C.pointedGHConverges href (properMetricOn L hcomplete hconn)
    (fun k => properMetricOn (X.obj (subseq k)) (hsource k) (hsourceConn k))

end DifferentialGeometry.CheegerGromovCompactness
