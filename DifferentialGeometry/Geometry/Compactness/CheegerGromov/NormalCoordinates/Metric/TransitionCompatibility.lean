import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart
import DifferentialGeometry.Analysis.Calculus.MapConvergence.LimitIdentities
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.FiniteLimits
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChartMetric
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.PointedLimits

section

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Filter Topology
open scoped Manifold ContDiff
open CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)]

theorem metric_limit_eq_pullbackForm
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    {p q : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k))
    (d : ∀ k, NormalBallChart (I := I) (q k))
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {gc gd : E → E →L[Real] E →L[Real] Real} {J : E → E}
    (hc : MapCInfConvergenceOnCompacts U (fun k => (c k).metric (g k)) gc)
    (hd : MapCInfConvergenceOnCompacts V (fun k => (d k).metric (g k)) gd)
    (hJ : MapCInfConvergenceOnCompacts U (fun k => (c k).transition (d k)) J)
    (hJsmooth : ContDiffOn Real ∞ J U) (hgd : ContinuousOn gd V)
    (hovl : ∀ k, (c k).OverlapOn (d k) U)
    {z : E} (hz : z ∈ U) (hJz : J z ∈ V) :
    gc z = pullbackForm (gd (J z), fderiv Real J z) := by
  apply eq_pullbackForm_of_mapCInfConvergenceOnCompacts hU hV hc hd hJ
    (fun k => (c k).transition_smooth (d k) (hovl k)) hJsmooth hgd ?_ hz hJz
  exact Eventually.of_forall fun k z hz _ u v =>
    ((c k).transition_isom (g k) (d k) (hovl k) hz u v).symm

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart


end

section

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Bundle Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)]
  [∀ k, SigmaCompactSpace (M k)] [∀ k, T2Space (TangentBundle I (M k))]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.metric_limit_eq_pullbackForm_of_near_centers
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (p q : ∀ k, M k) {ρ : ℝ} (hρ : 0 < ρ)
    (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) ρ)
    (d : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (q k) ρ)
    (hnear : ∀ k, edist (p k) (q k) < ENNReal.ofReal (ρ / 4))
    {gc gd : E → E →L[ℝ] E →L[ℝ] ℝ} {J : E → E}
    (hc : CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
      (fun k => intrinsicFrameMetric (I := I) (g k) (hEnorm k) (p k)) gc)
    (hd : CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
      (fun k => intrinsicFrameMetric (I := I) (g k) (hEnorm k) (q k)) gd)
    (hJ : CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball 0 (ρ / 2))
      (fun k => ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hρ).transition
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hρ)) J)
    (hJsmooth : ContDiffOn ℝ ∞ J (Metric.ball 0 (ρ / 2)))
    (hgd : ContinuousOn gd (Metric.ball 0 ρ))
    {z : E} (hz : z ∈ Metric.ball 0 (ρ / 2)) (hJz : J z ∈ Metric.ball 0 ρ) :
    gc z = CheegerGromovCompactness.pullbackForm (gd (J z), fderiv ℝ J z) := by
  let cn : ∀ k, NormalBallChart (I := I) (p k) :=
    fun k => (c k).toNormalBallChart (g k) (hEnorm k) (p k) hρ
  let dn : ∀ k, NormalBallChart (I := I) (q k) :=
    fun k => (d k).toNormalBallChart (g k) (hEnorm k) (q k) hρ
  have hhalf : ρ / 2 ≤ ρ := by linarith
  have hc' : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Metric.ball 0 (ρ / 2)) (fun k => (cn k).metric (g k)) gc := by
    have hcr : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
        (Metric.ball 0 (ρ / 2))
        (fun k => intrinsicFrameMetric (I := I) (g k) (hEnorm k) (p k)) gc :=
      fun A hA hsub => hc A hA (hsub.trans (Metric.ball_subset_ball hhalf))
    apply hcr.congr Metric.isOpen_ball _ (fun _ _ => rfl)
    intro k x hx
    exact ((c k).metric_eq_intrinsicFrameMetric (g k) (hEnorm k) (p k) hρ
      (Metric.ball_subset_ball hhalf hx))
  have hd' : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Metric.ball 0 ρ) (fun k => (dn k).metric (g k)) gd := by
    apply hd.congr Metric.isOpen_ball _ (fun _ _ => rfl)
    intro k x hx
    exact ((d k).metric_eq_intrinsicFrameMetric (g k) (hEnorm k) (q k) hρ hx)
  have hovl : ∀ k, (cn k).OverlapOn (dn k) (Metric.ball 0 (ρ / 2)) := by
    intro k
    apply (c k).overlap_on_ball_of_edist_add_le (g k) (hEnorm k) (p k) (q k)
      (d k) hρ hρ hhalf
    calc
      edist (p k) (q k) + ENNReal.ofReal (ρ / 2) ≤
          ENNReal.ofReal (ρ / 4) + ENNReal.ofReal (ρ / 2) :=
        add_le_add (hnear k).le le_rfl
      _ = ENNReal.ofReal (ρ / 4 + ρ / 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (by linarith)
  exact NormalBallChart.metric_limit_eq_pullbackForm g cn dn Metric.isOpen_ball
    Metric.isOpen_ball hc' hd' hJ hJsmooth hgd hovl hz hJz

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_finite_pointed_covering_intrinsicBallChart_buffered_compatible_metric_transition_limits
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
      riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η) :
    letI : ∀ k, RiemannianBundle (fun x : (X.obj k).M => TangentSpace I x) :=
      fun k => (X.obj k).riemBundle (I := I)
    letI : ∀ k, (x : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I x) :=
      fun k => (X.obj k).riemInner (I := I)
    letI : ∀ k, IsContinuousRiemannianBundle E
        (fun x : (X.obj k).M => TangentSpace I x) :=
      fun k => (X.obj k).riemBundle_cont (I := I)
    letI : ∀ k, EMetricSpace (X.obj k).M := fun k => (X.obj k).emetricSpace (I := I)
    letI : ∀ k, IsRiemannianManifold I (X.obj k).M := fun _ => ⟨fun _ _ => rfl⟩
    letI : ∀ k, CompleteSpace (X.obj k).M :=
      fun k => MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    let hEnorm : ∀ k (x : (X.obj k).M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner x v v)) := by
      intro k x v
      with_unfolding_all
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (X.obj k).metric x v
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ R - r ∧ ∃ N : ℕ,
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        ∃ (c : Fin (N + 1) → ∀ k, (X.obj (phi k)).M)
          (charts : ∀ i k, IntrinsicBallChart (I := I) (X.obj (phi k)).metric
            (hEnorm (phi k)) (c i k) ρ)
          (gInf : Fin (N + 1) → E → E →L[ℝ] E →L[ℝ] ℝ),
          (∀ k, c 0 k = (X.obj (phi k)).basepoint) ∧
          (∀ i k, riemannianEDistOf (I := I) (X.obj (phi k)).metric
            (X.obj (phi k)).basepoint (c i k) ≤ ENNReal.ofReal r) ∧
          (∀ k, ∀ y : (X.obj (phi k)).M,
            riemannianEDistOf (I := I) (X.obj (phi k)).metric
              (X.obj (phi k)).basepoint y ≤ ENNReal.ofReal r →
            ∃ i, y ∈ (charts i k).hom '' Metric.ball (0 : E) (ρ / 10)) ∧
          (∀ i k, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
            (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I)
                (X.obj (phi k)).metric (hEnorm (phi k)) (c i k) z v v ∧
              intrinsicFrameMetric (I := I) (X.obj (phi k)).metric
                (hEnorm (phi k)) (c i k) z v v ≤ 2 * ‖v‖ ^ 2) ∧
          (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (gInf i) (Metric.ball 0 ρ) ∧
            MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
              (fun k => intrinsicFrameMetric (I := I) (X.obj (phi k)).metric
                (hEnorm (phi k)) (c i k)) (gInf i) ∧
            (∀ z ∈ Metric.ball 0 ρ, ∀ v w, gInf i z v w = gInf i z w v) ∧
            (∀ z ∈ Metric.ball 0 ρ, ∀ v,
              (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gInf i z v v ∧
                gInf i z v v ≤ 2 * ‖v‖ ^ 2)) ∧
          ∃ near : Fin (N + 1) → Fin (N + 1) → Bool,
            (∀ k i j,
              (near i j = true →
                riemannianEDistOf (I := I) (X.obj (phi k)).metric (c i k) (c j k) <
                  ENNReal.ofReal (ρ / 4)) ∧
              (near i j = false → ENNReal.ofReal (ρ / 4) ≤
                riemannianEDistOf (I := I) (X.obj (phi k)).metric (c i k) (c j k))) ∧
            (∀ k i j, near i j = false →
              Disjoint ((charts i k).hom '' Metric.ball (0 : E) (ρ / 10))
                ((charts j k).hom '' Metric.ball (0 : E) (ρ / 10))) ∧
            ∃ Jinf Jbarinf : {a : Fin (N + 1) × Fin (N + 1) // near a.1 a.2 = true} → E → E,
              ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (Jinf a) (Metric.ball (0 : E) (ρ / 2)) ∧
                ContDiffOn ℝ (⊤ : ℕ∞) (Jbarinf a) (Metric.ball (0 : E) (ρ / 2)) ∧
                MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
                  (fun k => ((charts a.1.1 k).toNormalBallChart
                    (X.obj (phi k)).metric (hEnorm (phi k)) (c a.1.1 k) hρ).transition
                    ((charts a.1.2 k).toNormalBallChart
                      (X.obj (phi k)).metric (hEnorm (phi k)) (c a.1.2 k) hρ)) (Jinf a) ∧
                MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
                  (fun k => ((charts a.1.2 k).toNormalBallChart
                    (X.obj (phi k)).metric (hEnorm (phi k)) (c a.1.2 k) hρ).transition
                    ((charts a.1.1 k).toNormalBallChart
                      (X.obj (phi k)).metric (hEnorm (phi k)) (c a.1.1 k) hρ)) (Jbarinf a) ∧
                (∀ z ∈ Metric.ball (0 : E) (ρ / 2),
                  Jinf a z ∈ Metric.ball (0 : E) (ρ / 2) → Jbarinf a (Jinf a z) = z) ∧
                (∀ z ∈ Metric.ball (0 : E) (ρ / 2),
                  Jbarinf a z ∈ Metric.ball (0 : E) (ρ / 2) → Jinf a (Jbarinf a z) = z) ∧
                (∀ z ∈ Metric.ball (0 : E) (ρ / 2),
                  Jinf a z ∈ Metric.ball (0 : E) ρ →
                    gInf a.1.1 z = pullbackForm
                      (gInf a.1.2 (Jinf a z), fderiv ℝ (Jinf a) z)) := by
  classical
  let : ∀ k, RiemannianBundle (fun x : (X.obj k).M => TangentSpace I x) :=
    fun k => (X.obj k).riemBundle (I := I)
  let : ∀ k, (x : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I x) :=
    fun k => (X.obj k).riemInner (I := I)
  let : ∀ k, IsContinuousRiemannianBundle E
      (fun x : (X.obj k).M => TangentSpace I x) :=
    fun k => (X.obj k).riemBundle_cont (I := I)
  let : ∀ k, EMetricSpace (X.obj k).M := fun k => (X.obj k).emetricSpace (I := I)
  let : ∀ k, IsRiemannianManifold I (X.obj k).M := fun _ => ⟨fun _ _ => rfl⟩
  let : ∀ k, CompleteSpace (X.obj k).M :=
    fun k => MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  intro hEnorm
  obtain ⟨ρ, hρ, hρR, N, phi, hphi, c, charts, gInf, hbase, hc, hcover, hell, hmetric,
    near, hnear, hfar, Jinf, Jbarinf, htrans⟩ :=
    exists_finite_pointed_covering_intrinsicBallChart_metric_transition_limit_subsequence
      X hcomplete hconn hr hrR hη hjets hinj
  refine ⟨ρ, hρ, hρR, N, phi, hphi, c, charts, gInf, hbase, hc, hcover, hell, hmetric,
    near, hnear, hfar, Jinf, Jbarinf, ?_⟩
  intro a
  obtain ⟨hJs, hJbars, hJconv, hJbarconv, hinv, hbarinv⟩ := htrans a
  refine ⟨hJs, hJbars, hJconv, hJbarconv, hinv, hbarinv, ?_⟩
  intro z hz hJz
  have hneari : ∀ k, edist (c a.1.1 k) (c a.1.2 k) < ENNReal.ofReal (ρ / 4) := by
    intro k
    simpa only [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I)
      (X.obj (phi k))] using (hnear k a.1.1 a.1.2).1 a.2
  exact IntrinsicBallChart.metric_limit_eq_pullbackForm_of_near_centers
    (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k))
    (c a.1.1) (c a.1.2) hρ (charts a.1.1) (charts a.1.2) hneari
    (hmetric a.1.1).2.1 (hmetric a.1.2).2.1 hJconv hJs
    (hmetric a.1.2).1.continuousOn
    hz hJz

end DifferentialGeometry.CheegerGromovCompactness

end

end
