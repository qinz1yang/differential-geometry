import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.TransitionCompatibility
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Topology
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Smooth

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology
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

theorem exists_finite_pointed_buffered_smooth_transition_quotient
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
            ∃ hnear : ∀ k i j,
              (near i j = true →
                riemannianEDistOf (I := I) (X.obj (phi k)).metric (c i k) (c j k) <
                  ENNReal.ofReal (ρ / 4)) ∧
              (near i j = false → ENNReal.ofReal (ρ / 4) ≤
                riemannianEDistOf (I := I) (X.obj (phi k)).metric (c i k) (c j k)),
            (∀ k i j, near i j = false →
              Disjoint ((charts i k).hom '' Metric.ball (0 : E) (ρ / 10))
                ((charts j k).hom '' Metric.ball (0 : E) (ρ / 10))) ∧
            ∃ Jinf Jbarinf : {a : Fin (N + 1) × Fin (N + 1) // near a.1 a.2 = true} → E → E,
              ∃ htrans : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (Jinf a) (Metric.ball (0 : E) (ρ / 2)) ∧
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
                      (gInf a.1.2 (Jinf a z), fderiv ℝ (Jinf a) z)),
              let hclass : ∀ i j, ∀ᶠ k in atTop,
                  (near i j = true → edist (c i k) (c j k) < ENNReal.ofReal (ρ / 4)) ∧
                  (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (c i k) (c j k)) := by
                intro i j
                exact Filter.Eventually.of_forall fun k => hnear k i j
              let hcont := fun a => (htrans a).1.continuousOn
              let hconv := fun a => (htrans a).2.2.1
              let U : TopologicalSpace.Opens E := ⟨Metric.ball 0 (ρ / 8), Metric.isOpen_ball⟩
              let D := IntrinsicBallChart.finiteBufferedTransitionGlueData
                (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k))
                c hρ charts near hclass Jinf hcont hconv
              let p := IntrinsicBallChart.bufferedTransitionGlueBasepoint
                (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k))
                c hρ charts near hclass Jinf hcont hconv
              let V := IntrinsicBallChart.transitionGlueCore
                (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k))
                (fun i : ULift.{uE} (Fin (N + 1)) => c i.down) hρ
                (fun i k => charts i.down k) (fun i j => near i.down j.down)
                (fun i j => hclass i.down j.down)
                (fun a => Jinf ⟨(a.1.1.down, a.1.2.down), a.2⟩)
                (fun a => hcont ⟨(a.1.1.down, a.1.2.down), a.2⟩)
                (fun a => hconv ⟨(a.1.1.down, a.1.2.down), a.2⟩)
              let K := IntrinsicBallChart.transitionGlueCompactCore
                (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k))
                (fun i : ULift.{uE} (Fin (N + 1)) => c i.down) hρ
                (fun i k => charts i.down k) (fun i j => near i.down j.down)
                (fun i j => hclass i.down j.down)
                (fun a => Jinf ⟨(a.1.1.down, a.1.2.down), a.2⟩)
                (fun a => hcont ⟨(a.1.1.down, a.1.2.down), a.2⟩)
                (fun a => hconv ⟨(a.1.1.down, a.1.2.down), a.2⟩)
              IsOpen V ∧ IsCompact K ∧ V ⊆ K ∧ IsCompact (closure V) ∧ p ∈ V ∧
              T2Space D.toGlueData.glued ∧ SecondCountableTopology D.toGlueData.glued ∧
              (p = D.toGlueData.ι (ULift.up 0) ⟨0, Metric.mem_ball_self (by positivity)⟩) ∧
              (∀ k, (charts 0 k).hom 0 = (X.obj (phi k)).basepoint) ∧
              ∃ C : ChartedSpace E D.toGlueData.glued, letI := C
                IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued ∧
                ∀ i : ULift.{uE} (Fin (N + 1)),
                  IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
                    (fun z : U => D.toGlueData.ι i z) := by
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
    exists_finite_pointed_covering_intrinsicBallChart_buffered_compatible_metric_transition_limits
      X hcomplete hconn hr hrR hη hjets hinj
  refine ⟨ρ, hρ, hρR, N, phi, hphi, c, charts, gInf, hbase, hc, hcover, hell, hmetric,
    near, hnear, hfar, Jinf, Jbarinf, htrans, ?_⟩
  dsimp only
  refine ⟨IntrinsicBallChart.isOpen_transitionGlueCore _ _ _ _ _ _ _ _ _ _,
    IntrinsicBallChart.isCompact_transitionGlueCompactCore _ _ _ _ _ _ _ _ _ _,
    IntrinsicBallChart.transitionGlueCore_subset_compactCore _ _ _ _ _ _ _ _ _ _,
    IntrinsicBallChart.isCompact_closure_transitionGlueCore _ _ _ _ _ _ _ _ _ _,
    IntrinsicBallChart.zero_mem_transitionGlueCore _ _ _ _ _ _ _ _ _ _ (ULift.up 0),
    IntrinsicBallChart.finiteBufferedTransitionGlueData_t2Space _ _ _ _ _ _ _ _ _ _,
    IntrinsicBallChart.finiteBufferedTransitionGlueData_secondCountableTopology _ _ _ _ _ _ _ _ _ _,
    rfl, ?_, ?_⟩
  · exact IntrinsicBallChart.pointed_intrinsic_chart_zero
      (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k)) c hρ charts
      (fun k => (X.obj (phi k)).basepoint) hbase
  · unfold IntrinsicBallChart.finiteBufferedTransitionGlueData
    exact IntrinsicBallChart.exists_smooth_atlas_bufferedTransitionGlueData
      _ _ _ _ _ _ _ _ _ _ (fun a => (htrans ⟨(a.1.1.down, a.1.2.down), a.2⟩).1)

end DifferentialGeometry.CheegerGromovCompactness

end

end
