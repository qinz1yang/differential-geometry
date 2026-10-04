import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.PointedNormalChartMetricLaws
import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Radial

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold Metric Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open GC.MetricGeometry
namespace DifferentialGeometry.CheegerGromovCompactness
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
universe u w

theorem exists_uniform_pointed_limit_normal_charts_of_approximations
    (n K : ℕ) (hn : 2 ≤ n) {r v S A : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hS : 0 < S) (hA : 0 < A) :
    letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := ⟨by simpa using (show n ≠ 0 by omega)⟩
    letI : NormedAddCommGroup ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    ∃ (a C : ℝ) (ha : 0 < a), 0 < C ∧ 2 * a < 1 ∧
      ∀ (P : ℕ → PointedRiemannianManifold.{u} (𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))))
        (hcomplete : ∀ i, MetricComplete (P i))
        (hconn : ∀ i, letI : TopologicalSpace (P i).M := (P i).topology; ConnectedSpace (P i).M),
    letI : ∀ i, TopologicalSpace (P i).M := fun i => (P i).topology
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i).M := fun i => (P i).charted
    letI : ∀ i, IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) ∞ (P i).M := fun i => (P i).smooth
    letI : ∀ i, IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 1 (P i).M := fun i =>
      IsManifold.of_le (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (M := (P i).M) (n := ∞) (by decide)
    letI : ∀ i, SigmaCompactSpace (P i).M := fun i => (P i).sigmaCompact
    letI : ∀ i, T2Space (P i).M := fun i => (P i).t2
    letI : ∀ i, T2Space (TangentBundle 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (P i).M) :=
      fun i => (P i).t2TangentBundle
    letI : ∀ i, RiemannianBundle (fun x : (P i).M => TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x) :=
      fun i => (P i).riemBundle (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : ∀ i, (x : (P i).M) → InnerProductSpace Real (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x) :=
      fun i => (P i).riemInner (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : ∀ i, IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (fun x : (P i).M => TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x) :=
      fun i => (P i).riemBundle_cont (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : ∀ i, EMetricSpace (P i).M := fun i => (P i).emetricSpace (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : ∀ i, CompleteSpace (P i).M := fun i =>
      MetricComplete.complete (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (P i) (hcomplete i)
    letI : ∀ i, ConnectedSpace (P i).M := hconn
    letI : ∀ i, MetricSpace (P i).M := fun i =>
      HopfRinow.riemMetricSpace (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (M := (P i).M)
    let hEnorm : ∀ (i : ℕ) (x : (P i).M) (v : TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt ((P i).metric.inner x v v)) := by
      intro i x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (P i).metric x v
    ∀ (Q : ∀ i, (P i).M → (EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))),
    (∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure _ (P i).M (P i).metric
      (riemannianBallOf (P i).metric (P i).basepoint r)) →
    (∀ i, ∀ k : ℕ, k ≤ K → ∀ y ∈ riemannianBallOf (P i).metric (P i).basepoint (2 * S + r + 4),
      curvDerivNorm k (P i).metric y ≤ A) →
    ∀ (X : Type w) [MetricSpace X] [ProperSpace X] (p q : X) (R ε : ℕ → ℝ)
      (F : ∀ i, PointedBallApprox (P i).basepoint p (R i) (ε i)),
      Tendsto R atTop atTop → Tendsto ε atTop (𝓝 0) → q ∈ ball p S →
    ∃ (z : ∀ i, (P i).M)
      (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
        (EuclideanSpace ℝ (Fin n)) (P i).M ∞)
      (σ : ℕ → ℕ) (g : closedBall (0 : EuclideanSpace ℝ (Fin n)) (a / 8) → X),
      (q = p → ∀ i, z i = (P i).basepoint) ∧
      (∀ i, z i ∈ closedBall (P i).basepoint (R i) ∧ z i ∈ ball (P i).basepoint (S + 1)) ∧
      Tendsto (fun i => (F i).extendToWholeSpace (z i)) atTop (𝓝 q) ∧
      (∀ i, (Φ i).source = ball 0 (2 * a) ∧
        EqOn (Φ i) (intrinsicFramedExp (P i).metric (hEnorm i) (z i) ∘ Q i (z i))
          (ball 0 (2 * a)) ∧
        Φ i 0 = z i ∧
        ContDiffOn ℝ ∞ (pullbackMetricCoefficients (P i).metric (Φ i)) (ball 0 (2 * a)) ∧
        ContDiffOn ℝ K (fun w => Ring.inverse
          (IsCoercive.gramCLM (pullbackMetricCoefficients (P i).metric (Φ i) w)))
          (ball 0 (2 * a)) ∧
        (∀ w ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) a,
          (∀ v : EuclideanSpace ℝ (Fin n), (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
              pullbackMetricCoefficients (P i).metric (Φ i) w v v ∧
            pullbackMetricCoefficients (P i).metric (Φ i) w v v ≤ 2 * ‖v‖ ^ 2) ∧
          ∀ k : ℕ, k ≤ K →
            ‖iteratedFDeriv ℝ k (pullbackMetricCoefficients (P i).metric (Φ i)) w‖ +
              ‖iteratedFDeriv ℝ k (fun y => Ring.inverse
                (IsCoercive.gramCLM (pullbackMetricCoefficients (P i).metric (Φ i) y))) w‖ ≤ C) ∧
        LipschitzWith 2 (fun w : closedBall (0 : EuclideanSpace ℝ (Fin n)) (a / 8) => Φ i w) ∧
        AntilipschitzWith 2 (fun w : closedBall (0 : EuclideanSpace ℝ (Fin n)) (a / 8) => Φ i w) ∧
        (∀ w ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (2 * a), dist (Φ i w) (z i) = ‖w‖) ∧
        (∀ t ≤ 2 * a, (Φ i : EuclideanSpace ℝ (Fin n) → (P i).M) '' ball 0 t = ball (z i) t) ∧
        ∀ t < 2 * a,
          (Φ i : EuclideanSpace ℝ (Fin n) → (P i).M) '' closedBall 0 t = closedBall (z i) t) ∧
      StrictMono σ ∧ LipschitzWith 2 g ∧ AntilipschitzWith 2 g ∧
      g ⟨0, mem_closedBall_self (div_nonneg ha.le (by norm_num))⟩ = q ∧
      (∀ w, dist (g w) q = ‖(w : EuclideanSpace ℝ (Fin n))‖) ∧
      (∀ i (w : closedBall (0 : EuclideanSpace ℝ (Fin n)) (a / 8)),
        Φ (σ i) w ∈ closedBall (P (σ i)).basepoint (R (σ i))) ∧
      TendstoUniformly (fun i (w : closedBall (0 : EuclideanSpace ℝ (Fin n)) (a / 8)) =>
        (F (σ i)).extendToWholeSpace (Φ (σ i) w)) g atTop ∧
      ball q (a / 8) ⊆ range g ∧
      ∃ e : ball (0 : EuclideanSpace ℝ (Fin n)) (a / 16) ≃ₜ ball q (a / 16),
        (e ⟨0, mem_ball_self (div_pos ha (by norm_num))⟩ : X) = q ∧
        LipschitzWith 2 e ∧ AntilipschitzWith 2 e ∧
        ∀ w, (e w : X) = g ⟨w, closedBall_subset_closedBall (by linarith [ha])
          (ball_subset_closedBall w.property)⟩ := by
  let E := EuclideanSpace ℝ (Fin n)
  let _ : NeZero (Module.finrank ℝ E) := ⟨by simpa [E] using (show n ≠ 0 by omega)⟩
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  dsimp only
  obtain ⟨a, C, ha, hC, hsmall, hcharts⟩ :=
    exists_uniform_complete_normal_charts_with_metric_laws.{u}
      n K hn hr hv hS hA
  refine ⟨a, C, ha, hC, hsmall, ?_⟩
  intro P hcomplete hconn
  let _ : ∀ i, TopologicalSpace (P i).M := fun i => (P i).topology
  let _ : ∀ i, ChartedSpace E (P i).M := fun i => (P i).charted
  let _ : ∀ i, IsManifold 𝓘(ℝ, E) ∞ (P i).M := fun i => (P i).smooth
  let _ : ∀ i, IsManifold 𝓘(ℝ, E) 1 (P i).M := fun i =>
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := (P i).M) (n := ∞) (by decide)
  let _ : ∀ i, SigmaCompactSpace (P i).M := fun i => (P i).sigmaCompact
  let _ : ∀ i, T2Space (P i).M := fun i => (P i).t2
  let _ : ∀ i, T2Space (TangentBundle 𝓘(ℝ, E) (P i).M) := fun i => (P i).t2TangentBundle
  let _ : ∀ i, RiemannianBundle (fun x : (P i).M => TangentSpace 𝓘(ℝ, E) x) :=
    fun i => (P i).riemBundle (I := 𝓘(ℝ, E))
  let _ : ∀ i, (x : (P i).M) → InnerProductSpace Real (TangentSpace 𝓘(ℝ, E) x) :=
    fun i => (P i).riemInner (I := 𝓘(ℝ, E))
  let _ : ∀ i, IsContinuousRiemannianBundle E
      (fun x : (P i).M => TangentSpace 𝓘(ℝ, E) x) :=
    fun i => (P i).riemBundle_cont (I := 𝓘(ℝ, E))
  let _ : ∀ i, EMetricSpace (P i).M := fun i => (P i).emetricSpace (I := 𝓘(ℝ, E))
  let _ : ∀ i, CompleteSpace (P i).M := fun i =>
    MetricComplete.complete (I := 𝓘(ℝ, E)) (P i) (hcomplete i)
  let _ : ∀ i, ConnectedSpace (P i).M := hconn
  let _ : ∀ i, MetricSpace (P i).M := fun i =>
    HopfRinow.riemMetricSpace (I := 𝓘(ℝ, E)) (M := (P i).M)
  intro Q hvol hcurv X _ _ p q R ε F hR hε hq
  obtain ⟨z, hzp, hz, hzconv⟩ :=
    exists_approximating_centers p q (fun i => (P i).basepoint) F hR hε hS hq
  have hzi (i : ℕ) : z i ∈ riemannianBallOf (P i).metric (P i).basepoint (S + 1) := by
    have h1 : dist (P i).basepoint (z i) < S + 1 := by
      rw [dist_comm]
      exact (hz i).2
    have h2 : edist (P i).basepoint (z i) < ENNReal.ofReal (S + 1) := edist_lt_ofReal.mpr h1
    exact h2
  have hgeom := fun i : ℕ =>
    hcharts (P i) (hcomplete i) (hconn i) (z i) (hvol i) (hcurv i) (hzi i) (Q i (z i))
  choose Φ hsrc _ hmap hzero hsmooth hinverse hbound hlip hanti hrad hopen hclosed using hgeom
  let c (i : ℕ) : closedBall (0 : E) (a / 8) → (P i).M := fun w => Φ i w
  let w₀ : closedBall (0 : E) (a / 8) :=
    ⟨0, mem_closedBall_self (div_nonneg ha.le (by norm_num))⟩
  have hc0 (i : ℕ) : c i w₀ = z i := hzero i
  obtain ⟨σ, g, hσ, hg, hg', hg0, hmem, hconv, hcov⟩ :=
    exists_bilipschitz_chart_limit_of_approximations w₀ p q (fun i => (P i).basepoint)
      2 2 F hR hε c
      (Eventually.of_forall fun i => by
        rw [hc0]
        exact (hz i).1)
      (by
        simp only [hc0]
        exact hzconv)
      hlip hanti
  have hcoverage : ball q (a / 8) ⊆ range g := by
    apply hcov (a / 8)
    apply Eventually.of_forall
    intro i
    rw [hc0]
    intro y hy
    have hy' : y ∈ (Φ i : E → (P i).M) '' closedBall 0 (a / 8) := by
      rw [hclosed i (a / 8) (by linarith [ha])]
      exact ball_subset_closedBall hy
    obtain ⟨w, hw, heq⟩ := hy'
    exact Set.mem_range.mpr ⟨⟨w, hw⟩, heq⟩
  have hradg (w : closedBall (0 : E) (a / 8)) : dist (g w) q = ‖(w : E)‖ := by
    have hrad' : ∀ i (u : closedBall (0 : E) (a / 8)),
        dist (c (σ i) u) (c (σ i) w₀) = ‖(u : E)‖ := by
      intro i u
      rw [hc0]
      exact hrad (σ i) u (closedBall_subset_ball (by linarith [ha]) u.property)
    exact dist_eq_norm_of_radial_chart_limit w₀ p q (fun i => (P (σ i)).basepoint)
      (fun i => F (σ i)) (hε.comp hσ.tendsto_atTop) (fun i => c (σ i)) g hg0
      (Eventually.of_forall fun i => hmem i) hconv hrad' w
  refine ⟨z, Φ, σ, g, hzp, hz, hzconv, fun i => ⟨hsrc i, hmap i, hzero i, hsmooth i,
    hinverse i, hbound i, hlip i, hanti i, hrad i, hopen i, hclosed i⟩, hσ, hg, hg', hg0,
    hradg, hmem, hconv, hcoverage,
    exists_radial_ball_homeomorph ha q g hg hg' hg0 hradg hcoverage⟩

end DifferentialGeometry.CheegerGromovCompactness
