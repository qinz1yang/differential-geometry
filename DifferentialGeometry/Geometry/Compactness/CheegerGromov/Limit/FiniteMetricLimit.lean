import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.CountablePointedNormalCharts
import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Atlas
import DifferentialGeometry.Geometry.Metric.Convergence.NormalChartRealization

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold Metric Filter Topology
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

private theorem tendstoUniformly_comp_strictMono {α β : Type*} [UniformSpace β]
    {F : ℕ → α → β} {f : α → β} (h : TendstoUniformly F f atTop)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    TendstoUniformly (fun i => F (σ i)) f atTop :=
  fun u hu => hσ.tendsto_atTop.eventually (h u hu)

private theorem tendstoUniformlyOn_ball_of_closedBall
    {E X : Type*} [NormedAddCommGroup E] [MetricSpace X]
    {ρ δ : ℝ} (hρδ : ρ ≤ δ) {G : ℕ → E → X} {g : closedBall (0 : E) δ → X} {f : E → X}
    (hconv : TendstoUniformly (fun i (u : closedBall (0 : E) δ) => G i u) g atTop)
    (hf : ∀ u : ball (0 : E) ρ, f u = g ⟨u,
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hρδ)) u.property⟩) :
    TendstoUniformlyOn G f atTop (ball 0 ρ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [Metric.tendstoUniformly_iff.mp hconv η hη] with i hi
  intro u hu
  have h := hi ⟨u, (ball_subset_closedBall.trans (closedBall_subset_closedBall hρδ)) hu⟩
  have hfu : f u = g ⟨u, (ball_subset_closedBall.trans (closedBall_subset_closedBall hρδ)) hu⟩ :=
    hf ⟨u, hu⟩
  rw [hfu]
  exact h

private theorem exists_limit_atlas_of_normal_chart_limits
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace X] [Countable ι]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (K : ℕ) (hK : 1 ≤ K) (p : X) (o : ∀ i, Y i) {R ε : ℕ → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i)) (hε : Tendsto ε atTop (𝓝 0))
    (g : ∀ i, DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    (a C : ι → ℝ) (ha : ∀ j, 0 < a j)
    (Φ : ι → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞) (z : ι → ∀ i, Y i)
    (hΦs : ∀ j i, (Φ j i).source = ball 0 (2 * a j)) (hΦ0 : ∀ j i, Φ j i 0 = z j i)
    (hrad : ∀ j i, ∀ w ∈ ball (0 : E) (2 * a j), dist (Φ j i w) (z j i) = ‖w‖)
    (himage : ∀ j i, ∀ t ≤ 2 * a j, (Φ j i : E → Y i) '' ball 0 t = ball (z j i) t)
    (hell : ∀ j i, ∀ w ∈ closedBall (0 : E) (a j), ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients (g i) (Φ j i) w v v ∧
        pullbackMetricCoefficients (g i) (Φ j i) w v v ≤ 2 * ‖v‖ ^ 2)
    (hjets : ∀ j i, ∀ w ∈ closedBall (0 : E) (a j), ∀ k : ℕ, k ≤ K →
      ‖iteratedFDeriv ℝ k (pullbackMetricCoefficients (g i) (Φ j i)) w‖ ≤ C j)
    (gl : ∀ j, closedBall (0 : E) (a j / 8) → X)
    (hmem : ∀ j, ∀ᶠ i in atTop, ∀ u : closedBall (0 : E) (a j / 8),
      Φ j i u ∈ closedBall (o i) (R i))
    (hconv : ∀ j, TendstoUniformly (fun i (u : closedBall (0 : E) (a j / 8)) =>
      (F i).extendToWholeSpace (Φ j i u)) (gl j) atTop)
    (ψ : ι → OpenPartialHomeomorph E X) (q : ι → X)
    (hψs : ∀ j, (ψ j).source = ball 0 (a j / 16))
    (hψt : ∀ j, (ψ j).target = ball (q j) (a j / 16)) (hψ0 : ∀ j, ψ j 0 = q j)
    (hcover : ∀ x, ∃ j, x ∈ (ψ j).target)
    (hψanti : ∀ j, AntilipschitzWith 2 (fun u : ball (0 : E) (a j / 16) => ψ j u))
    (hψmap : ∀ j, ∀ u : ball (0 : E) (a j / 16), ψ j u = gl j ⟨u, (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith [ha j]))) u.property⟩) :
    ∃ (σ : ℕ → ℕ) (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ), StrictMono σ ∧
      (∀ j, ContDiffOn ℝ (K - 1 : ℕ) (b j) (ball 0 (a j)) ∧
        (∀ u ∈ ball (0 : E) (a j), ∀ v w : E, b j u v w = b j u w v) ∧
        (∀ u ∈ ball (0 : E) (a j), ∀ v : E,
          (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ b j u v v ∧ b j u v v ≤ 2 * ‖v‖ ^ 2) ∧
        ∀ D : Set E, IsCompact D → D ⊆ ball 0 (a j) →
          MapCPConvergenceOn D (K - 1)
            (fun i => pullbackMetricCoefficients (g (σ i)) (Φ j (σ i))) (b j)) ∧
      (∀ j d, ContDiffOn ℝ K ((ψ j).trans (ψ d).symm) ((ψ j).trans (ψ d).symm).source ∧
        ∀ S : Set E, IsCompact S → S ⊆ ((ψ j).trans (ψ d).symm).source →
          MapCPConvergenceOn S K (fun i u => (Φ d (σ i)).symm (Φ j (σ i) u))
            ((ψ j).trans (ψ d).symm) ∧
          ∃ s : ℝ, 0 < s ∧ s < a d / 16 ∧ ∀ᶠ i in atTop,
            S ⊆ ((Φ j (σ i)).trans (Φ d (σ i)).symm).source ∧
            MapsTo (fun u => (Φ d (σ i)).symm (Φ j (σ i) u)) S (closedBall 0 s)) ∧
      (∀ j d u, u ∈ ((ψ j).symm.symm.trans (ψ d).symm).source →
        b j u = (b d (((ψ j).symm.symm.trans (ψ d).symm) u)).bilinearComp
          (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u)
          (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u)) ∧
      (∀ j d, ContDiffOn ℝ ((K - 1 + 1 : ℕ) : ℕ∞ω) ((ψ j).symm.symm.trans (ψ d).symm)
        ((ψ j).symm.symm.trans (ψ d).symm).source) ∧
      (letI := DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover
        (fun j => (ψ j).symm) hcover
       IsManifold 𝓘(ℝ, E) K X) := by
  have hdom (j : ι) : ∀ᶠ i in atTop, ∀ u ∈ ball (0 : E) (a j / 16),
      Φ j i u ∈ closedBall (o i) (R i) := by
    filter_upwards [hmem j] with i hi u hu
    exact hi ⟨u, (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith [ha j]))) hu⟩
  have hlim (j : ι) : TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (Φ j i u))
      (ψ j) atTop (ball 0 (a j / 16)) :=
    tendstoUniformlyOn_ball_of_closedBall (by linarith [ha j])
      (G := fun i u => (F i).extendToWholeSpace (Φ j i u)) (hconv j) (hψmap j)
  have hρ (j : ι) : 0 < a j / 16 := div_pos (ha j) (by norm_num)
  have hρr (j : ι) : a j / 16 ≤ 2 * a j := by linarith [ha j]
  have hρV (j : ι) : ball (0 : E) (a j / 16) ⊆ ball 0 (a j) :=
    ball_subset_ball (by linarith [ha j])
  have hVr (j : ι) : ball (0 : E) (a j) ⊆ ball 0 (2 * a j) :=
    ball_subset_ball (by linarith [ha j])
  have hell' (j : ι) : ∀ᶠ i in atTop, ∀ u ∈ ball (0 : E) (a j), ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients (g i) (Φ j i) u v v ∧
        pullbackMetricCoefficients (g i) (Φ j i) u v v ≤ 2 * ‖v‖ ^ 2 :=
    Eventually.of_forall fun i u hu => hell j i u (ball_subset_closedBall hu)
  have hjets' (j : ι) : ∀ᶠ i in atTop, ∀ k : ℕ, k ≤ K → ∀ u ∈ ball (0 : E) (a j),
      ‖iteratedFDeriv ℝ k (pullbackMetricCoefficients (g i) (Φ j i)) u‖ ≤ C j :=
    Eventually.of_forall fun i k hk u hu => hjets j i u (ball_subset_closedBall hu) k hk
  exact exists_limit_atlas_of_pointed_chart_limits K hK p o F hε g Φ z (fun j => 2 * a j)
    hΦs hΦ0 hrad himage ψ q (fun j => a j / 16) hρ hρr hψs hψt hψ0 hcover (fun _ => 2)
    hψanti hdom hlim (fun j => ball 0 (a j)) (fun _ => isOpen_ball) hρV hVr C hell' hjets'

theorem exists_finite_metric_limit_of_approximations
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R) :
    letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := ⟨by simpa using (show n ≠ 0 by omega)⟩
    letI : NormedAddCommGroup ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    ∃ (a C : ℕ → ℝ) (ha : ∀ t, 0 < a t), (∀ t, 0 < C t ∧ 2 * a t < 1) ∧
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
    (∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (P i).metric (P i).basepoint R,
      curvDerivNorm k (P i).metric y ≤ A R) →
    ∀ (X : Type w) [MetricSpace X] [ProperSpace X],
    (∀ x y : X, Metric.intrinsicEDist x y = edist x y) →
    ∀ (p : X) (R ε : ℕ → ℝ) (F : ∀ i, PointedBallApprox (P i).basepoint p (R i) (ε i)),
      Tendsto R atTop atTop → Tendsto ε atTop (𝓝 0) →
    ∃ (q : Option (ℕ × ℕ) → X) (z : Option (ℕ × ℕ) → ∀ i, (P i).M)
      (Φ : Option (ℕ × ℕ) → ∀ i, PartialDiffeomorph 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n)) (P i).M ∞)
      (τ : ℕ → ℕ)
      (g : ∀ j : Option (ℕ × ℕ),
        closedBall (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst) / 8) → X)
      (ψ : Option (ℕ × ℕ) → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) X)
      (hcover : ∀ x, ∃ j : Option (ℕ × ℕ), x ∈ (ψ j).target)
      (b : Option (ℕ × ℕ) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      q none = p ∧ (∀ i, Φ none i 0 = (P i).basepoint) ∧ StrictMono τ ∧
      (⋃ j : Option (ℕ × ℕ), ball (q j) (a (j.elim 0 Prod.fst) / 64)) = univ ∧
      (∀ j : Option (ℕ × ℕ),
        q j ∈ ball p (((j.elim 0 Prod.fst : ℕ) : ℝ) + 1) ∧
        (q j = p → ∀ i, z j i = (P i).basepoint) ∧
        (∀ i, z j i ∈ closedBall (P i).basepoint (R i) ∧
          z j i ∈ ball (P i).basepoint (((j.elim 0 Prod.fst : ℕ) : ℝ) + 2)) ∧
        Tendsto (fun i => (F i).extendToWholeSpace (z j i)) atTop (𝓝 (q j)) ∧
        (∀ i, (Φ j i).source = ball 0 (2 * a (j.elim 0 Prod.fst)) ∧
          EqOn (Φ j i) (intrinsicFramedExp (P i).metric (hEnorm i) (z j i) ∘ Q i (z j i))
            (ball 0 (2 * a (j.elim 0 Prod.fst))) ∧
          Φ j i 0 = z j i ∧
          ContDiffOn ℝ ∞ (pullbackMetricCoefficients (P i).metric (Φ j i))
            (ball 0 (2 * a (j.elim 0 Prod.fst))) ∧
          ContDiffOn ℝ K (fun w => Ring.inverse
            (IsCoercive.gramCLM (pullbackMetricCoefficients (P i).metric (Φ j i) w)))
            (ball 0 (2 * a (j.elim 0 Prod.fst))) ∧
          (∀ w ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst)),
            (∀ v : EuclideanSpace ℝ (Fin n), (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
                pullbackMetricCoefficients (P i).metric (Φ j i) w v v ∧
              pullbackMetricCoefficients (P i).metric (Φ j i) w v v ≤ 2 * ‖v‖ ^ 2) ∧
            ∀ k : ℕ, k ≤ K →
              ‖iteratedFDeriv ℝ k (pullbackMetricCoefficients (P i).metric (Φ j i)) w‖ +
                ‖iteratedFDeriv ℝ k (fun y => Ring.inverse
                  (IsCoercive.gramCLM (pullbackMetricCoefficients (P i).metric (Φ j i) y))) w‖ ≤
                C (j.elim 0 Prod.fst)) ∧
          LipschitzWith 2 (fun w : closedBall (0 : EuclideanSpace ℝ (Fin n))
            (a (j.elim 0 Prod.fst) / 8) => Φ j i w) ∧
          AntilipschitzWith 2 (fun w : closedBall (0 : EuclideanSpace ℝ (Fin n))
            (a (j.elim 0 Prod.fst) / 8) => Φ j i w) ∧
          (∀ w ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (2 * a (j.elim 0 Prod.fst)),
            dist (Φ j i w) (z j i) = ‖w‖) ∧
          (∀ t ≤ 2 * a (j.elim 0 Prod.fst),
            (Φ j i : EuclideanSpace ℝ (Fin n) → (P i).M) '' ball 0 t = ball (z j i) t) ∧
          ∀ t < 2 * a (j.elim 0 Prod.fst),
            (Φ j i : EuclideanSpace ℝ (Fin n) → (P i).M) '' closedBall 0 t =
              closedBall (z j i) t) ∧
        LipschitzWith 2 (g j) ∧ AntilipschitzWith 2 (g j) ∧
        g j ⟨0, mem_closedBall_self (div_nonneg (ha (j.elim 0 Prod.fst)).le (by norm_num))⟩ =
          q j ∧
        (∀ u, dist (g j u) (q j) = ‖(u : EuclideanSpace ℝ (Fin n))‖) ∧
        (∀ᶠ i in atTop, ∀ u : closedBall (0 : EuclideanSpace ℝ (Fin n))
            (a (j.elim 0 Prod.fst) / 8),
          Φ j (τ i) u ∈ closedBall (P (τ i)).basepoint (R (τ i))) ∧
        TendstoUniformly (fun i (u : closedBall (0 : EuclideanSpace ℝ (Fin n))
            (a (j.elim 0 Prod.fst) / 8)) =>
          (F (τ i)).extendToWholeSpace (Φ j (τ i) u)) (g j) atTop ∧
        ball (q j) (a (j.elim 0 Prod.fst) / 8) ⊆ range (g j) ∧
        (ψ j).source = ball 0 (a (j.elim 0 Prod.fst) / 16) ∧
        (ψ j).target = ball (q j) (a (j.elim 0 Prod.fst) / 16) ∧ ψ j 0 = q j ∧
        LipschitzWith 2 (fun u : ball (0 : EuclideanSpace ℝ (Fin n))
          (a (j.elim 0 Prod.fst) / 16) => ψ j u) ∧
        AntilipschitzWith 2 (fun u : ball (0 : EuclideanSpace ℝ (Fin n))
          (a (j.elim 0 Prod.fst) / 16) => ψ j u) ∧
        ∀ u : ball (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst) / 16),
          ψ j u = g j ⟨u, (ball_subset_closedBall.trans
            (closedBall_subset_closedBall (by linarith [ha (j.elim 0 Prod.fst)]))) u.property⟩) ∧
      (∀ j : Option (ℕ × ℕ),
        ContDiffOn ℝ (K - 1 : ℕ) (b j) (ball 0 (a (j.elim 0 Prod.fst))) ∧
        (∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst)),
          ∀ v w : EuclideanSpace ℝ (Fin n), b j u v w = b j u w v) ∧
        (∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst)),
          ∀ v : EuclideanSpace ℝ (Fin n),
            (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ b j u v v ∧ b j u v v ≤ 2 * ‖v‖ ^ 2) ∧
        ∀ D : Set (EuclideanSpace ℝ (Fin n)), IsCompact D →
          D ⊆ ball 0 (a (j.elim 0 Prod.fst)) →
          MapCPConvergenceOn D (K - 1)
            (fun i => pullbackMetricCoefficients (P (τ i)).metric (Φ j (τ i))) (b j)) ∧
      (∀ j d : Option (ℕ × ℕ),
        ContDiffOn ℝ K ((ψ j).trans (ψ d).symm) ((ψ j).trans (ψ d).symm).source ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          S ⊆ ((ψ j).trans (ψ d).symm).source →
          MapCPConvergenceOn S K (fun i u => (Φ d (τ i)).symm (Φ j (τ i) u))
            ((ψ j).trans (ψ d).symm) ∧
          ∃ s : ℝ, 0 < s ∧ s < a (d.elim 0 Prod.fst) / 16 ∧ ∀ᶠ i in atTop,
            S ⊆ ((Φ j (τ i)).trans (Φ d (τ i)).symm).source ∧
            MapsTo (fun u => (Φ d (τ i)).symm (Φ j (τ i) u)) S (closedBall 0 s)) ∧
      (∀ (j d : Option (ℕ × ℕ)) (u : EuclideanSpace ℝ (Fin n)),
        u ∈ ((ψ j).symm.symm.trans (ψ d).symm).source →
        b j u = (b d (((ψ j).symm.symm.trans (ψ d).symm) u)).bilinearComp
          (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u)
          (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u)) ∧
      (∀ j d : Option (ℕ × ℕ),
        ContDiffOn ℝ ((K - 1 + 1 : ℕ) : ℕ∞ω) ((ψ j).symm.symm.trans (ψ d).symm)
          ((ψ j).symm.symm.trans (ψ d).symm).source) ∧
      (letI := DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover
        (fun j => (ψ j).symm) hcover
       ∃ hM : IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) K X,
         letI := hM
         letI : IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 1 X :=
           IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast hK)
         ∃! G : ContMDiffRiemannianMetric 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) ((K - 1 : ℕ) : ℕ∞ω)
             (EuclideanSpace ℝ (Fin n))
             (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) : X → Type _),
           (∀ j x, x ∈ (ψ j).symm.source → ∀ v w : EuclideanSpace ℝ (Fin n),
             G.inner x v w = b j ((ψ j).symm x)
               (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                 (ψ j).symm x v)
               (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                 (ψ j).symm x w)) ∧
           (letI : RiemannianBundle
               (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) : X → Type _) :=
             ⟨G.toRiemannianMetric⟩
            IsRiemannianManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) X)) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let _ : NeZero (Module.finrank ℝ E) := ⟨by simpa [E] using (show n ≠ 0 by omega)⟩
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  dsimp only
  obtain ⟨a, C, ha, hC, hcharts⟩ :=
    exists_countable_pointed_limit_normal_charts_of_approximations.{u, w}
      n K hn hr hv A hA
  refine ⟨a, C, ha, hC, ?_⟩
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
  intro Q hvol hcurv X _ _ hX p R ε F hR hε
  obtain ⟨q, z, Φ, σA, g, ψ, hq0, hbase, hσA, hsmall, hcover, hdata⟩ :=
    hcharts P hcomplete hconn Q hvol hcurv X p R ε F hR hε
  have hchart (j : Option (ℕ × ℕ)) := (hdata j).2.2.2.2.1
  have hmem (j : Option (ℕ × ℕ)) := (hdata j).2.2.2.2.2.2.2.2.2.1
  have hconvA (j : Option (ℕ × ℕ)) := (hdata j).2.2.2.2.2.2.2.2.2.2.1
  have hψs (j : Option (ℕ × ℕ)) := (hdata j).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hψt (j : Option (ℕ × ℕ)) := (hdata j).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hψ0 (j : Option (ℕ × ℕ)) := (hdata j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hψanti (j : Option (ℕ × ℕ)) := (hdata j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hψmap (j : Option (ℕ × ℕ)) := (hdata j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨σB, b, hσB, hb1, hb2, hb3, hb4, hman⟩ :=
    exists_limit_atlas_of_normal_chart_limits (Y := fun i => (P (σA i)).M) K hK p
      (fun i => (P (σA i)).basepoint) (fun i => F (σA i)) (hε.comp hσA.tendsto_atTop)
      (fun i => (P (σA i)).metric) (fun j => a (j.elim 0 Prod.fst))
      (fun j => C (j.elim 0 Prod.fst)) (fun j => ha (j.elim 0 Prod.fst))
      (fun j i => Φ j (σA i)) (fun j i => z j (σA i))
      (fun j i => (hchart j (σA i)).1) (fun j i => (hchart j (σA i)).2.2.1)
      (fun j i => (hchart j (σA i)).2.2.2.2.2.2.2.2.1)
      (fun j i => (hchart j (σA i)).2.2.2.2.2.2.2.2.2.1)
      (fun j i w hw => ((hchart j (σA i)).2.2.2.2.2.1 w hw).1)
      (fun j i w hw k hk => le_trans (le_add_of_nonneg_right (norm_nonneg _))
        (((hchart j (σA i)).2.2.2.2.2.1 w hw).2 k hk))
      g hmem hconvA ψ q hψs hψt hψ0 hcover hψanti hψmap
  have hreal := exists_unique_metric_of_normal_chart_limits
    (Y := fun i => (P (σA (σB i))).M) hX K p (fun i => (P (σA (σB i))).basepoint)
    (fun i => F (σA (σB i))) (hε.comp (hσA.comp hσB).tendsto_atTop)
    (fun i => (P (σA (σB i))).metric) (fun _ => ⟨fun _ _ => rfl⟩)
    (fun j => a (j.elim 0 Prod.fst)) (fun j => ha (j.elim 0 Prod.fst))
    (fun j i => Φ j (σA (σB i))) (fun j i => z j (σA (σB i)))
    (fun j i => (hchart j (σA (σB i))).1)
    (fun j i => (hchart j (σA (σB i))).2.2.1)
    (fun j i => (hchart j (σA (σB i))).2.2.2.2.2.2.2.2.1)
    (fun j i => (hchart j (σA (σB i))).2.2.2.2.2.2.2.2.2.1)
    (fun j i w hw v => (((hchart j (σA (σB i))).2.2.2.2.2.1 w hw).1 v).1)
    g (fun j => hσB.tendsto_atTop.eventually (hmem j))
    (fun j => tendstoUniformly_comp_strictMono (hconvA j) hσB) ψ hψs hcover hψmap b
    (fun j => (hb1 j).1) (fun j => (hb1 j).2.2.2) hb3 hb4
  refine ⟨q, z, Φ, fun i => σA (σB i), g, ψ, hcover, b, hq0, hbase, hσA.comp hσB, hsmall,
    fun j => ?_, hb1, hb2, hb3, hb4, hman, hreal⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    hdata j
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hσB.tendsto_atTop.eventually h10,
    tendstoUniformly_comp_strictMono h11 hσB, h12, h13, h14, h15, h16, h17, h18⟩

end DifferentialGeometry.CheegerGromovCompactness
