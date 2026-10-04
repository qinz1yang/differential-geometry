import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.PointedNormalCharts
import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Radial
import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Countable

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

private theorem exists_shell_centers
    {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X] (p : X) :
    ∃ q : Option (ℕ × ℕ) → X,
      q none = p ∧
      (∀ s j : ℕ, q (some (s, j)) ∈ ball p ((s : ℝ) + 1)) ∧
      ∀ b : ℕ → ℝ, (∀ s, 0 < b s) →
        (⋃ j : Option (ℕ × ℕ), ball (q j) (b (j.elim 0 Prod.fst))) = univ := by
  classical
  have : Nonempty X := ⟨p⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq X
  let q : Option (ℕ × ℕ) → X := fun j => j.elim p
    (fun sj => if dist (d sj.2) p < (sj.1 : ℝ) + 1 then d sj.2 else p)
  refine ⟨q, rfl, ?_, ?_⟩
  · intro s j
    change (if dist (d j) p < (s : ℝ) + 1 then d j else p) ∈ ball p ((s : ℝ) + 1)
    split_ifs with h
    · exact h
    · exact mem_ball_self (by positivity)
  · intro b hb
    apply eq_univ_of_forall
    intro x
    obtain ⟨s, hs⟩ := exists_nat_gt (dist x p)
    have hmargin : 0 < (s : ℝ) + 1 - dist x p := by linarith
    have hδ : 0 < min (b s) ((s : ℝ) + 1 - dist x p) := lt_min (hb s) hmargin
    obtain ⟨j, hj⟩ := hd.exists_dist_lt x hδ
    have hjb : dist x (d j) < b s := hj.trans_le (min_le_left _ _)
    have hjs : dist (d j) p < (s : ℝ) + 1 := by
      have hsmall := hj.trans_le (min_le_right _ _)
      have htri := dist_triangle (d j) x p
      rw [dist_comm (d j) x] at htri
      linarith
    apply mem_iUnion.mpr
    refine ⟨some (s, j), ?_⟩
    change x ∈ ball (if dist (d j) p < (s : ℝ) + 1 then d j else p) (b s)
    rw [ite_eq_left hjs]
    exact hjb

theorem exists_countable_pointed_limit_normal_charts_of_approximations
    (n K : ℕ) (hn : 2 ≤ n) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
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
    ∀ (X : Type w) [MetricSpace X] [ProperSpace X] (p : X) (R ε : ℕ → ℝ)
      (F : ∀ i, PointedBallApprox (P i).basepoint p (R i) (ε i)),
      Tendsto R atTop atTop → Tendsto ε atTop (𝓝 0) →
    ∃ (q : Option (ℕ × ℕ) → X) (z : Option (ℕ × ℕ) → ∀ i, (P i).M)
      (Φ : Option (ℕ × ℕ) → ∀ i, PartialDiffeomorph 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n)) (P i).M ∞)
      (σ : ℕ → ℕ)
      (g : ∀ j : Option (ℕ × ℕ),
        closedBall (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst) / 8) → X)
      (ψ : Option (ℕ × ℕ) → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) X),
      q none = p ∧ (∀ i, Φ none i 0 = (P i).basepoint) ∧ StrictMono σ ∧
      (⋃ j : Option (ℕ × ℕ), ball (q j) (a (j.elim 0 Prod.fst) / 64)) = univ ∧
      (∀ x, ∃ j : Option (ℕ × ℕ), x ∈ (ψ j).target) ∧
      ∀ j : Option (ℕ × ℕ),
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
          Φ j (σ i) u ∈ closedBall (P (σ i)).basepoint (R (σ i))) ∧
        TendstoUniformly (fun i (u : closedBall (0 : EuclideanSpace ℝ (Fin n))
            (a (j.elim 0 Prod.fst) / 8)) =>
          (F (σ i)).extendToWholeSpace (Φ j (σ i) u)) (g j) atTop ∧
        ball (q j) (a (j.elim 0 Prod.fst) / 8) ⊆ range (g j) ∧
        (ψ j).source = ball 0 (a (j.elim 0 Prod.fst) / 16) ∧
        (ψ j).target = ball (q j) (a (j.elim 0 Prod.fst) / 16) ∧ ψ j 0 = q j ∧
        LipschitzWith 2 (fun u : ball (0 : EuclideanSpace ℝ (Fin n))
          (a (j.elim 0 Prod.fst) / 16) => ψ j u) ∧
        AntilipschitzWith 2 (fun u : ball (0 : EuclideanSpace ℝ (Fin n))
          (a (j.elim 0 Prod.fst) / 16) => ψ j u) ∧
        ∀ u : ball (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst) / 16),
          ψ j u = g j ⟨u, (ball_subset_closedBall.trans
            (closedBall_subset_closedBall (by linarith [ha (j.elim 0 Prod.fst)]))) u.property⟩ := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let _ : NeZero (Module.finrank ℝ E) := ⟨by simpa [E] using (show n ≠ 0 by omega)⟩
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  dsimp only
  have H (t : ℕ) :=
    exists_uniform_pointed_limit_normal_charts_of_approximations.{u, w}
      n K hn hr hv (show 0 < (t : ℝ) + 1 by positivity)
      (hA (2 * ((t : ℝ) + 1) + r + 4) (by positivity))
  choose a C ha hC hsmall hcharts using H
  refine ⟨a, C, ha, fun t => ⟨hC t, hsmall t⟩, ?_⟩
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
  intro Q hvol hcurv X _ _ p R ε F hR hε
  obtain ⟨q, hq0, hq, hcover⟩ := exists_shell_centers p
  have hqs (j : Option (ℕ × ℕ)) : q j ∈ ball p (((j.elim 0 Prod.fst : ℕ) : ℝ) + 1) := by
    cases j with
    | none =>
      rw [hq0]
      exact mem_ball_self (by positivity)
    | some sj => exact hq sj.1 sj.2
  have each (j : Option (ℕ × ℕ)) :=
    hcharts (j.elim 0 Prod.fst) P hcomplete hconn Q hvol
      (hcurv (2 * (((j.elim 0 Prod.fst : ℕ) : ℝ) + 1) + r + 4) (by positivity))
      X p (q j) R ε F hR hε (hqs j)
  choose z Φ _ _ hzp hz hzconv hchart _ using each
  let w₀ (j : Option (ℕ × ℕ)) : closedBall (0 : E) (a (j.elim 0 Prod.fst) / 8) :=
    ⟨0, mem_closedBall_self (div_nonneg (ha (j.elim 0 Prod.fst)).le (by norm_num))⟩
  let c (i : ℕ) (j : Option (ℕ × ℕ)) (u : closedBall (0 : E) (a (j.elim 0 Prod.fst) / 8)) :
      (P i).M := Φ j i u
  have hc0 (j : Option (ℕ × ℕ)) (i : ℕ) : c i j (w₀ j) = z j i := (hchart j i).2.2.1
  obtain ⟨σ, g, hσ, hg⟩ := exists_bilipschitz_chart_limits_of_approximations
    w₀ p q (fun i => (P i).basepoint) (fun _ => 2) (fun _ => 2) F hR hε c
    (fun j => Eventually.of_forall fun i => by
      rw [hc0]
      exact (hz j i).1)
    (fun j => by
      simp only [hc0]
      exact hzconv j)
    (fun j => Eventually.of_forall fun i =>
      ⟨(hchart j i).2.2.2.2.2.2.1, (hchart j i).2.2.2.2.2.2.2.1⟩)
  have hradg (j : Option (ℕ × ℕ)) (u : closedBall (0 : E) (a (j.elim 0 Prod.fst) / 8)) :
      dist (g j u) (q j) = ‖(u : E)‖ := by
    obtain ⟨_, _, hzero, hmem, hconv, _⟩ := hg j
    have hrad' : ∀ i (v : closedBall (0 : E) (a (j.elim 0 Prod.fst) / 8)),
        dist (c (σ i) j v) (c (σ i) j (w₀ j)) = ‖(v : E)‖ := by
      intro i v
      rw [hc0]
      exact (hchart j (σ i)).2.2.2.2.2.2.2.2.1 v
        (closedBall_subset_ball (by linarith [ha (j.elim 0 Prod.fst)]) v.property)
    exact dist_eq_norm_of_radial_chart_limit (w₀ j) p (q j) (fun i => (P (σ i)).basepoint)
      (fun i => F (σ i)) (hε.comp hσ.tendsto_atTop) (fun i => c (σ i) j) (g j) hzero hmem
      hconv hrad' u
  have hcoverage (j : Option (ℕ × ℕ)) :
      ball (q j) (a (j.elim 0 Prod.fst) / 8) ⊆ range (g j) := by
    apply (hg j).2.2.2.2.2 (a (j.elim 0 Prod.fst) / 8)
    apply Eventually.of_forall
    intro i
    rw [hc0]
    intro y hy
    have he : y ∈ (Φ j i : E → (P i).M) '' closedBall 0 (a (j.elim 0 Prod.fst) / 8) := by
      rw [(hchart j i).2.2.2.2.2.2.2.2.2.2 (a (j.elim 0 Prod.fst) / 8)
        (by linarith [ha (j.elim 0 Prod.fst)])]
      exact ball_subset_closedBall hy
    obtain ⟨v, hv, heq⟩ := he
    exact Set.mem_range.mpr ⟨⟨v, hv⟩, heq⟩
  have hopen (j : Option (ℕ × ℕ)) := exists_radial_openPartialHomeomorph_of_closedBall
    (div_pos (ha (j.elim 0 Prod.fst)) (by norm_num : (0 : ℝ) < 16))
    (by linarith [ha (j.elim 0 Prod.fst)]) (q j) (g j) (hg j).1 (hg j).2.1 (hradg j)
    ((ball_subset_ball (by linarith [ha (j.elim 0 Prod.fst)])).trans (hcoverage j))
  choose ψ hψs hψt hψlip hψanti hψmap using hopen
  have hsmallcover : (⋃ j : Option (ℕ × ℕ), ball (q j) (a (j.elim 0 Prod.fst) / 64)) = univ :=
    hcover (fun t => a t / 64) (fun t => div_pos (ha t) (by norm_num))
  refine ⟨q, z, Φ, σ, g, ψ, hq0, fun i => (hchart none i).2.2.1.trans (hzp none hq0 i), hσ,
    hsmallcover, ?_, ?_⟩
  · intro x
    obtain ⟨j, hj⟩ := mem_iUnion.mp (Set.eq_univ_iff_forall.mp hsmallcover x)
    refine ⟨j, ?_⟩
    rw [hψt j]
    exact ball_subset_ball (by linarith [ha (j.elim 0 Prod.fst)]) hj
  · intro j
    obtain ⟨hlip, hanti, hzero, hmem, hconv, _⟩ := hg j
    have hz2 (i : ℕ) : z j i ∈ closedBall (P i).basepoint (R i) ∧
        z j i ∈ ball (P i).basepoint (((j.elim 0 Prod.fst : ℕ) : ℝ) + 2) :=
      ⟨(hz j i).1, ball_subset_ball (by linarith) (hz j i).2⟩
    have hψ0 : ψ j 0 = q j :=
      (hψmap j ⟨0, mem_ball_self (div_pos (ha (j.elim 0 Prod.fst)) (by norm_num))⟩).trans hzero
    exact ⟨hqs j, hzp j, hz2, hzconv j, hchart j, hlip, hanti, hzero, hradg j, hmem, hconv,
      hcoverage j, hψs j, hψt j, hψ0, hψlip j, hψanti j, hψmap j⟩

end DifferentialGeometry.CheegerGromovCompactness
