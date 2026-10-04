import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.FiniteMetricCompactness
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CoefficientChart

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
universe u

theorem coefficientRm04_nonneg_of_normal_chart_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)] [∀ i, T2Space (Y i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    {a : ℝ} (ha : 0 < a) (hΦs : ∀ i, (Φ i).source = ball 0 (2 * a))
    (b : E → E →L[ℝ] E →L[ℝ] ℝ) (hb : ContDiffOn ℝ 2 b (ball 0 a))
    (hbpos : ∀ w ∈ ball (0 : E) a, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ b w v v)
    (hconv : ∀ D : Set E, IsCompact D → D ⊆ ball 0 a →
      MapCPConvergenceOn D 2 (fun i => pullbackMetricCoefficients (g i) (Φ i)) b)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsec : ∀ᶠ i in atTop, ∀ w ∈ ball (0 : E) a,
      SectionalBoundedBelowAt (g i) (Φ i w) (-ε i)) :
    ∀ w ∈ ball (0 : E) a, ∀ v u : E,
      0 ≤ DifferentialGeometry.Analysis.coefficientRm04 b w v u u v := by
  intro w hw v u
  have hsrc (i : ℕ) : ball (0 : E) a ⊆ (Φ i).source := by
    rw [hΦs i]
    exact Metric.ball_subset_ball (by linarith)
  have hB (i : ℕ) : ContDiffOn ℝ 2 (pullbackMetricCoefficients (g i) (Φ i)) (ball 0 a) :=
    ((DifferentialGeometry.Geometry.contDiffOn_pullback_metric_coefficients (g i)
      (Φ i).open_source (Φ i).contMDiffOn).mono (hsrc i)).of_le ENat.LEInfty.out
  have hwD : ({w} : Set E) ⊆ ball 0 a := Set.singleton_subset_iff.mpr hw
  have hpos : ∀ x ∈ ({w} : Set E), ∀ v' : E, v' ≠ 0 → 0 < b x v' v' := by
    intro x hx v' hv'
    have h1 : (0 : ℝ) < (1 / 2 : ℝ) * ‖v'‖ ^ 2 :=
      mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hv') 2)
    exact lt_of_lt_of_le h1 (hbpos x (hwD hx) v')
  have hlow : ∀ᶠ i in atTop, ∀ x ∈ ({w} : Set E), ∀ v' u' : E,
      -ε i * (pullbackMetricCoefficients (g i) (Φ i) x v' v' *
          pullbackMetricCoefficients (g i) (Φ i) x u' u' -
          (pullbackMetricCoefficients (g i) (Φ i) x v' u') ^ 2) ≤
        DifferentialGeometry.Analysis.coefficientRm04
          (pullbackMetricCoefficients (g i) (Φ i)) x v' u' u' v' := by
    filter_upwards [hsec] with i hi x hx v' u'
    exact coefficientRm04_lower_bound_of_sectionalBoundedBelowAt (g i) (Φ i) (hsrc i (hwD hx))
      (hi x (hwD hx)) v' u'
  exact DifferentialGeometry.Analysis.nonneg_coefficientRm04_of_eventual_sectional_lower_bound
    Metric.isOpen_ball hwD hB hb (hconv {w} isCompact_singleton hwD) hpos hε hlow w
    (Set.mem_singleton w) v u

theorem exists_pointed_finite_metric_subsequence_of_almost_nonnegative_sectional_curvature
    (n K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
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
    ∀ (η L : ℕ → ℝ), Tendsto η atTop (𝓝 0) → Tendsto L atTop atTop →
    (∀ i, ∀ y ∈ riemannianBallOf (P i).metric (P i).basepoint (L i),
      SectionalBoundedBelowAt (P i).metric y (-η i)) →
    ∃ (φ : ℕ → ℕ) (X : Type) (m : MetricSpace X),
      letI := m
      StrictMono φ ∧ ProperSpace X ∧ CompleteSpace X ∧ PathConnectedSpace X ∧ ConnectedSpace X ∧
      ∃ p : X, PointedGHConverges (fun i => (P (φ i)).basepoint) p ∧
        (∀ x y : X, Metric.intrinsicEDist x y = edist x y) ∧
        (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X, Continuous f ∧
          f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
        ∃ (ν : ℕ → ℕ) (R ε : ℕ → ℝ)
          (F : ∀ i, PointedBallApprox (P (φ (ν i))).basepoint p (R i) (ε i)),
          StrictMono ν ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
    ∃ (q : Option (ℕ × ℕ) → X) (z : Option (ℕ × ℕ) → ∀ i, (P (φ (ν i))).M)
      (Φ : Option (ℕ × ℕ) → ∀ i, PartialDiffeomorph 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n)) (P (φ (ν i))).M ∞)
      (τ : ℕ → ℕ)
      (g : ∀ j : Option (ℕ × ℕ),
        closedBall (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst) / 8) → X)
      (ψ : Option (ℕ × ℕ) → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) X)
      (hcover : ∀ x, ∃ j : Option (ℕ × ℕ), x ∈ (ψ j).target)
      (b : Option (ℕ × ℕ) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (∀ j : Option (ℕ × ℕ), ∀ w ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst)),
        ∀ v u : EuclideanSpace ℝ (Fin n),
          0 ≤ DifferentialGeometry.Analysis.coefficientRm04 (b j) w v u u v) ∧
      q none = p ∧ (∀ i, Φ none i 0 = (P (φ (ν i))).basepoint) ∧ StrictMono τ ∧
      (⋃ j : Option (ℕ × ℕ), ball (q j) (a (j.elim 0 Prod.fst) / 64)) = univ ∧
      (∀ j : Option (ℕ × ℕ),
        q j ∈ ball p (((j.elim 0 Prod.fst : ℕ) : ℝ) + 1) ∧
        (q j = p → ∀ i, z j i = (P (φ (ν i))).basepoint) ∧
        (∀ i, z j i ∈ closedBall (P (φ (ν i))).basepoint (R i) ∧
          z j i ∈ ball (P (φ (ν i))).basepoint (((j.elim 0 Prod.fst : ℕ) : ℝ) + 2)) ∧
        Tendsto (fun i => (F i).extendToWholeSpace (z j i)) atTop (𝓝 (q j)) ∧
        (∀ i, (Φ j i).source = ball 0 (2 * a (j.elim 0 Prod.fst)) ∧
          EqOn (Φ j i) (intrinsicFramedExp (P (φ (ν i))).metric (hEnorm (φ (ν i))) (z j i) ∘ Q (φ (ν i)) (z j i))
            (ball 0 (2 * a (j.elim 0 Prod.fst))) ∧
          Φ j i 0 = z j i ∧
          ContDiffOn ℝ ∞ (pullbackMetricCoefficients (P (φ (ν i))).metric (Φ j i))
            (ball 0 (2 * a (j.elim 0 Prod.fst))) ∧
          ContDiffOn ℝ K (fun w => Ring.inverse
            (IsCoercive.gramCLM (pullbackMetricCoefficients (P (φ (ν i))).metric (Φ j i) w)))
            (ball 0 (2 * a (j.elim 0 Prod.fst))) ∧
          (∀ w ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (a (j.elim 0 Prod.fst)),
            (∀ v : EuclideanSpace ℝ (Fin n), (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
                pullbackMetricCoefficients (P (φ (ν i))).metric (Φ j i) w v v ∧
              pullbackMetricCoefficients (P (φ (ν i))).metric (Φ j i) w v v ≤ 2 * ‖v‖ ^ 2) ∧
            ∀ k : ℕ, k ≤ K →
              ‖iteratedFDeriv ℝ k (pullbackMetricCoefficients (P (φ (ν i))).metric (Φ j i)) w‖ +
                ‖iteratedFDeriv ℝ k (fun y => Ring.inverse
                  (IsCoercive.gramCLM (pullbackMetricCoefficients (P (φ (ν i))).metric (Φ j i) y))) w‖ ≤
                C (j.elim 0 Prod.fst)) ∧
          LipschitzWith 2 (fun w : closedBall (0 : EuclideanSpace ℝ (Fin n))
            (a (j.elim 0 Prod.fst) / 8) => Φ j i w) ∧
          AntilipschitzWith 2 (fun w : closedBall (0 : EuclideanSpace ℝ (Fin n))
            (a (j.elim 0 Prod.fst) / 8) => Φ j i w) ∧
          (∀ w ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (2 * a (j.elim 0 Prod.fst)),
            dist (Φ j i w) (z j i) = ‖w‖) ∧
          (∀ t ≤ 2 * a (j.elim 0 Prod.fst),
            (Φ j i : EuclideanSpace ℝ (Fin n) → (P (φ (ν i))).M) '' ball 0 t = ball (z j i) t) ∧
          ∀ t < 2 * a (j.elim 0 Prod.fst),
            (Φ j i : EuclideanSpace ℝ (Fin n) → (P (φ (ν i))).M) '' closedBall 0 t =
              closedBall (z j i) t) ∧
        LipschitzWith 2 (g j) ∧ AntilipschitzWith 2 (g j) ∧
        g j ⟨0, mem_closedBall_self (div_nonneg (ha (j.elim 0 Prod.fst)).le (by norm_num))⟩ =
          q j ∧
        (∀ u, dist (g j u) (q j) = ‖(u : EuclideanSpace ℝ (Fin n))‖) ∧
        (∀ᶠ i in atTop, ∀ u : closedBall (0 : EuclideanSpace ℝ (Fin n))
            (a (j.elim 0 Prod.fst) / 8),
          Φ j (τ i) u ∈ closedBall (P (φ (ν (τ i)))).basepoint (R (τ i))) ∧
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
            (fun i => pullbackMetricCoefficients (P (φ (ν (τ i)))).metric (Φ j (τ i))) (b j)) ∧
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
           IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast (show 1 ≤ K by omega))
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
  obtain ⟨a, C, ha, hC, hmain⟩ :=
    exists_pointed_finite_metric_subsequence_of_curvature_bounds.{u}
      n K hn (by omega) hr hv A hA
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
  intro Q hvol hcurv η L hη hL hsec
  obtain ⟨φ, X, m, hφ, hXp, hXc, hpc, hcc, p, hGH, hlen, hseg, ν, R, ε, F, hν, hR, hε, q, z, Φ,
    τ, g, ψ, hcover, b, hrest⟩ := hmain P hcomplete hconn Q hvol hcurv
  have hτ : StrictMono τ := hrest.2.2.1
  have hψ : StrictMono (fun i => φ (ν (τ i))) := hφ.comp (hν.comp hτ)
  refine ⟨φ, X, m, hφ, hXp, hXc, hpc, hcc, p, hGH, hlen, hseg, ν, R, ε, F, hν, hR, hε, q, z, Φ,
    τ, g, ψ, hcover, b, fun j => ?_, hrest⟩
  have hA := hrest.2.2.2.2.1 j
  have hB1 := hrest.2.2.2.2.2.1 j
  have hK2 : 2 ≤ K - 1 := by omega
  have hsec' : ∀ᶠ i in atTop, ∀ w ∈ ball (0 : E) (a (j.elim 0 Prod.fst)),
      SectionalBoundedBelowAt (P (φ (ν (τ i)))).metric (Φ j (τ i) w) (-η (φ (ν (τ i)))) := by
    filter_upwards [(hL.comp hψ.tendsto_atTop).eventually_gt_atTop
      (((j.elim 0 Prod.fst : ℕ) : ℝ) + 3)] with i hi w hw
    apply hsec (φ (ν (τ i)))
    have hi' : ((j.elim 0 Prod.fst : ℕ) : ℝ) + 3 < L (φ (ν (τ i))) := hi
    have hz : dist (z j (τ i)) (P (φ (ν (τ i)))).basepoint <
        ((j.elim 0 Prod.fst : ℕ) : ℝ) + 2 := (hA.2.2.1 (τ i)).2
    have hrad : dist (Φ j (τ i) w) (z j (τ i)) = ‖w‖ :=
      (hA.2.2.2.2.1 (τ i)).2.2.2.2.2.2.2.2.1 w
        (Metric.ball_subset_ball (by linarith [ha (j.elim 0 Prod.fst)]) hw)
    have hw' : ‖w‖ < a (j.elim 0 Prod.fst) := mem_ball_zero_iff.mp hw
    have hsmall : 2 * a (j.elim 0 Prod.fst) < 1 := (hC (j.elim 0 Prod.fst)).2
    have htri := dist_triangle (P (φ (ν (τ i)))).basepoint (z j (τ i)) (Φ j (τ i) w)
    rw [dist_comm (P (φ (ν (τ i)))).basepoint (z j (τ i)),
      dist_comm (z j (τ i)) (Φ j (τ i) w), hrad] at htri
    have hd : dist (P (φ (ν (τ i)))).basepoint (Φ j (τ i) w) < L (φ (ν (τ i))) := by
      linarith
    have h2 : edist (P (φ (ν (τ i)))).basepoint (Φ j (τ i) w) <
        ENNReal.ofReal (L (φ (ν (τ i)))) := edist_lt_ofReal.mpr hd
    exact h2
  exact coefficientRm04_nonneg_of_normal_chart_limit (E := E)
    (Y := fun i => (P (φ (ν (τ i)))).M) (ε := fun i => η (φ (ν (τ i))))
    (fun i => (P (φ (ν (τ i)))).metric) (fun i => Φ j (τ i)) (ha (j.elim 0 Prod.fst))
    (fun i => (hA.2.2.2.2.1 (τ i)).1) (b j) (hB1.1.of_le (by exact_mod_cast hK2))
    (fun w hw v' => (hB1.2.2.1 w hw v').1)
    (fun D hD hDs => (hB1.2.2.2 D hD hDs).mono_order hK2)
    (hη.comp hψ.tendsto_atTop) hsec'

end DifferentialGeometry.CheegerGromovCompactness
