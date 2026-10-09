import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.FiniteMetricCurvatureSign
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.OrientedChart
import DifferentialGeometry.Topology.Manifold.OrientedChartTransition
import DifferentialGeometry.Analysis.Calculus.MapConvergence.DeterminantSign

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

theorem exists_pointed_finite_metric_subsequence_with_oriented_atlas_of_almost_nonnegative_sectional_curvature
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
    ∀ (o : ∀ i, ManifoldOrientation 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (P i).M n),
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
      (∀ (j : Option (ℕ × ℕ)) (i : ℕ),
        IsOrientedChart (o (φ (ν i))) (stdEuclideanOrientation n) (Φ j i)) ∧
      (∀ j d : Option (ℕ × ℕ), ∀ u ∈ ((ψ j).trans (ψ d).symm).source,
        0 < (fderiv ℝ ((ψ j).trans (ψ d).symm) u).det) ∧
      q none = p ∧ (∀ i, Φ none i 0 = (P (φ (ν i))).basepoint) ∧ StrictMono τ ∧
      (⋃ j : Option (ℕ × ℕ), ball (q j) (a (j.elim 0 Prod.fst) / 64)) = univ ∧
      (∀ j : Option (ℕ × ℕ),
        q j ∈ ball p (((j.elim 0 Prod.fst : ℕ) : ℝ) + 1) ∧
        (q j = p → ∀ i, z j i = (P (φ (ν i))).basepoint) ∧
        (∀ i, z j i ∈ closedBall (P (φ (ν i))).basepoint (R i) ∧
          z j i ∈ ball (P (φ (ν i))).basepoint (((j.elim 0 Prod.fst : ℕ) : ℝ) + 2)) ∧
        Tendsto (fun i => (F i).extendToWholeSpace (z j i)) atTop (𝓝 (q j)) ∧
        (∀ i, (Φ j i).source = ball 0 (2 * a (j.elim 0 Prod.fst)) ∧
          EqOn (Φ j i) (intrinsicFramedExp (P (φ (ν i))).metric (hEnorm (φ (ν i))) (z j i) ∘
              orientedEuclideanNormalRotation (show 0 < n by omega) (P (φ (ν i))).metric
                (o (φ (ν i))) (z j i))
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
    exists_pointed_finite_metric_subsequence_of_almost_nonnegative_sectional_curvature.{u}
      n K hn hK hr hv A hA
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
  intro o hvol hcurv η L hη hL hsec
  obtain ⟨φ, X, m, hφ, hXp, hXc, hpc, hcc, p, hGH, hlen, hseg, ν, R, ε, F, hν, hR, hε, q, z, Φ,
    τ, g, ψ, hcover, b, hsign, hrest⟩ := hmain P hcomplete hconn
      (fun i => orientedEuclideanNormalRotation (show 0 < n by omega) (P i).metric (o i)) hvol hcurv
      η L hη hL hsec
  have horient : ∀ (j : Option (ℕ × ℕ)) (i : ℕ),
      IsOrientedChart (o (φ (ν i))) (stdEuclideanOrientation n) (Φ j i) := by
    intro j i
    have hchart := (hrest.2.2.2.2.1 j).2.2.2.2.1 i
    exact isOrientedChart_of_eqOn_intrinsicFramedExp (P (φ (ν i))).metric _ (o (φ (ν i)))
      (stdEuclideanOrientation n) (firstCoordinateReflection (show 0 < n by omega))
      (det_firstCoordinateReflection_neg (show 0 < n by omega)) (z j i) (Φ j i)
      (by linarith [ha (j.elim 0 Prod.fst)]) hchart.1 hchart.2.1
  refine ⟨φ, X, m, hφ, hXp, hXc, hpc, hcc, p, hGH, hlen, hseg, ν, R, ε, F, hν, hR, hε, q, z, Φ,
    τ, g, ψ, hcover, b, hsign, horient, fun j d u hu => ?_, hrest⟩
  have hT := hrest.2.2.2.2.2.2.1 j d
  have hRev := hrest.2.2.2.2.2.2.1 d j
  have hT1 : ContDiffOn ℝ 1 ((ψ j).trans (ψ d).symm) ((ψ j).trans (ψ d).symm).source :=
    hT.1.of_le (by exact_mod_cast (show 1 ≤ K by omega))
  have hR1 : ContDiffOn ℝ 1 ((ψ d).trans (ψ j).symm) ((ψ d).trans (ψ j).symm).source :=
    hRev.1.of_le (by exact_mod_cast (show 1 ≤ K by omega))
  have hTd : DifferentiableAt ℝ ((ψ j).trans (ψ d).symm) u :=
    (hT1.contDiffAt (((ψ j).trans (ψ d).symm).open_source.mem_nhds hu)).differentiableAt
      one_ne_zero
  have hRu := DifferentialGeometry.Analysis.trans_symm_apply_mem_source hu
  have hRd : DifferentiableAt ℝ ((ψ d).trans (ψ j).symm) (((ψ j).trans (ψ d).symm) u) :=
    (hR1.contDiffAt (((ψ d).trans (ψ j).symm).open_source.mem_nhds hRu)).differentiableAt
      one_ne_zero
  have hne := DifferentialGeometry.Analysis.det_fderiv_trans_symm_ne_zero hu hTd hRd
  obtain ⟨hconvK, _, -, -, hev⟩ :=
    hT.2 {u} isCompact_singleton (Set.singleton_subset_iff.mpr hu)
  refine DifferentialGeometry.Analysis.det_fderiv_pos_of_mapCPConvergenceOn_at
    (hconvK.mono_order (show 1 ≤ K by omega)) (Set.mem_singleton u) hTd hne ?_
  filter_upwards [hev] with i hi
  have hui : u ∈ ((Φ j (τ i)).trans (Φ d (τ i)).symm).source := hi.1 (Set.mem_singleton u)
  exact ⟨Topology.Manifold.differentiableAt_symm_comp hui,
    Topology.Manifold.det_fderiv_symm_comp_pos (o (φ (ν (τ i)))) (stdEuclideanOrientation n)
      (Φ := Φ j (τ i)) (Ψ := Φ d (τ i)) (horient j (τ i)) (horient d (τ i)) hui⟩

end DifferentialGeometry.CheegerGromovCompactness
