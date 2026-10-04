import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.OrientedCurvatureAtlas
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.OrientedContDiffAtlas

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

theorem exists_pointed_smooth_carrier_limit_with_oriented_curvature_atlas
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
         ∃ G : ContMDiffRiemannianMetric 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) ((K - 1 : ℕ) : ℕ∞ω)
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
            IsRiemannianManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) X) ∧
           (∀ G₁ : ContMDiffRiemannianMetric 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) ((K - 1 : ℕ) : ℕ∞ω)
               (EuclideanSpace ℝ (Fin n))
               (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) : X → Type _),
             ((∀ j x, x ∈ (ψ j).symm.source → ∀ v w : EuclideanSpace ℝ (Fin n),
               G₁.inner x v w = b j ((ψ j).symm x)
                 (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                   (ψ j).symm x v)
                 (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                   (ψ j).symm x w)) ∧
             (letI : RiemannianBundle
                 (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) : X → Type _) :=
               ⟨G₁.toRiemannianMetric⟩
              IsRiemannianManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) X)) →
             G₁ = G) ∧
           ∃ (𝒜 : Topology.Manifold.SmoothCompatibleAtlas (EuclideanSpace ℝ (Fin n)) X
               (Option (ℕ × ℕ)))
             (κ : Option (ℕ × ℕ) → EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)),
             (∀ j, 𝒜.chart j = (ψ j).symm.trans (κ j).toOpenPartialHomeomorph) ∧
             (∀ j, (𝒜.chart j).source = (ψ j).target ∧ (𝒜.chart j).target = (ψ j).source) ∧
             (∀ j, ContDiff ℝ K (κ j) ∧ ContDiff ℝ K (κ j).symm) ∧
             (∀ j u, u ∉ (ψ j).source → κ j u = u ∧ (κ j).symm u = u) ∧
             (∀ j u, 0 < (fderiv ℝ (κ j) u).det) ∧
             𝒜.IsCompatible (fun j => (ψ j).symm) K ∧
             (∀ j d, ∀ u ∈ ((𝒜.chart j).symm.trans (𝒜.chart d)).source,
               0 < (fderiv ℝ ((𝒜.chart j).symm.trans (𝒜.chart d)) u).det) ∧
             (∃ O : ManifoldOrientation 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                 (Topology.Manifold.SmoothCarrier 𝒜) n,
               ∀ (y₀ x : Topology.Manifold.SmoothCarrier 𝒜)
                 (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
                   (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) y₀).baseSet),
                 O.inChart y₀ x hx = stdEuclideanOrientation n) ∧
             (∃ f : Diffeomorph 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                 (Topology.Manifold.SmoothCarrier 𝒜) X K,
               ⇑f = Topology.Manifold.SmoothCarrier.toBase 𝒜 ∧
                 ⇑f.symm = Topology.Manifold.SmoothCarrier.ofBase 𝒜) ∧
             (∀ x : Topology.Manifold.SmoothCarrier 𝒜,
               (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                   (Topology.Manifold.SmoothCarrier.ofBase 𝒜)
                   (Topology.Manifold.SmoothCarrier.toBase 𝒜 x)).comp
                 (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                   (Topology.Manifold.SmoothCarrier.toBase 𝒜) x) =
               ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x)) ∧
             (∀ y : X,
               (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                   (Topology.Manifold.SmoothCarrier.toBase 𝒜)
                   (Topology.Manifold.SmoothCarrier.ofBase 𝒜 y)).comp
                 (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                   (Topology.Manifold.SmoothCarrier.ofBase 𝒜) y) =
               ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) y)) ∧
             ∃ G' : ContMDiffRiemannianMetric 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) ((K - 1 : ℕ) : ℕ∞ω)
                 (EuclideanSpace ℝ (Fin n))
                 (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) :
                   Topology.Manifold.SmoothCarrier 𝒜 → Type _),
               (∀ (x : Topology.Manifold.SmoothCarrier 𝒜) (v w : EuclideanSpace ℝ (Fin n)),
                 G'.inner x v w = G.inner (Topology.Manifold.SmoothCarrier.toBase 𝒜 x)
                   (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                     (Topology.Manifold.SmoothCarrier.toBase 𝒜) x v)
                   (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                     (Topology.Manifold.SmoothCarrier.toBase 𝒜) x w)) ∧
               (letI : RiemannianBundle
                   (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) : X → Type _) :=
                 ⟨G.toRiemannianMetric⟩
                letI : RiemannianBundle
                   (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) :
                     Topology.Manifold.SmoothCarrier 𝒜 → Type _) :=
                 ⟨G'.toRiemannianMetric⟩
                (∀ (x : Topology.Manifold.SmoothCarrier 𝒜)
                    (v : TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x),
                  ‖mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                    (Topology.Manifold.SmoothCarrier.toBase 𝒜) x v‖ₑ = ‖v‖ₑ) ∧
                (∀ (y : X) (w : TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) y),
                  ‖mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                    (Topology.Manifold.SmoothCarrier.ofBase 𝒜) y w‖ₑ = ‖w‖ₑ) ∧
                (∀ (γ : ℝ → Topology.Manifold.SmoothCarrier 𝒜) (t₀ t₁ : ℝ),
                  (∀ᵐ t ∂MeasureTheory.volume.restrict (Ioo t₀ t₁),
                    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) γ t) →
                  pathELength 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                      (Topology.Manifold.SmoothCarrier.toBase 𝒜 ∘ γ) t₀ t₁ =
                    pathELength 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) γ t₀ t₁) ∧
                (∀ (γ : ℝ → X) (t₀ t₁ : ℝ),
                  (∀ᵐ t ∂MeasureTheory.volume.restrict (Ioo t₀ t₁),
                    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) γ t) →
                  pathELength 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                      (Topology.Manifold.SmoothCarrier.ofBase 𝒜 ∘ γ) t₀ t₁ =
                    pathELength 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) γ t₀ t₁) ∧
                (∀ x y : Topology.Manifold.SmoothCarrier 𝒜,
                  riemannianEDist 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x y =
                    riemannianEDist 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                      (Topology.Manifold.SmoothCarrier.toBase 𝒜 x)
                      (Topology.Manifold.SmoothCarrier.toBase 𝒜 y)) ∧
                (∀ x y : Topology.Manifold.SmoothCarrier 𝒜,
                  dist x y = dist (Topology.Manifold.SmoothCarrier.toBase 𝒜 x)
                    (Topology.Manifold.SmoothCarrier.toBase 𝒜 y)) ∧
                IsRiemannianManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
                  (Topology.Manifold.SmoothCarrier 𝒜))) := by
  have hK1 : 1 ≤ K := by omega
  dsimp only
  obtain ⟨a, C, ha, hC, hmain⟩ :=
    exists_pointed_finite_metric_subsequence_with_oriented_atlas_of_almost_nonnegative_sectional_curvature.{u}
      n K hn hK hr hv A hA
  refine ⟨a, C, ha, hC, ?_⟩
  intro P hcomplete hconn o hvol hcurv η L hη hL hsec
  obtain ⟨φ, X, m, hφ, hXp, hXc, hpc, hcc, p, hGH, hlen, hseg, ν, R, ε, F, hν, hR, hε, q, z, Φ,
    τ, g, ψ, hcover, b, hsign, horient, hposψ, h1, h2, h3, h4, h5, h6, h7, h8, h9, hM, G,
    ⟨hGb, hRiem⟩, huniq⟩ := hmain P hcomplete hconn o hvol hcurv η L hη hL hsec
  exact ⟨φ, X, m, hφ, hXp, hXc, hpc, hcc, p, hGH, hlen, hseg, ν, R, ε, F, hν, hR, hε, q, z, Φ,
    τ, g, ψ, hcover, b, hsign, horient, hposψ, h1, h2, h3, h4, h5, h6, h7, h8, h9, hM, G, hGb,
    hRiem, huniq,
    Topology.Manifold.SmoothCarrier.exists_of_contDiff_atlas_oriented hK1 ψ hcover
      (fun j d => (h7 j d).1) hM finrank_euclideanSpace_fin hposψ (stdEuclideanOrientation n)
      G hRiem⟩

end DifferentialGeometry.CheegerGromovCompactness
