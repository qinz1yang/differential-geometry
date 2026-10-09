import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.FiniteMetricCurvatureSign
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.ContDiffAtlas
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.SectionalTransport
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.IntrinsicSectional

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold Metric Filter Topology
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open GC.MetricGeometry

namespace DifferentialGeometry.CheegerGromovCompactness

universe u

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "𝓙" => 𝓘(ℝ, E)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pointed_smooth_carrier_limit_of_almost_nonnegative_sectional_curvature
    (K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R) :
    letI : NeZero (Module.finrank ℝ E) := ⟨by simpa using (show n ≠ 0 by omega)⟩
    ∀ (P : ℕ → PointedRiemannianManifold.{u} 𝓙)
      (hcomplete : ∀ i, MetricComplete (P i))
      (hconn : ∀ i, letI : TopologicalSpace (P i).M := (P i).topology;
        ConnectedSpace (P i).M),
    letI : ∀ i, TopologicalSpace (P i).M := fun i => (P i).topology
    letI : ∀ i, ChartedSpace E (P i).M := fun i => (P i).charted
    letI : ∀ i, IsManifold 𝓙 ∞ (P i).M := fun i => (P i).smooth
    letI : ∀ i, IsManifold 𝓙 1 (P i).M := fun i =>
      IsManifold.of_le (I := 𝓙) (M := (P i).M) (n := ∞) (by decide)
    letI : ∀ i, SigmaCompactSpace (P i).M := fun i => (P i).sigmaCompact
    letI : ∀ i, T2Space (P i).M := fun i => (P i).t2
    letI : ∀ i, T2Space (TangentBundle 𝓙 (P i).M) := fun i => (P i).t2TangentBundle
    letI : ∀ i, RiemannianBundle (fun x : (P i).M => TangentSpace 𝓙 x) :=
      fun i => (P i).riemBundle (I := 𝓙)
    letI : ∀ i, (x : (P i).M) → InnerProductSpace ℝ (TangentSpace 𝓙 x) :=
      fun i => (P i).riemInner (I := 𝓙)
    letI : ∀ i, IsContinuousRiemannianBundle E
        (fun x : (P i).M => TangentSpace 𝓙 x) :=
      fun i => (P i).riemBundle_cont (I := 𝓙)
    letI : ∀ i, EMetricSpace (P i).M := fun i => (P i).emetricSpace (I := 𝓙)
    letI : ∀ i, CompleteSpace (P i).M := fun i =>
      MetricComplete.complete (I := 𝓙) (P i) (hcomplete i)
    letI : ∀ i, ConnectedSpace (P i).M := hconn
    letI : ∀ i, MetricSpace (P i).M := fun i =>
      HopfRinow.riemMetricSpace (I := 𝓙) (M := (P i).M)
    (∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure _ (P i).M (P i).metric
      (riemannianBallOf (P i).metric (P i).basepoint r)) →
    (∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈
      riemannianBallOf (P i).metric (P i).basepoint R,
        curvDerivNorm k (P i).metric y ≤ A R) →
    ∀ (η L : ℕ → ℝ), Tendsto η atTop (𝓝 0) → Tendsto L atTop atTop →
    (∀ i, ∀ y ∈ riemannianBallOf (P i).metric (P i).basepoint (L i),
      SectionalBoundedBelowAt (P i).metric y (-η i)) →
    ∃ (φ : ℕ → ℕ) (X : Type) (m : MetricSpace X),
      letI := m
      StrictMono φ ∧ ProperSpace X ∧ CompleteSpace X ∧ PathConnectedSpace X ∧ ConnectedSpace X ∧
      ∃ p : X, PointedGHConverges (fun i => (P (φ i)).basepoint) p ∧
      ∃ c : ChartedSpace E X,
        letI := c
        ∃ hM : IsManifold 𝓙 K X,
          letI := hM
          letI : IsManifold 𝓙 1 X :=
            IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast (show 1 ≤ K by omega))
          ∃ (G : ContMDiffRiemannianMetric 𝓙 ((K - 1 : ℕ) : ℕ∞ω) E
              (TangentSpace 𝓙 : X → Type _))
            (𝒜 : DifferentialGeometry.Topology.Manifold.SmoothCompatibleAtlas E X
              (Option (ℕ × ℕ)))
            (G' : ContMDiffRiemannianMetric 𝓙 ((K - 1 : ℕ) : ℕ∞ω) E (TangentSpace 𝓙 :
              DifferentialGeometry.Topology.Manifold.SmoothCarrier 𝒜 → Type _)),
            (∃ f : Diffeomorph 𝓙 𝓙
                (DifferentialGeometry.Topology.Manifold.SmoothCarrier 𝒜) X K,
              ⇑f = DifferentialGeometry.Topology.Manifold.SmoothCarrier.toBase 𝒜 ∧
              ⇑f.symm = DifferentialGeometry.Topology.Manifold.SmoothCarrier.ofBase 𝒜) ∧
            (∀ (x : DifferentialGeometry.Topology.Manifold.SmoothCarrier 𝒜) (v w : E),
              G'.inner x v w =
                G.inner (DifferentialGeometry.Topology.Manifold.SmoothCarrier.toBase 𝒜 x)
                  (mfderiv 𝓙 𝓙 (DifferentialGeometry.Topology.Manifold.SmoothCarrier.toBase 𝒜)
                    x v)
                  (mfderiv 𝓙 𝓙 (DifferentialGeometry.Topology.Manifold.SmoothCarrier.toBase 𝒜)
                    x w)) ∧
            (letI : RiemannianBundle (TangentSpace 𝓙 : X → Type _) := ⟨G.toRiemannianMetric⟩
             IsRiemannianManifold 𝓙 X) ∧
            (letI : RiemannianBundle (TangentSpace 𝓙 : X → Type _) := ⟨G.toRiemannianMetric⟩
             letI : RiemannianBundle (TangentSpace 𝓙 :
                 DifferentialGeometry.Topology.Manifold.SmoothCarrier 𝒜 → Type _) :=
               ⟨G'.toRiemannianMetric⟩
             IsRiemannianManifold 𝓙 (DifferentialGeometry.Topology.Manifold.SmoothCarrier 𝒜) ∧
             ∀ x y : DifferentialGeometry.Topology.Manifold.SmoothCarrier 𝒜,
               riemannianEDist 𝓙 x y = riemannianEDist 𝓙
                 (DifferentialGeometry.Topology.Manifold.SmoothCarrier.toBase 𝒜 x)
                 (DifferentialGeometry.Topology.Manifold.SmoothCarrier.toBase 𝒜 y)) ∧
            (∀ x y : DifferentialGeometry.Topology.Manifold.SmoothCarrier 𝒜,
              dist x y =
                dist (DifferentialGeometry.Topology.Manifold.SmoothCarrier.toBase 𝒜 x)
                  (DifferentialGeometry.Topology.Manifold.SmoothCarrier.toBase 𝒜 y)) ∧
            ∀ (x : DifferentialGeometry.Topology.Manifold.SmoothCarrier 𝒜)
              (v w : TangentSpace 𝓙 x), 0 ≤ G'.sectionalCurvature x v w := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by simpa using (show n ≠ 0 by omega)⟩
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  obtain ⟨a, C, ha, hC, hmain⟩ :=
    exists_pointed_finite_metric_subsequence_of_almost_nonnegative_sectional_curvature.{u}
      n K hn hK hr hv A hA
  intro P hcomplete hconn
  let _ : ∀ i, TopologicalSpace (P i).M := fun i => (P i).topology
  let _ : ∀ i, ChartedSpace E (P i).M := fun i => (P i).charted
  let _ : ∀ i, IsManifold 𝓙 ∞ (P i).M := fun i => (P i).smooth
  let _ : ∀ i, IsManifold 𝓙 1 (P i).M := fun i =>
    IsManifold.of_le (I := 𝓙) (M := (P i).M) (n := ∞) (by decide)
  let _ : ∀ i, SigmaCompactSpace (P i).M := fun i => (P i).sigmaCompact
  let _ : ∀ i, T2Space (P i).M := fun i => (P i).t2
  let _ : ∀ i, T2Space (TangentBundle 𝓙 (P i).M) := fun i => (P i).t2TangentBundle
  let _ : ∀ i, RiemannianBundle (fun x : (P i).M => TangentSpace 𝓙 x) :=
    fun i => (P i).riemBundle (I := 𝓙)
  let _ : ∀ i, (x : (P i).M) → InnerProductSpace ℝ (TangentSpace 𝓙 x) :=
    fun i => (P i).riemInner (I := 𝓙)
  let _ : ∀ i, IsContinuousRiemannianBundle E
      (fun x : (P i).M => TangentSpace 𝓙 x) :=
    fun i => (P i).riemBundle_cont (I := 𝓙)
  let _ : ∀ i, EMetricSpace (P i).M := fun i => (P i).emetricSpace (I := 𝓙)
  let _ : ∀ i, CompleteSpace (P i).M := fun i =>
    MetricComplete.complete (I := 𝓙) (P i) (hcomplete i)
  let _ : ∀ i, ConnectedSpace (P i).M := hconn
  let _ : ∀ i, MetricSpace (P i).M := fun i =>
    HopfRinow.riemMetricSpace (I := 𝓙) (M := (P i).M)
  intro hvol hcurv η L hη hL hsec
  obtain ⟨φ, X, m, hφ, hXp, hXc, hpc, hcc, p, hGH, hlen, hseg, ν, R, ε, F,
    hν, hR, hε, q, z, Φ, τ, g, ψ, hcover, b, hsign,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, hM, G, ⟨hGb, hRiem⟩, huniq⟩ :=
    hmain P hcomplete hconn (fun _ _ => LinearIsometryEquiv.refl ℝ E)
      hvol hcurv η L hη hL hsec
  let _ : MetricSpace X := m
  let c : ChartedSpace E X :=
    DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover
      (fun j => (ψ j).symm) hcover
  let _ := c
  let _ : IsManifold 𝓙 K X := hM
  let _ : IsManifold 𝓙 1 X :=
    IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast (show 1 ≤ K by omega))
  obtain ⟨𝒜, κ, hchart, hst, hκ, hfix, hdetκ, hcomp, hdiff, hleft, hright,
    G', hG', hnorm, hinvnorm, hlength, hinvlength, hRiemdist, hdist, hcarrierRiem⟩ :=
    Topology.Manifold.SmoothCarrier.exists_of_contDiff_atlas (by omega : 1 ≤ K)
      ψ hcover (fun j d => (h7 j d).1) hM G hRiem
  have hψΩ : ∀ j, (ψ j).source ⊆ ball (0 : E) (a (j.elim 0 Prod.fst)) := by
    intro j
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsrc, -⟩ := h5 j
    rw [hsrc]
    exact Metric.ball_subset_ball (by linarith [ha (j.elim 0 Prod.fst)])
  have hmaps : ∀ j, MapsTo (κ j).symm (ψ j).source
      (ball (0 : E) (a (j.elim 0 Prod.fst))) := by
    intro j y hy
    have hy' : (κ j).symm y ∈ (ψ j).source := by
      rw [← (hst j).2, hchart j, OpenPartialHomeomorph.trans_target,
        Set.mem_inter_iff, Set.mem_preimage, Homeomorph.toOpenPartialHomeomorph_symm_apply,
        OpenPartialHomeomorph.symm_target] at hy
      exact hy.2
    exact hψΩ j hy'
  have hread := Topology.Manifold.SmoothCarrier.inner_chart_symm_eq_coefficientPullback
    (by omega : 1 ≤ K) ψ hcover hM 𝒜 κ hchart (fun j => (hst j).2) hcomp b G G' hGb hG'
  have hnonneg : ∀ (x : Topology.Manifold.SmoothCarrier 𝒜)
      (v w : TangentSpace 𝓙 x), 0 ≤ G'.sectionalCurvature x v w := by
    intro x v w
    apply Topology.Manifold.SmoothCarrier.sectionalCurvature_nonneg_of_chart_coefficients
      𝒜 G' (by exact_mod_cast (show 2 ≤ K - 1 by omega))
      (fun j => Analysis.coefficientPullback (b j) (κ j).symm)
      (fun j y hy v w => hread j y ((hst j).2 ▸ hy) v w) _ x v w
    intro j y hy v w
    exact (Analysis.coefficientRm04_nonneg_coefficientPullback_homeomorph
      (ψ j).open_source Metric.isOpen_ball hK (h6 j).1 (h6 j).2.1
      (fun z hz => Analysis.isCoercive_of_half_sq_le fun u => ((h6 j).2.2.1 z hz u).1)
      (hκ j).1 (hκ j).2 (hmaps j) (hsign j) y ((hst j).2 ▸ hy) v w).2
  exact ⟨φ, X, m, hφ, hXp, hXc, hpc, hcc, p, hGH, c, hM, G, 𝒜, G', hdiff,
    hG', hRiem, ⟨hcarrierRiem, hRiemdist⟩, hdist, hnonneg⟩

end DifferentialGeometry.CheegerGromovCompactness

end
