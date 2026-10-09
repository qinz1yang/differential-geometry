import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.LConsMergeNoncompact
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceCarrierNoncompact

/-!
# Consumers of the noncompact L-CONS merge (LFR28 blocker B1)

* `exists_lcons_merge_noncompact_of_forall_bounds`: the verbatim form of the frozen statement
  (volume and sectional bounds for EVERY `i`, as in `lfr16_lcons_merge_Stmt`), from the eventual
  form `exists_lcons_merge_noncompact`.
* `exists_lcons_merge_oriented_surfaceCarrier`: LFR16 for noncompact factors, on ONE subsequence —
  B1 (oriented) followed by B2 (`surfaceFactor_smoothCarrier_oriented_noncompact`): the comparison
  maps are almost isometric and cover strictly, the SAME maps track the exact splitting
  `e : N ≃ᵢ ℓ²(ℝ × W)`, and the surface factor has an oriented complete connected smooth carrier
  `S ≃ᵢ W` with a nonnegatively curved `C^{K-1}` metric for which it is a Riemannian manifold.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

universe u w

/-- **B1, verbatim form** (bounds for every `i`). -/
theorem exists_lcons_merge_noncompact_of_forall_bounds
    (K : ℕ) (hK : 4 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {a : ℝ} {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin 3))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) : N → Type _))
        (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N (X (φ i)) K),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L' : Set (EuclideanSpace ℝ (Fin 3))), IsCompact L' →
          L' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x).target →
          MapCPConvergenceOn L' (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ y ∈ ball (p (φ i)) R,
          ∃ x ∈ ball q (R + 1), dist (j i x) y < ε) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x),
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), ProperSpace W ∧ CompleteSpace W ∧
            ∃ e : N ≃ᵢ WithLp 2 (ℝ × W), e q = WithLp.toLp 2 (a, w) ∧
              ∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C := by
  exact exists_lcons_merge_noncompact K hK hr hv A g hmetric p (Eventually.of_forall hvol)
    hcurv hη hL (Eventually.of_forall hsec) Φ hδ

/-- **LFR16 for noncompact factors on one subsequence (B1 + B2).** -/
theorem exists_lcons_merge_oriented_surfaceCarrier
    (K : ℕ) (hK : 4 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (o : ∀ i, ManifoldOrientation (𝓡 3) (X i) 3)
    (hvol : ∀ᶠ i in atTop, ENNReal.ofReal v ≤ riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {a : ℝ} {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ N) (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N (X (φ i)) K),
        ProperSpace N ∧ (∀ i, j i q = p (φ i)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ e : N ≃ᵢ WithLp 2 (ℝ × W),
            (∀ C : Set N, Bornology.IsBounded C →
              TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                (fun x => (e x).fst) atTop C) ∧
            ∃ (S : Type) (_ : MetricSpace S) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S)
              (_ : IsManifold (𝓡 2) ∞ S),
              CompleteSpace S ∧ ConnectedSpace S ∧ Nonempty (ManifoldOrientation (𝓡 2) S 2) ∧
              Nonempty (S ≃ᵢ W) ∧
              ∃ κ : ContMDiffRiemannianMetric (𝓡 2) ((K - 2 + 1 : ℕ) : ℕ∞ω)
                  (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2) : S → Type _),
                (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w) ∧
                (letI : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) :=
                  ⟨κ.toRiemannianMetric⟩
                 IsRiemannianManifold (𝓡 2) S) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, -, hpt, -, -, hdist, hcov, -,
      -, hsecG, W, m, w, -, -, e, -, hcoord⟩ :=
    exists_lcons_merge_noncompact_oriented K hK hr hv A g hmetric p o hvol hcurv hη hL hsec Φ hδ
  let := mN
  let := cN
  let := m
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x) :=
    ⟨G.toRiemannianMetric⟩
  have _ : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N := hRiem
  have hsec' : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x),
      0 ≤ (finiteMetricReindex K hK G).sectionalCurvature x v w := fun x v w => hsecG x v w
  obtain ⟨S, mS, cS, iS, hc, hconnS, ho, -, -, -, -, ⟨ψ, -⟩, κ, -, hsecS, hR, -⟩ :=
    surfaceFactor_smoothCarrier_oriented_noncompact (finiteMetricReindex K hK G)
      (two_le_reindex K hK) (finiteMetricReindex_enorm K hK G) hsec' oN e
  exact ⟨φ, hφ, N, mN, cN, hMN, q, j, hprop, fun i => (hpt i).2, hdist, hcov, W, m, e, hcoord,
    S, mS, cS, iS, hc, hconnS, ho, ⟨ψ⟩, κ, hsecS, hR⟩

end DifferentialGeometry.CheegerGromovCompactness
