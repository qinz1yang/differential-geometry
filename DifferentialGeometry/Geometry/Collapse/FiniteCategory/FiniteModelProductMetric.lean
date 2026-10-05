import DifferentialGeometry.Geometry.Collapse.FiniteCategory.FiniteModelSplitting
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.FiniteLimitProductMetric

/-!
# R2 on the LFR15 limit (input of LFR18 / LFR20)

The recorded missing statement (R2) of build-logs/worker-F7-DOWN.md: "the LFR15 limit `N` carries
a `C^{K-1}` product metric `dt² + k` on `ℝ × Z`, `Z` a `C^{K-1}` surface, with `Φ` its distance
isometry", here for any dimension `n` and any Euclidean factor `F`:
`exists_finite_model_product_metric` — on the SAME limit as LFR15 (T0's package, `sec ≥ 0`, the
exact splitting `e` tracked by the actual maps), `Z` is a `C^K` manifold, the actual product map
`Ψ : F × Z → N` is a `C^K` diffeomorphism, the `C^{K-1}` product metric `κ = du² + h` on `F × Z`
equals `Ψ^* G`, its Riemannian distance is the `ℓ²` distance, and `Ψ` is a distance isometry.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse.FiniteCategory

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.ExactSplitting
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

universe u v w

/-- **R2 on the LFR15 limit.** -/
theorem exists_finite_model_product_metric
    (n K : ℕ) (hn : 2 ≤ n) (hK : 4 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {a : F} {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
        (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K)
        (_ : ProperSpace N)
        (hRiem : letI : RiemannianBundle (fun x : N =>
            TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := ⟨G.toRiemannianMetric⟩
          IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N),
        ConnectedSpace N ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L' : Set (EuclideanSpace ℝ (Fin n))), IsCompact L' →
          L' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L' (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), ProperSpace W ∧ CompleteSpace W ∧
            PointedGHConverges (fun i => b (φ i)) w ∧
            ∃ e : N ≃ᵢ WithLp 2 (F × W), e q = WithLp.toLp 2 (a, w) ∧
              (∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C) ∧
              (letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
                 ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
               letI : RiemannianBundle (fun x : N =>
                   TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := ⟨G.toRiemannianMetric⟩
               letI : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N := hRiem
               letI := splittingFactorChartedSpace (finiteOrderMetricReindex K hK G)
                 (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
               letI := splittingFactor_isManifold_one (finiteOrderMetricReindex K hK G)
                 (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
               IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ)
                 ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
               ContMDiff ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                 ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
                 (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) ∧
               ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                 ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ))
                 ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
                 (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e).symm ∧
               (letI : RiemannianBundle (TangentSpace ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                     (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ)) :
                   F × {x : N // (e x).fst = 0} → Type _) :=
                 ⟨(splittingProductMetric (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e).toRiemannianMetric⟩
                (∀ (p : F × {x : N // (e x).fst = 0})
                  (v w : TangentSpace ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                    (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ)) p),
                  (splittingProductMetric (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e).inner p v w =
                    inner ℝ v.1 w.1 + (inducedMetric (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e).inner p.2 v.2 w.2) ∧
                (∀ (p : F × {x : N // (e x).fst = 0})
                  (v w : TangentSpace ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                    (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ)) p),
                  G.inner (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p)
                    (mfderiv ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                        (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ))
                      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) p v)
                    (mfderiv ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                        (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ))
                      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) p w) =
                    (splittingProductMetric (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e).inner p v w) ∧
                (∀ p q : F × {x : N // (e x).fst = 0},
                  riemannianEDist ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                    (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ)) p q =
                    edist (toLp 2 p) (toLp 2 q)) ∧
                (∀ p q : F × {x : N // (e x).fst = 0},
                  dist (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p)
                    (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e q) =
                    dist (toLp 2 p) (toLp 2 q)))) := by
  have hne : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hRiem, hconn, hGH, hpt, hexh, hconv, hdist, hcov,
      hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord, -, hZ, -, -, -, hΨ, hΨs, -, -⟩ :=
    exists_finite_model_exact_splitting n K hn hK hr hv A hA g hmetric p hvol hcurv hη hL hsec Φ hδ
  let := mN
  let := cN
  let := m
  have hR2 := finiteLimit_productMetric K hK G hRiem e
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hRiem, hconn, hGH, hpt, hexh, hconv, hdist, hcov,
    hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord, hZ, hΨ, hΨs, hR2⟩

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
