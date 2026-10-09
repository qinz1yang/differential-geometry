import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.SplittingLimitMerge
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.FiniteLimitSplitting

/-!
# LFR15: the same finite model tracks the actual splitting (the row)

Chapter 13, row LFR15 (`cor:collapse-finite-model-splitting-producer`, A:26086). Under LFR14's
hypotheses with the expanding-ball sectional lower bounds and normalized `(j, δᵢ)`-splittings
`Φᵢ : Xᵢ → F × Zᵢ` (`F` Euclidean of dimension `j`, `δᵢ → 0`), along ONE subsequence the SAME
complete finite limit `(N, G)` (order `K - 1`, `K ≥ 4`, with LFR14's actual comparison maps
`jᵢ` and their `C^{K-1}` metric convergence) is nonnegatively curved and is an exact product
`e : N ≃ᵢ F × W`, with `(Φᵢ ∘ jᵢ)_F → t = e_F` uniformly on bounded sets; by LFR11 at order
`K - 1` the factor `Z = t⁻¹(0)` is a complete nonnegatively curved `C^{K-1}` Riemannian manifold
with a `C^K` atlas and the actual product map is a `C^K` diffeomorphism with `Ψ^* G = du² + h`
(`exists_finite_model_exact_splitting`).

The orientation sentence of LFR15 (oriented sources) needs the oriented limit of LFR14 on the same
subsequence; it is delivered separately, together with the LFR16 row.
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

/-- **LFR15 (row).** One subsequence and one finite limit carry T0's package, `sec_G ≥ 0`, the exact
product `e : N ≃ᵢ F × W` tracked by the actual maps (`(Φ_{φ i} ∘ jᵢ)_F → e_F` uniformly on bounded
sets), and LFR11's product regularity at order `K - 1` for that actual isometry. -/
theorem exists_finite_model_exact_splitting
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
               ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, F)
                 ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) (fun x => (e x).fst) ∧
               IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ)
                 ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
               (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ
                     (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ) :
                   {x : N // (e x).fst = 0} → Type _) :=
                 ⟨(inducedMetric (finiteOrderMetricReindex K hK G) (two_le_finiteOrderReindex K hK)
                   (finiteOrderMetricReindex_enorm K hK G) e).toRiemannianMetric⟩
                IsRiemannianManifold 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ) {x : N // (e x).fst = 0}) ∧
               CompleteSpace {x : N // (e x).fst = 0} ∧
               (∀ (z : {x : N // (e x).fst = 0})
                 (v w : TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ) z),
                 0 ≤ (inducedMetric (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G)
                   e).sectionalCurvature z v w) ∧
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
               (∀ p : F × {x : N // (e x).fst = 0},
                 splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p =
                   e.symm (toLp 2 (p.1, (e p.2.val).snd))) ∧
               (∀ (p : F × {x : N // (e x).fst = 0})
                 (v w : TangentSpace ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                   (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ)) p),
                 G.inner (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                     (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p)
                   (mfderiv ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                       (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ))
                     𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                     (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                       (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e)
                     p v)
                   (mfderiv ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                       (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ))
                     𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                     (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                       (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e)
                     p w) =
                 inner ℝ v.1 w.1 + (inducedMetric (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G)
                   e).inner p.2 v.2 w.2)) := by
  have hne : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord⟩ :=
    exists_finite_cheeger_gromov_limit_with_nonneg_splitting n K hn (by omega) hr hv A hA g
      hmetric p hvol hcurv hη hL hsec Φ hδ
  let := mN
  let := cN
  let := m
  obtain ⟨hT, hZ, hRZ, hcZ, hsecZ, hΨ, hΨs, hΨe, hΨm⟩ :=
    exactSplitting_of_finite_limit K hK G hRiem e
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hRiem, hconn, hGH, hpt, hexh, hconv, hdist, hcov,
    hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord, hT, hZ, hRZ, hcZ, hsecZ hsecG, hΨ, hΨs, hΨe,
    hΨm⟩

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
