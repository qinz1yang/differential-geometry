import DifferentialGeometry.Geometry.Collapse.FiniteCategory.FiniteModelSplitting

/-!
# Consumers of the L-CONS merge and of the LFR15 row

* `lfr16_lcons_merge`: the merge statement requested for the LFR16 row
  (build-logs/resume/sheet-F7-LFR11b.md §7, `lfr16_lcons_merge_Stmt`), verbatim, for
  three-dimensional sources and a line factor (from `exists_finite_cheeger_gromov_limit_with_compact_splitting`).
* `exists_finite_model_line_splitting_factor`: LFR15 for a line factor (`F = ℝ`): the factor of the
  limit is complete and nonnegatively curved, and the actual product map is `C^K`.
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

universe u w

/-- **The L-CONS merge for LFR16** (`lfr16_lcons_merge_Stmt` of sheet-F7-LFR11b §7). -/
theorem lfr16_lcons_merge (K : ℕ) (hK : 4 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i), SectionalBoundedBelowAt (g i) y (-η i))
    {a : ℝ} {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) {D : ℝ} (hD : ∀ i, ∀ x y : Z i, dist x y ≤ D) :
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
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x),
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), CompactSpace W ∧ (∀ x y : W, dist x y ≤ D) ∧
            ∃ e : N ≃ᵢ WithLp 2 (ℝ × W), e q = WithLp.toLp 2 (a, w) ∧
              ∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      -, hsecG, W, m, w, -, hcpt, hdiam, -, e, he, hcoord⟩ :=
    exists_finite_cheeger_gromov_limit_with_compact_splitting 3 K (by norm_num) (by omega) hr hv
      A g hmetric p hvol hcurv hη hL hsec Φ hδ hD
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
    hsecG, W, m, w, hcpt, hdiam, e, he, hcoord⟩

/-- **LFR15 for a line factor.** The factor `Z` of the exact line splitting of the LFR15 limit is
complete and nonnegatively curved for its induced metric, and the actual product map
`ℝ × Z → N` is `C^K`. -/
theorem exists_finite_model_line_splitting_factor
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
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i), SectionalBoundedBelowAt (g i) y (-η i))
    {a : ℝ} {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
        (_ : ProperSpace N)
        (hRiem : letI : RiemannianBundle (fun x : N =>
            TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := ⟨G.toRiemannianMetric⟩
          IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)
        (W : Type) (m : MetricSpace W) (e : N ≃ᵢ WithLp 2 (ℝ × W)),
        letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
          ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
        letI : RiemannianBundle (fun x : N =>
          TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := ⟨G.toRiemannianMetric⟩
        letI : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N := hRiem
        letI := splittingFactorChartedSpace (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
        letI := splittingFactor_isManifold_one (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
        CompleteSpace {x : N // (e x).fst = 0} ∧
        (∀ (z : {x : N // (e x).fst = 0})
          (v w : TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
            Module.finrank ℝ ℝ) → ℝ) z),
          0 ≤ (inducedMetric (finiteOrderMetricReindex K hK G) (two_le_finiteOrderReindex K hK)
            (finiteOrderMetricReindex_enorm K hK G) e).sectionalCurvature z v w) ∧
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
            Module.finrank ℝ ℝ) → ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
          (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
            (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) := by
  obtain ⟨-, -, N, mN, cN, hMN, G, -, -, hprop, hRiem, -, -, -, -, -, -, -, -, W, m, -, -, -, -,
      e, -, -, -, -, -, hcZ, hsecZ, hΨ, -, -, -⟩ :=
    exists_finite_model_exact_splitting n K hn hK hr hv A hA g hmetric p hvol hcurv hη hL hsec Φ hδ
  exact ⟨N, mN, cN, hMN, G, hprop, hRiem, W, m, e, hcZ, hsecZ, hΨ⟩

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
