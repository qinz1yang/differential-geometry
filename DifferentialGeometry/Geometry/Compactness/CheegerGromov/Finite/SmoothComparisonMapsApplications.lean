import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.SmoothComparisonMaps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CheegerGromovLimit

/-!
# Consumer of LFR48: LFR14 with SMOOTH comparison maps

`exists_finite_cheeger_gromov_limit_with_smooth_comparison_maps`: under the hypotheses of LFR14
(T0, `exists_finite_cheeger_gromov_limit`), the comparison maps can be taken SMOOTH: a subsequence
`φ`, a proper pointed limit `(N, q)` on a smooth carrier with a `C^{K-1}` metric `G`, and smooth
pointed partial diffeomorphisms `jt i : N → X (φ i)` whose sources exhaust `N`, with `C^{K-1}`
chart convergence `jt i^* g → G`, pointed distortion `→ 0` on balls and strict-radius coverage.
This is LFR48 applied to LFR14's maps (`exists_smooth_comparison_maps_of_finite_limit`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing

universe w

/-- **LFR14 with smooth comparison maps (T0 + LFR48).** -/
theorem exists_finite_cheeger_gromov_limit_with_smooth_comparison_maps
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R)
    {X : ℕ → Type w} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ i, ENNReal.ofReal v ≤ Integral.Measure.riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
        (q : N)
        (jt : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) ∞),
        ProperSpace N ∧ ConnectedSpace N ∧
        (∀ i, q ∈ (jt i).source ∧ jt i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (jt i).source) ∧
        (∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
          L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((jt i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (jt i x) (jt i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (jt i : N → X (φ i)) '' ball q b) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, -, -, hpt, hexh, hcoef, hdist, -⟩ :=
    exists_finite_cheeger_gromov_limit n K hn hK hr hv A hA g hmetric p hvol hcurv
  let := mN
  let := cN
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  obtain ⟨jt, hjpt, -, -, hjexh, hjcoef, hjdist, hjcov⟩ :=
    exists_smooth_comparison_maps_of_finite_limit (X := fun i => X (φ i)) hK
      (fun i => g (φ i)) (fun i => hmetric (φ i)) (fun i => p (φ i)) G q j hpt hexh hcoef hdist
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, jt, hprop, hconn, hjpt, hjexh, hjcoef, hjdist, hjcov⟩

end DifferentialGeometry.CheegerGromovCompactness
