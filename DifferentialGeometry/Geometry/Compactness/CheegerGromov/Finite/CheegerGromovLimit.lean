import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Riemannian.Basic
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Smoothing
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.MarkedPointEvaluation
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import DifferentialGeometry.Topology.Manifold.Orientation
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Collapse.ComparisonImageContainment
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ComparisonAssembly
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ChartCoefficientTransfer
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CompactLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CurvatureSign
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.LimitChartData

/-!
# LFR14: finite-regularity Cheeger–Gromov limit with comparison maps (T0)

Blueprint LFR14, Theorem 13.97 (master207A.tex:25869–26084). The frozen target T0
(`build-logs/scratch/D-LFR14/Target.lean`), verbatim, and two consumers of its output clauses.

* `exists_finite_cheeger_gromov_limit` (T0): a subsequence `φ`, a proper connected smooth carrier
  `N` with a `C^{K-1}` metric `G` realising its distance, a base point `q`, and `C^K` partial
  diffeomorphisms `j i : N → X (φ i)`, pointed for EVERY `i`, whose sources exhaust `N`, with
  `C^{K-1}` convergence of the pulled-back metrics in every extended chart of `N`, distortion
  `→ 0` on balls, the coverage `B(pᵢ,a) ⊆ jᵢ(B(q,b))` for `a < b`, and pointed Gromov–Hausdorff
  convergence.
* `exists_finite_cheeger_gromov_limit_with_compact_case` (T0 + T3): if `N` is compact, eventually
  every `j i` has source and target `univ`.
* `exists_finite_cheeger_gromov_limit_with_nonneg_sectional` (T0 + T2, `3 ≤ K`): under almost
  nonnegative sectional curvature on growing balls, `G` has nonnegative sectional curvature.

Route: the limit chart data I-LIM (`exists_finite_limit_chart_data`, steps 1–3 on the smooth
carrier); the assembly kernel `exists_comparison_maps_of_stage_data` (I-STAGE on the closed balls
`closedBall q (k + 1)`, one diagonal sequence through
`PartialDiffeomorph.exists_exhausting_restrictions`); the transfer
`mapCPConvergenceOn_chartCoeff_of_limit_charts` from the limit charts to the extended charts
(I-CHART on open overlaps); the coverage clause is the LFR10 containment
`eventually_riemannian_ball_subset_image_of_localDiffeomorph`.
-/


set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian

universe u

/-- **T0 — LFR14 (A:25869), main package.** Complete connected smooth pointed `n`-manifolds in the
aligned convention (`hmetric`), basepoint volume `≥ v` on `B(pᵢ,r)` and
`|∇^k Rm| ≤ A(R)` on `B(pᵢ,R)` for `k ≤ K`. A subsequence `φ` has a proper connected pointed limit
`(N, q)` on a SMOOTH carrier with a `C^{K-1}` metric `G` realising its distance, and actual pointed
`C^K` partial diffeomorphisms `j i : N → X (φ i)` (embeddings on their whole open sources) whose
sources exhaust `N`, with `C^{K-1}` chart convergence `j i^* g → G`, pointed distortion `→ 0` on
every ball, and strict-radius coverage `B(pᵢ,a) ⊆ j i (B(q,b))`. -/
theorem exists_finite_cheeger_gromov_limit
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
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
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
          L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) := by
  have hKle : ((K : ℕ) : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, σ, d, D, b, R, ε, F, hprop, hconn, hRiem, hGH, -, hε,
      hcover, h0s, h0q, h0p, hD, htrans, hb, hGb, hchart⟩ :=
    exists_finite_limit_chart_data n K hn hK hr hv A hA g hmetric p
      (fun _ _ => LinearIsometryEquiv.refl ℝ _) hvol hcurv
  let := mN
  let := cN
  have := hMN
  have := hprop
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) K N := IsManifold.of_le hKle
  obtain ⟨j, hpt, hexh, hcoef, hdist, -⟩ :=
    exists_comparison_maps_of_stage_data (Y := fun i => X (φ i)) hK (fun i => g (φ i)) σ d D hD
      htrans b hb q (fun i => p (φ i)) none ⟨h0s, h0q, h0p⟩ R ε F hε hchart hcover
  refine ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, ?_, hdist, ?_⟩
  · intro x L hL hLt
    exact mapCPConvergenceOn_chartCoeff_of_limit_charts hK G (fun i => g (φ i)) σ hcover b
      (fun a => (hb a).1.mono (hD a).2.2.1) hGb j hexh hcoef x hL hLt
  · intro a' b' _ hab
    have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
      ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
    have hloc : ∀ᶠ i in atTop, IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (K : ℕ∞ω) (j i : N → X (φ i)) (ball q b') := by
      filter_upwards [hexh _ (isCompact_closedBall q b')] with i hi
      intro x
      exact (j i).isLocalDiffeomorphAt _ _ _ (hi (ball_subset_closedBall x.2))
    exact Geometry.Metric.eventually_riemannian_ball_subset_image_of_localDiffeomorph
      (fun i => g (φ i)) (fun i => hmetric (φ i)) (fun i => (j i : N → X (φ i))) q
      (fun i => p (φ i)) (fun i => (hpt i).2) hloc (fun η hη => hdist b' η hη) hab

/-- **LFR14 with the compact case (T0 + T3).** The package of
`exists_finite_cheeger_gromov_limit`, and if the limit `N` is compact then eventually every `j i`
is defined on all of `N` and onto `X (φ i)` (a global `C^K` diffeomorphism by
`globalDiffeomorphOfUniv`). -/
theorem exists_finite_cheeger_gromov_limit_with_compact_case
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
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
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
          L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        (CompactSpace N → ∀ᶠ i in atTop, (j i).source = univ ∧ (j i).target = univ) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov⟩ := exists_finite_cheeger_gromov_limit n K hn hK hr hv A hA g hmetric p hvol hcurv
  let := mN
  let := cN
  have : Nonempty N := ⟨q⟩
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist, hcov,
    fun _ => eventually_source_eq_univ_of_compactSpace j hexh⟩

/-- **LFR14 with the curvature sign (T0 + T2).** For `3 ≤ K`, if moreover
`sec_{gᵢ} ≥ -ηᵢ` on `B(pᵢ, Lᵢ)` with `ηᵢ → 0` and `Lᵢ → ∞`, the limit metric `G` of
`exists_finite_cheeger_gromov_limit` has nonnegative sectional curvature. -/
theorem exists_finite_cheeger_gromov_limit_with_nonneg_sectional
    (n K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
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
      SectionalBoundedBelowAt (g i) y (-η i)) :
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
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
          L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          0 ≤ G.sectionalCurvature x v w := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov⟩ := exists_finite_cheeger_gromov_limit n K hn (by omega) hr hv A hA g hmetric p hvol
    hcurv
  let := mN
  let := cN
  have := hMN
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist, hcov,
    sectionalCurvature_nonneg_of_finite_comparison hK (X := fun i => X (φ i)) (fun i => g (φ i))
      (fun i => hmetric (φ i)) (fun i => p (φ i)) G q j hpt hexh hconv hdist
      (hη.comp hφ.tendsto_atTop) (hL.comp hφ.tendsto_atTop) (fun i => hsec (φ i))⟩

end DifferentialGeometry.CheegerGromovCompactness
