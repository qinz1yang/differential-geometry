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
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.OrientationTransfer
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.OrientedLimitChartData

/-!
# LFR14: finite-regularity Cheeger–Gromov limit, oriented sources (T1)

Blueprint LFR14, Theorem 13.97 (master207A.tex:25869–26084), orientation clause of step 5. The
frozen target T1 (`build-logs/scratch/D-LFR14/Target.lean`), verbatim.

* `exists_finite_cheeger_gromov_limit_oriented` (T1): the package of T0 for oriented sources, with
  an orientation `oN` of the limit carrier such that eventually every `j i` preserves orientation
  at every point of its source.

Route: as T0, with the oriented limit chart data I-LIM-OR
(`exists_finite_limit_chart_data_oriented`: the chart parametrizations `σ a` and the source charts
`d a i` are oriented against one orientation `oE` of the model). The assembly kernel
`exists_comparison_maps_of_stage_data` gives, eventually and at every point of the source of `j i`,
a positive Jacobian of the chart representation `(d a i)⁻¹ ∘ j i ∘ σ a` (a clause of the stage
predicate, so it holds on the whole growing source), and `orientation_map_mfderiv_eq_of_det_pos`
turns it into orientation preservation.
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

/-- **T1 — LFR14, oriented sources.** As T0, for sources with given orientations `o i`; in addition
`N` carries an orientation `oN` and eventually every `j i` preserves orientation at every point of
its source. -/
theorem exists_finite_cheeger_gromov_limit_oriented
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
    (o : ∀ i, ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i) n)
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
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K)
        (oN : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N n),
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
        (∀ᶠ i in atTop, ∀ (x : N) (hx : x ∈ (j i).source),
          Orientation.map (Fin n)
            (((j i).isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
              (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK)).toLinearEquiv (oN.orientation x) =
            (o (φ i)).orientation (j i x)) := by
  have hKle : ((K : ℕ) : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, σ, d, D, b, R, ε, F, hprop, hconn, hRiem, hGH, -, hε,
      hcover, h0s, h0q, h0p, hD, htrans, hb, hGb, hchart, oE, oN, hσo, hdo⟩ :=
    exists_finite_limit_chart_data_oriented n K hn hK hr hv A hA g hmetric p o hvol hcurv
  let := mN
  let := cN
  have := hMN
  have := hprop
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) K N := IsManifold.of_le hKle
  obtain ⟨j, hpt, hexh, hcoef, hdist, hjac⟩ :=
    exists_comparison_maps_of_stage_data (Y := fun i => X (φ i)) hK (fun i => g (φ i)) σ d D hD
      htrans b hb q (fun i => p (φ i)) none ⟨h0s, h0q, h0p⟩ R ε F hε hchart hcover
  refine ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, hGH, hpt, hexh, ?_, hdist, ?_,
    ?_⟩
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
  · filter_upwards [hjac] with i hi x hx
    obtain ⟨a, u, hu, hσu, ht, hdet⟩ := hi x hx
    exact orientation_map_mfderiv_eq_of_det_pos hK0 oE oN (o (φ i)) (σ a) (d a i) (hσo a)
      (hdo a i) (j i) hx hu hσu ht hdet

end DifferentialGeometry.CheegerGromovCompactness
