import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem integral_dirichletLocalSpacetimeLp_fderiv
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (μ : Measure Z) [IsLocallyFiniteMeasure μ] (i : Fin (Module.finrank ℝ EuN))
    (u : Lp (H1ComplDirichlet q) 2 μ)
    (φ : Z × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ (univ : Set Z) ×ˢ Ω) :
    (∫ p, dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) μ u p *
      fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂μ.prod (volume.restrict Ω)) =
      -∫ p, dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i u p * φ p
        ∂μ.prod (volume.restrict Ω) := by
  apply Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
    (Lp.memLp _ |>.locallyIntegrable (by norm_num))
    (Lp.memLp _ |>.locallyIntegrable (by norm_num)) i
    (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i u)
    φ hφ hφc hφs

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
