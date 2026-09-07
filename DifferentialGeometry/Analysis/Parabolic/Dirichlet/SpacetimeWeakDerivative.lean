import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientProduct

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

theorem eLpNorm_diffQuot_dirichletLocalSpacetimeLp_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω' Ω'' : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (u : Lp (H1ComplDirichlet q) 2 μ) (k : Fin (Module.finrank ℝ EuN))
    {h0 : ℝ} (hh0 : 0 < h0) (hthick : Metric.cthickening h0 (closure Ω'') ⊆ Ω')
    {h : ℝ} (hh : |h| ≤ h0) :
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) μ u
    let DU := dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ k u
    eLpNorm (fun p : Z × EuStd => Sobolev.diffQuot k h (fun x => U (p.1, x)) p.2)
        2 (μ.prod (volume.restrict Ω'')) ≤
      eLpNorm DU 2 (μ.prod (volume.restrict Ω')) := by
  apply Sobolev.eLpNorm_spatial_diffQuot_le_eLpNorm_weakPartial_local hΩ hΩ' hΩ'' hΩ'c
    hΩ'Ω hΩ''c μ
  · exact hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ k u
  · exact hh0
  · exact hthick
  · exact hh

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
