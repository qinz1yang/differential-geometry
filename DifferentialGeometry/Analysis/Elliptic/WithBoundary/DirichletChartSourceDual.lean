import DifferentialGeometry.Analysis.Integration.Lp.SpacetimeDual
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff
noncomputable section
open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology InnerProductSpace
namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure
variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))
private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd := WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem exists_lp_chart_source_dual
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (F : Lp ℝ 2 (μ.prod (volume.restrict Ω))) :
    ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ, ∀ η : Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
      (∫ t, η t * ℓ t v ∂μ) =
        ∫ p, η p.1 * F p * H1ComplDirichletToLp q v
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω) := by
  let J : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
    (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  obtain ⟨ℓ, hℓ⟩ := MeasureTheory.Lp.exists_lp_dual_integral_prod J F
  refine ⟨ℓ, ?_⟩
  intro η v
  rw [hℓ η v]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd (μ := μ)
      (ν := volume.restrict Ω).ae
      (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q v))] with p hp
  change η p.1 * inner ℝ (F p)
    ((chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2) (H1ComplDirichletToLp q v) p.2) = _
  rw [hp]
  simp only [Real.inner_apply, mul_assoc]
end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
