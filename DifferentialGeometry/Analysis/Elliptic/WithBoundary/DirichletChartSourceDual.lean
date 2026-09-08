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
theorem exists_lp_chart_divergence_dual
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω))) :
    ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ, ∀ η : Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
      (∫ t, η t * ℓ t v ∂μ) =
        ∑ j, ∫ p, η p.1 * F j p *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v p.2 ∂μ.prod (volume.restrict Ω) := by
  classical
  have hparts (j : Fin (Module.finrank ℝ EuN)) :=
    MeasureTheory.Lp.exists_lp_dual_integral_prod
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j) (F j)
  choose L hL using hparts
  refine ⟨∑ j, L j, ?_⟩
  intro η v
  have hint (j : Fin (Module.finrank ℝ EuN)) : Integrable (fun t => η t * L j t v) μ := by
    exact (Lp.memLp η).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp (L j))
  calc
    (∫ t, η t * (∑ j, L j) t v ∂μ) = ∫ t, ∑ j, η t * L j t v ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_finsetSum Finset.univ L] with t ht
      rw [ht]
      simp only [Finset.sum_apply]
      change η t * ((ContinuousLinearMap.apply ℝ ℝ v) (∑ j, L j t)) = _
      rw [map_sum, Finset.mul_sum]
      rfl
    _ = ∑ j, ∫ t, η t * L j t v ∂μ := integral_finsetSum _ (fun j _ => hint j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hL j η v]
      apply integral_congr_ae
      filter_upwards with p
      simp only [Real.inner_apply, mul_assoc]
end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
