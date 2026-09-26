import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CanonicalWitnessPositiveAge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessProjection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

theorem PartialStandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_age
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C τmin : ℝ, 1 ≤ C ∧ 0 < τmin ∧ ∀ (S : PartialStandardSolution)
      (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ), t ∈ S.domain → t < 1 →
        τmin ≤ t * metricScalarAt (S.metric t) x →
          ∃ W : SpatialCanonicalWitness (S.metric t) eps C C x, W.capTubeHasNeckChart eps := by
  obtain ⟨C, τmin, hC, hτ, hK⟩ :=
    exists_canonicalWitness_with_cap_neck_charts_of_age heps hsmall
  refine ⟨C, τmin, hC, hτ, fun S x t ht ht1 hage => ?_⟩
  obtain ⟨K, hK⟩ := hK S x t ht ht1 hage
  exact ⟨K.toSpatial, K.capTubeHasNeckChart_toSpatial hK⟩

def StandardSolution.YoungSpatiallyCanonical (Θ eps C τmin : ℝ) : Prop :=
  ∀ (S : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ), t ∈ Icc 0 Θ →
    t * metricScalarAt (S.val.metric t) x < τmin →
      ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x, W.capTubeHasNeckChart eps

theorem StandardSolution.mem_domain_of_mem_Icc (S : StandardSolution) {Θ t : ℝ} (hΘ : Θ < 1)
    (ht : t ∈ Icc 0 Θ) : t ∈ S.val.domain := by
  refine (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr ⟨ht.1, ?_⟩
  rw [S.lifetime_eq_one, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (ht.2.trans_lt hΘ)

theorem StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_young
    {eps Θ : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hΘ : Θ < 1)
    (hyoung : ∀ τmin : ℝ, 0 < τmin →
      ∃ C : ℝ, 1 ≤ C ∧ StandardSolution.YoungSpatiallyCanonical Θ eps C τmin) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      t ∈ Icc 0 Θ →
        ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x, W.capTubeHasNeckChart eps := by
  obtain ⟨Cold, τmin, hCold, hτ, hold⟩ :=
    PartialStandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_age heps hsmall
  obtain ⟨Cyoung, hCyoung, hyoung⟩ := hyoung τmin hτ
  refine ⟨max Cold Cyoung, hCold.trans (le_max_left _ _), fun S x t ht => ?_⟩
  rcases le_or_gt τmin (t * metricScalarAt (S.val.metric t) x) with hage | hage
  · obtain ⟨W, hW⟩ := hold S.val x t (S.mem_domain_of_mem_Icc hΘ ht) (ht.2.trans_lt hΘ) hage
    exact ⟨W.enlargeConstants (le_max_left _ _) (le_max_left _ _),
      hW.enlarge_constants (le_max_left _ _) (le_max_left _ _)⟩
  · obtain ⟨W, hW⟩ := hyoung S x t ht hage
    exact ⟨W.enlargeConstants (le_max_right _ _) (le_max_right _ _),
      hW.enlarge_constants (le_max_right _ _) (le_max_right _ _)⟩

end DifferentialGeometry.PDE.RicciFlow
