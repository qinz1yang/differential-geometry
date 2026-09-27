import DifferentialGeometry.Geometry.Curvature.ContinuousEvaluation
import DifferentialGeometry.Geometry.Metric.UnitTangentPair

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]


def orthonormalPairCurvature (g : SmoothRiemannianMetric I M) (p : OrthonormalTangentPair g) : ℝ :=
  metricRm04StandardAt g (SameBaseUnitTangentPair.base g p.val)
    (SameBaseUnitTangentPair.first g p.val) (SameBaseUnitTangentPair.second g p.val)
    (SameBaseUnitTangentPair.second g p.val) (SameBaseUnitTangentPair.first g p.val)


theorem orthonormalPairCurvature_continuous (g : SmoothRiemannianMetric I M) :
    Continuous (orthonormalPairCurvature g) :=
  (continuous_sectional_contraction g (SameBaseUnitTangentPair.base g)
    (SameBaseUnitTangentPair.continuous_base g)
    (SameBaseUnitTangentPair.first g) (SameBaseUnitTangentPair.second g)
    (SameBaseUnitTangentPair.continuous_first g) (SameBaseUnitTangentPair.continuous_second g)).comp
      continuous_subtype_val

theorem HasPositiveSectionalCurvature.exists_uniform_orthonormal_bound [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (hg : HasPositiveSectionalCurvature g) :
    ∃ k : ℝ, 0 < k ∧ ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v v = 1 → g.inner x w w = 1 → g.inner x v w = 0 →
        k ≤ metricRm04StandardAt g x v w w v := by
  let := orthonormalTangentPair_compactSpace g
  have hpos (p : OrthonormalTangentPair g) : 0 < orthonormalPairCurvature g p :=
    hg _ _ _ (tangent_pair_linearIndependent_of_orthonormal g _ _ _
      (SameBaseUnitTangentPair.unit g p.val).1 (SameBaseUnitTangentPair.unit g p.val).2 p.property)
  by_cases hn : Nonempty (OrthonormalTangentPair g)
  · obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn
      (Set.nonempty_iff_univ_nonempty.mp hn) (orthonormalPairCurvature_continuous g).continuousOn
    refine ⟨orthonormalPairCurvature g p, hpos p, ?_⟩
    intro x v w hv hw hvw
    let q : OrthonormalTangentPair g :=
      ⟨⟨(⟨⟨x, v⟩, hv⟩, ⟨⟨x, w⟩, hw⟩), rfl⟩, hvw⟩
    exact (isMinOn_iff.mp hp) q (mem_univ q)
  · refine ⟨1, one_pos, ?_⟩
    intro x v w hv hw hvw
    exact False.elim (hn ⟨⟨⟨(⟨⟨x, v⟩, hv⟩, ⟨⟨x, w⟩, hw⟩), rfl⟩, hvw⟩⟩)

end DifferentialGeometry.Geometry
