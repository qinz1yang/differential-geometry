import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.HalfCollarOfEmbeddingHCOL
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyHalfCollar
import DifferentialGeometry.Topology.Manifold.ImmersionBoundaryOpenHCOL
import DifferentialGeometry.Topology.Manifold.ImmersionPartialDiffeomorphHCOL

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

/-- Interior points of the half-collar model are the points of positive height. -/
theorem isInteriorPoint_halfCollar_iff_CPA2 (q : CuspHalfSpace) :
    halfCollarModel.IsInteriorPoint q ↔ 0 < q.2.val 0 := by
  change q ∈ halfCollarModel.interior CuspHalfSpace ↔ _
  rw [halfCollarModel, ModelWithCorners.interior_prod]
  constructor
  · rintro ⟨-, h⟩
    have h' : (𝓡∂ 1).IsInteriorPoint q.2 := h
    rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace] at h'
    exact h'
  · intro h
    refine ⟨?_, ?_⟩
    · rw [ModelWithCorners.interior_eq_univ]; trivial
    · change (𝓡∂ 1).IsInteriorPoint q.2
      rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace]
      exact h

/-- The height coordinate functional on the model space of the half collar. -/
def heightFunctional_CPA2 : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
    EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ :=
  (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))

theorem heightFunctional_ne_zero_CPA2 : heightFunctional_CPA2 ≠ 0 := by
  intro h
  have := congrArg (fun L : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ => L ((0, 0), EuclideanSpace.single 0 1)) h
  simp [heightFunctional_CPA2] at this

/-- **Interior chart of a cusp embedding.** A smooth embedding of the half collar into a
`3`-manifold is a partial diffeomorphism on the open set of positive height. -/
theorem exists_interior_partialDiffeomorph_CPA2 {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N] [Nonempty CuspHalfSpace]
    {e : CuspHalfSpace → N} (he : IsSmoothEmbedding halfCollarModel (𝓡 3) ∞ e) :
    ∃ d : PartialDiffeomorph halfCollarModel (𝓡 3) CuspHalfSpace N ∞,
      d.source = {q | 0 < q.2.val 0} ∧ d.target = e '' {q | 0 < q.2.val 0} ∧
        (d : CuspHalfSpace → N) = e := by
  have hS : IsOpen {q : CuspHalfSpace | 0 < q.2.val 0} :=
    isOpen_lt continuous_const
      ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
  refine exists_partialDiffeomorph_of_open_injOn_immersion_HCOL hS
    (fun y _ => he.isImmersion.isImmersionAt y) ?_ he.isEmbedding.injective.injOn
  intro y hy
  refine IsImmersionAt.nhds_le_map_of_halfSpace_HCOL (I := halfCollarModel) (J := 𝓡 3)
    (by simp [Module.finrank_prod]) ⟨heightFunctional_CPA2, heightFunctional_ne_zero_CPA2, ?_⟩
    (Or.inl ModelWithCorners.Boundaryless.range_eq_univ) (he.isImmersion.isImmersionAt y) ?_
  · exact DifferentialGeometry.Topology.HalfCollarHCOL.range_halfCollarModel_HCOL
  · intro hb
    exfalso
    have hint := (isInteriorPoint_halfCollar_iff_CPA2 y).mpr hy
    exact Set.disjoint_left.mp (halfCollarModel.disjoint_interior_boundary (M := CuspHalfSpace))
      hint hb

end GC.LongTime.CuspP1
