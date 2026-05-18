import DifferentialGeometry.Geometry.Riemannian.Geodesic.Homogeneity

set_option linter.unusedSectionVars false

/-!
# Geodesic completeness

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the metric `g` is
**geodesically complete** iff every maximal geodesic is defined on the
entire real line: for every initial datum `(p : M, v : T_p M)`, the
maximal interval `maximalGeodesicInterval g p v` equals `Set.univ`.

## Main definitions

* `GeodesicallyComplete g` — the predicate above.

## Main theorems

* `GeodesicallyComplete.zero_velocity_interval` — the maximal interval at
  zero velocity is always `Set.univ`. Hence the zero-velocity component
  of geodesic completeness is automatically satisfied; only nonzero
  initial velocities can obstruct completeness.

* `GeodesicallyComplete.iff_maximalGeodesic_total` — `g` is geodesically
  complete iff for every `(p, v)` every `t : ℝ` belongs to the maximal
  interval.

## Strategy

`GeodesicallyComplete g` is unfolded straight from
`maximalGeodesicInterval`. The zero-velocity case is a thin
reformulation of `maximalGeodesicInterval_zero_velocity` (shipped in
`Geodesic/Homogeneity.lean`) under the `TangentSpace I p`-typing of the
velocity slot. The iff is unfolding `S = Set.univ ↔ ∀ t, t ∈ S` via
`Set.eq_univ_iff_forall`.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace Geometry
namespace Riemannian
namespace Completeness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The geodesic-completeness predicate -/

/-- A smooth Riemannian metric `g` on `M` is **geodesically complete** iff
every maximal geodesic is defined on all of `ℝ`. Concretely: for every
point `p : M` and every initial velocity `v : T_p M`, the maximal
interval `maximalGeodesicInterval g p v` is the entire real line. -/
def GeodesicallyComplete (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ (p : M) (v : TangentSpace I p),
    maximalGeodesicInterval (I := I) g p v = Set.univ

/-! ## The zero-velocity case -/

section ZeroVelocity

variable [I.Boundaryless] [CompleteSpace E]

/-- **Zero-velocity completeness.** At every base point `p : M`, the
maximal interval at zero initial velocity is the whole real line: the
constant curve at `p` is a global geodesic with zero initial velocity.

This is `maximalGeodesicInterval_zero_velocity` re-exposed under the
`TangentSpace I p`-typing of the velocity slot used in
`GeodesicallyComplete`; `TangentSpace I p` reduces to `E` definitionally
at every base point. -/
theorem GeodesicallyComplete.zero_velocity_interval
    (g : SmoothRiemannianMetric I M) (p : M) :
    maximalGeodesicInterval (I := I) g p (0 : TangentSpace I p) = Set.univ := by
  change maximalGeodesicInterval (I := I) g p (0 : E) = Set.univ
  exact maximalGeodesicInterval_zero_velocity (I := I) g p

end ZeroVelocity

/-! ## Pointwise characterisation -/

/-- **Completeness as pointwise total domain.** `g` is geodesically
complete iff every real number lies in every maximal interval: the
condition `maximalGeodesicInterval g p v = Set.univ` is just the
pointwise statement `∀ t, t ∈ maximalGeodesicInterval g p v`. -/
theorem GeodesicallyComplete.iff_maximalGeodesic_total
    {g : SmoothRiemannianMetric I M} :
    GeodesicallyComplete (I := I) g ↔
      ∀ (p : M) (v : TangentSpace I p),
        ∀ t : ℝ, t ∈ maximalGeodesicInterval (I := I) g p v := by
  unfold GeodesicallyComplete
  refine ⟨?_, ?_⟩
  · intro h p v t
    rw [h p v]
    exact Set.mem_univ t
  · intro h p v
    exact Set.eq_univ_of_forall (h p v)

end Completeness
end Riemannian
end Geometry

end
