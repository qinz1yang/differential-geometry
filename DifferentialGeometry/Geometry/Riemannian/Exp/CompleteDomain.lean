import DifferentialGeometry.Geometry.Riemannian.Exp.Basic
import DifferentialGeometry.Geometry.Riemannian.Completeness.Defs

set_option linter.unusedSectionVars false

/-!
# Domain of the exponential map under geodesic completeness

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, geodesic completeness
forces the exponential map to be defined on the entire tangent space at
every point.

## Main results

* `GeodesicallyComplete.mem_expDomain` — under geodesic completeness,
  every tangent vector at every point lies in the domain of the
  exponential map.
* `GeodesicallyComplete.expDomain_eq_univ` — under geodesic
  completeness, the domain of the exponential map at every point is the
  entire tangent space.
* `expDomain_zero_velocity` — the zero scalar multiple of any tangent
  vector lies in the domain of the exponential map (unconditional on
  completeness).

## Strategy

`GeodesicallyComplete g` is by definition the statement that
`maximalGeodesicInterval g p v = Set.univ` for every `(p, v)`. The
membership `v ∈ expDomain g p` unfolds (via `mem_expDomain_iff`) to
`(1 : ℝ) ∈ maximalGeodesicInterval g p v`, which then follows from
`Set.mem_univ`. The set-level identity `expDomain g p = Set.univ`
follows by `Set.eq_univ_of_forall`. The zero-velocity corollary uses
`zero_smul` to reduce `(0 : ℝ) • v` to `0` and then invokes
`zero_mem_expDomain`.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exp
open Geometry.Riemannian.Completeness

namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Geodesic completeness exhausts the exponential domain -/

namespace Completeness

section CompleteDomain

variable [I.Boundaryless] [CompleteSpace E]

/-- **Under geodesic completeness, every tangent vector is in the
exponential domain.** If `g` is geodesically complete, then for every
point `p : M` and every tangent vector `v : T_p M`, the vector `v` lies
in `expDomain g p`. The proof unfolds membership to
`(1 : ℝ) ∈ maximalGeodesicInterval g p v` and applies the hypothesis
`maximalGeodesicInterval g p v = Set.univ`. -/
theorem GeodesicallyComplete.mem_expDomain
    {g : SmoothRiemannianMetric I M}
    (hCom : GeodesicallyComplete (I := I) g) (p : M) (v : TangentSpace I p) :
    v ∈ expDomain (I := I) g p := by
  rw [mem_expDomain_iff]
  rw [hCom p v]
  exact Set.mem_univ _

/-- **Under geodesic completeness, the exponential domain is the entire
tangent space.** If `g` is geodesically complete, then for every point
`p : M`, the domain of the exponential map at `p` is `Set.univ`. -/
theorem GeodesicallyComplete.expDomain_eq_univ
    {g : SmoothRiemannianMetric I M}
    (hCom : GeodesicallyComplete (I := I) g) (p : M) :
    expDomain (I := I) g p = Set.univ :=
  Set.eq_univ_of_forall
    (fun v => GeodesicallyComplete.mem_expDomain (I := I) hCom p v)

end CompleteDomain

end Completeness

/-! ## Zero-velocity corollary -/

namespace Exp

section ZeroVelocity

variable [I.Boundaryless] [CompleteSpace E]

/-- **Zero scalar multiple of any tangent vector is in the exponential
domain.** For every `p : M` and `v : T_p M`, the vector `(0 : ℝ) • v`
lies in `expDomain g p`. This reduces to `zero_mem_expDomain` after
simplifying `(0 : ℝ) • v` to `0` via `zero_smul`. The statement is
unconditional on geodesic completeness: it only uses the standing
`[I.Boundaryless] [CompleteSpace E]` hypotheses. -/
theorem expDomain_zero_velocity
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (0 : ℝ) • v ∈ expDomain (I := I) g p := by
  -- `(0 : ℝ) • v = 0` in any module; reduces to `zero_mem_expDomain`.
  have hzero : ((0 : ℝ) • v) = (0 : TangentSpace I p) := zero_smul ℝ v
  rw [hzero]
  exact zero_mem_expDomain (I := I) g p

end ZeroVelocity

end Exp

end Riemannian
end Geometry

end
