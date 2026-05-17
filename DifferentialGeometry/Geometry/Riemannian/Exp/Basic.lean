import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Homogeneity

set_option linter.unusedSectionVars false

/-!
# The exponential map of a smooth Riemannian metric

For a smooth Riemannian metric `g` on a smooth manifold `M`, the
exponential map at a point `p : M`, applied to a tangent vector
`v : T_p M`, is the value at `t = 1` of the unique maximal geodesic of
`g` with initial data `(p, v)`:
$$\exp_p(v) := \gamma_{p, v}(1).$$
Its natural domain of definition is the set of `v` for which the
maximal geodesic extends to time `1`.

## Main definitions

* `expMap g p v` — the exponential map, defined unconditionally via the
  junk-extended canonical maximal geodesic `maximalGeodesic g p v`. When
  `v ∉ expDomain g p` the value is junk (equal to `p`).
* `expDomain g p` — the domain of `expMap g p`: the set of tangent
  vectors `v` for which `1` lies in the maximal interval of definition.

## Main results

* `mem_expDomain_iff` / `mem_expDomain_iff_witness`: characterisations
  of domain membership.
* `zero_mem_expDomain`: the zero vector belongs to the domain.
* `expDomain_nonempty`: the domain is nonempty.
* `expMap_of_not_mem`: outside the domain, the exponential map takes
  the junk value `p`.

## Note on `expMap_zero`

The structural identity `expMap g p 0 = p` (i.e.
`maximalGeodesic g p (0 : E) 1 = p`) reduces to the propagation
statement that any integral curve of the chart-fixed geodesic vector
field `geodesicVectorFieldChart g α` starting at the zero-section
point `⟨p, 0⟩` is the constant lift `fun _ => ⟨p, 0⟩` on its open
domain of definition. The existing local uniqueness lemma in
`Geodesic/Uniqueness.lean` delivers `eventuallyEq`; lifting this to a
clopen-set propagation on the connected component of the witness
interval calls for an extension of `Geodesic/Homogeneity.lean`. We
expose a hypothesis-form `expMap_zero_of_value` here, so that the
headline `expMap g p 0 = p` follows in one line from the structural
identity once it is shipped.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-! ## The exponential map and its domain -/

/-- **The exponential map.** For `p : M` and `v : T_p M`,
`expMap g p v := γ_{p, v}(1)`, the value at `t = 1` of the canonical
maximal geodesic with initial data `(p, v)`. The definition is
unconditional: when `1` does not lie in the maximal interval of
definition of the geodesic — i.e. `v ∉ expDomain g p` — the underlying
`maximalGeodesic` curve takes the junk value `p`, so `expMap g p v = p`
in that case. -/
def expMap (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) : M :=
  maximalGeodesic (I := I) g p v 1

/-- **The domain of the exponential map.** A tangent vector `v : T_p M`
belongs to `expDomain g p` iff `1` lies in the maximal interval of
definition of the geodesic with initial data `(p, v)`. -/
def expDomain (g : SmoothRiemannianMetric I M) (p : M) :
    Set (TangentSpace I p) :=
  {v | (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v}

/-- Membership in `expDomain` unfolds directly to membership of `1` in
the maximal interval. -/
lemma mem_expDomain_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} :
    v ∈ expDomain (I := I) g p ↔
      (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v :=
  Iff.rfl

/-- An alternative characterisation: a tangent vector `v` is in the
domain of the exponential map iff there exists an open
`J : Set ℝ` containing both `0` and `1` carrying a geodesic with
initial data `(p, v)`. -/
lemma mem_expDomain_iff_witness
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} :
    v ∈ expDomain (I := I) g p ↔
      MaximalGeodesicWitness (I := I) g p v 1 :=
  Iff.rfl

/-! ## Junk value outside the domain

These statements use the canonical maximal geodesic, hence require the
typeclasses `[I.Boundaryless] [CompleteSpace E]` under which the
maximal geodesic is defined in `Geodesic/MaximalInterval.lean`. -/

section JunkValue

variable [I.Boundaryless] [CompleteSpace E]

/-- If `v` is not in the domain of the exponential map, then
`expMap g p v = p` (the junk value of `maximalGeodesic` outside its
maximal interval). -/
theorem expMap_of_not_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (hv : v ∉ expDomain (I := I) g p) :
    expMap (I := I) g p v = p := by
  unfold expMap
  exact maximalGeodesic_of_not_mem (I := I) (g := g) (p := p) (v := v)
    (t := 1) hv

/-- Contrapositive form: if `expMap g p v ≠ p`, then `v` is in the
domain of the exponential map. (Note: the converse is false; many
elements of the domain may map to `p` for genuine geometric reasons,
e.g. conjugate-point identifications.) -/
theorem mem_expDomain_of_expMap_ne
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (h : expMap (I := I) g p v ≠ p) :
    v ∈ expDomain (I := I) g p := by
  by_contra hv
  exact h (expMap_of_not_mem (I := I) (g := g) (p := p) (v := v) hv)

end JunkValue

/-! ## Zero-vector behaviour

At zero initial velocity, the maximal interval is the entire real line
(`maximalGeodesicInterval_zero_velocity`), so in particular
`1 ∈ maximalGeodesicInterval g p 0`. Hence the zero vector is in the
domain of the exponential map and the domain is nonempty.

The corresponding value identity `expMap g p 0 = p` is the structural
identity captured by `maximalGeodesic_zero_velocity_value` (a pending
node — see the file overview). We expose a hypothesis-form here to
make `expMap_zero` derivable in one line once the structural identity
ships. -/

section ZeroVector

variable [I.Boundaryless] [CompleteSpace E]

/-- The zero tangent vector at `p` lies in the domain of the
exponential map at `p`. -/
theorem zero_mem_expDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∈ expDomain (I := I) g p := by
  -- `0 : TangentSpace I p` reduces definitionally to `0 : E`.
  change (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (0 : E)
  rw [maximalGeodesicInterval_zero_velocity (I := I) g p]
  exact Set.mem_univ _

/-- The domain of the exponential map is nonempty: it contains `0`. -/
theorem expDomain_nonempty
    (g : SmoothRiemannianMetric I M) (p : M) :
    (expDomain (I := I) g p).Nonempty :=
  ⟨(0 : TangentSpace I p), zero_mem_expDomain (I := I) g p⟩

/-- Hypothesis-form of `expMap_zero`. Once the structural identity
`maximalGeodesic g p (0 : E) 1 = p` ships (the propagation lemma in
`Geodesic/Homogeneity.lean`), the headline `expMap g p 0 = p` follows
in one line via this lemma. -/
theorem expMap_zero_of_value
    {g : SmoothRiemannianMetric I M} {p : M}
    (h : maximalGeodesic (I := I) g p (0 : E) 1 = p) :
    expMap (I := I) g p (0 : TangentSpace I p) = p := h

/-- **Unconditional headline.** `expMap g p 0 = p`. The exponential map
of any smooth Riemannian metric `g` at any point `p`, applied to the
zero tangent vector, returns the basepoint `p` itself. -/
theorem expMap_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    expMap (I := I) g p (0 : TangentSpace I p) = p :=
  expMap_zero_of_value
    (maximalGeodesic_zero_velocity_value (I := I) g p 1)

end ZeroVector

end Exp
end Riemannian
end Geometry
end DifferentialGeometry

end
