import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarMinimum
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.SectionalScalarBound

/-!
# Sectional lower bounds are preserved by Ricci flow on closed surfaces

On a closed surface `sec ≥ c` is `R ≥ 2c` (`sectionalBoundedBelow_iff_two_mul_le_scalar_of_finrank_eq_two`),
and a lower bound of the scalar curvature is preserved by the flow because
`∂R = ΔR + 2|Ric|² ≥ ΔR` (`scalar_lower_bound_of_compact`). Hence every sectional lower bound,
of either sign, is preserved, with no loss: this is the two-dimensional replacement of the
three-dimensional estimate `sectionalBoundedBelow_exp_preserved` used by LFR50.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M]

/-- **2D preservation.** Along a Ricci flow on a closed surface, `sec ≥ c` at time `a` gives
`sec ≥ c` at every later time of a regular slab. -/
theorem sectionalBoundedBelow_preserved_of_finrank_eq_two
    (hdim : Module.finrank ℝ E = 2) {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b c : ℝ}
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hinit : SectionalBoundedBelow (S.base.metric a) c) :
    ∀ t ∈ Icc a b, SectionalBoundedBelow (S.base.metric t) c := by
  have h0 := (sectionalBoundedBelow_iff_two_mul_le_scalar_of_finrank_eq_two hdim).1 hinit
  intro t ht
  refine (sectionalBoundedBelow_iff_two_mul_le_scalar_of_finrank_eq_two hdim).2 fun x => ?_
  exact scalar_lower_bound_of_compact S hS hslab hregular (c := 2 * c) h0 t ht x

end DifferentialGeometry.PDE.RicciFlow
