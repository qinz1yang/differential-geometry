import DifferentialGeometry.Geometry.Curvature.Realized.Operators

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Classical solutions of scalar time-dependent heat equations

This file gives the interval-local predicate for a classical solution of

`∂ₜu = Δ_{g(t)}u + V(t)u`

for a realized metric family.  It deliberately contains no existence theorem:
constructing such solutions for a genuinely time-dependent metric is the
non-autonomous parabolic frontier.
-/

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open DifferentialGeometry.Integral.Connection
open Set
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- A classical solution of the scalar heat equation with time-dependent
potential `V` on the real time interval `D`.

The solution is jointly smooth on the regular interior, continuous up to the
time carrier, spatially smooth on every carrier slice, and satisfies
`∂ₜu = Δ_{g(t)}u + V(t)u` at every regular time.  The function
`u` is separate data; this predicate records only its solution properties. -/
structure IsHeatPotOn
    (D : RealTimeInterval)
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (V u : Real → M → Real) : Prop where
  /-- Joint spacetime smoothness on the regular interior. -/
  jointSmooth :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => u q.1 q.2) (D.regular ×ˢ univ)
  /-- Joint spacetime continuity up to every endpoint in the carrier. -/
  jointCont :
    ContinuousOn (fun q : Real × M => u q.1 q.2)
      (D.carrier ×ˢ univ)
  /-- Smoothness of every spatial time slice, including carrier endpoints. -/
  sliceSmooth :
    ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (u t)
  /-- The pointwise scalar heat equation at every regular time. -/
  equation :
    ∀ t : Real, t ∈ D.regular → ∀ x : M,
      HasDerivAt (fun s : Real => u s x)
        (laplacianAt (I := I) G t (u t) x + V t x * u t x) t

namespace IsHeatPotOn

/-- Restrict a classical heat-potential solution to an interval with smaller
carrier and regular sets. -/
theorem mono
    {D D' : RealTimeInterval}
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    {V u : Real → M → Real}
    (h : IsHeatPotOn D G V u)
    (hcarrier : D'.carrier ⊆ D.carrier)
    (hregular : D'.regular ⊆ D.regular) :
    IsHeatPotOn D' G V u where
  jointSmooth := h.jointSmooth.mono
    (Set.prod_mono hregular Set.Subset.rfl)
  jointCont := h.jointCont.mono
    (Set.prod_mono hcarrier Set.Subset.rfl)
  sliceSmooth t ht := h.sliceSmooth t (hcarrier ht)
  equation t ht x := h.equation t (hregular ht) x

end IsHeatPotOn

end

end DifferentialGeometry.Analysis.Parabolic
