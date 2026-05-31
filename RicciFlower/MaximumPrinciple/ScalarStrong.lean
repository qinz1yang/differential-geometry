import RicciFlower.RicciFlow.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar Strong Maximum Principle

This file isolates the analytic strong-maximum-principle input needed by the
Hamilton positive-Ricci endpoint.  The checked theorem at the bottom is only
the logical assembly from the named analytic frontiers and the pointwise
three-dimensional flatness bridge.
-/

namespace RicciFlower
namespace RicciFlow

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Hopf parabolic strong maximum principle for the scalar curvature
supersolution on a connected boundaryless Ricci-flow spacetime.

If the scalar curvature is nonnegative on the time carrier and vanishes at a
point `(t₁,x₁)`, then the zero propagates backward in time and spreads over
each earlier connected slice.  This is the genuine analytic Hopf strong
maximum-principle frontier; cf. Chow--Lu--Ni, *Hamilton's Ricci Flow*,
Corollaries 12.43--12.50. -/
theorem scalar_hopf_zero_propagates_backward
    {D : Realized.RealTimeInterval}
    [ConnectedSpace M] [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (_hsol : IsSolutionOn (I := I) S)
    (_hscalarNonneg :
      ∀ t : Real, t ∈ D.carrier → ∀ x : M, 0 ≤ S.scalar t x)
    {t₁ : Real} (ht₁ : t₁ ∈ D.carrier) {x₁ : M}
    (hzero : S.scalar t₁ x₁ = 0) :
    ∀ t : Real, t ∈ D.carrier → t ≤ t₁ → ∀ y : M, S.scalar t y = 0 := by
  -- Frontier: Hopf parabolic SMP for a nonnegative scalar supersolution.
  sorry

/-- Pointwise three-dimensional flatness bridge at a scalar zero.

In dimension three, Ricci nonnegativity and scalar zero force all Ricci
eigenvalues to vanish; the canonical dimension-three Riemann-from-Ricci bridge
then gives vanishing lowered curvature.  This is intended to be closed from
`DimensionThree.ricciEigen3`, `RicciFlow.scalarTrace_delta`, and
`DimensionThree.rm04_einstein3_at`. -/
theorem ricci_flat_of_scalar_zero_dim3
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (_hdim : Module.finrank Real (TangentSpace I x) = 3)
    (_hRicNonneg : ∀ v : TangentSpace I x,
      0 ≤ S.ricciAt t x (Curvature.vec2 (I := I) v v))
    (_hscalarZero : S.scalar t x = 0) :
    S.base.rm04 t x = 0 := by
  -- Frontier: finite-dimensional Ricci-eigenvalue algebra plus the
  -- RicciFlower 3D Riemann-from-Ricci bridge.
  sorry

/-- Forward preservation of a flat time slice.

If one time slice of a smooth Ricci flow is flat, the stationary flat solution
has the same initial data, so forward uniqueness keeps the flow flat and hence
keeps scalar curvature zero at all later carrier times.  This is a genuine
analytic uniqueness frontier. -/
theorem scalar_zero_preserved_forward
    {D : Realized.RealTimeInterval}
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (_hsol : IsSolutionOn (I := I) S)
    {t₁ : Real} (ht₁ : t₁ ∈ D.carrier)
    (_hflat : ∀ y : M, S.base.rm04 t₁ y = 0) :
    ∀ t : Real, t ∈ D.carrier → t₁ ≤ t → ∀ y : M, S.scalar t y = 0 := by
  -- Frontier: forward uniqueness from a flat Ricci-flow slice.
  sorry

/-- Scalar strong maximum principle assembled from the Hopf zero-propagation
frontier, the three-dimensional scalar-zero flatness bridge, and forward
flat-slice preservation.

The Ricci nonnegativity hypothesis is explicit because the pointwise flatness
bridge uses `Ric ≥ 0` together with `R = 0`; scalar nonnegativity alone is not
an honest replacement for that input. -/
theorem scalar_strong_maximum_principle
    {D : Realized.RealTimeInterval}
    [ConnectedSpace M] [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hsol : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hRicNonneg :
      ∀ t : Real, t ∈ D.carrier → ∀ x : M, ∀ v : TangentSpace I x,
        0 ≤ S.ricciAt t x (Curvature.vec2 (I := I) v v))
    (hscalarNonneg :
      ∀ t : Real, t ∈ D.carrier → ∀ x : M, 0 ≤ S.scalar t x)
    {t₀ : Real} (ht₀ : t₀ ∈ D.carrier) {x₀ : M}
    (hpos : 0 < S.scalar t₀ x₀) :
    ∀ t : Real, t ∈ D.carrier → ∀ x : M, 0 < S.scalar t x := by
  intro t ht x
  by_contra hnot
  have hzero : S.scalar t x = 0 := by
    exact le_antisymm (le_of_not_gt hnot) (hscalarNonneg t ht x)
  by_cases htime : t₀ ≤ t
  · have hbaseZero :
        S.scalar t₀ x₀ = 0 :=
      scalar_hopf_zero_propagates_backward (I := I) (M := M) S hsol
        hscalarNonneg ht hzero t₀ ht₀ htime x₀
    linarith
  · have hlt : t < t₀ := lt_of_not_ge htime
    have hsliceZero : ∀ y : M, S.scalar t y = 0 := by
      intro y
      exact scalar_hopf_zero_propagates_backward (I := I) (M := M) S hsol
        hscalarNonneg ht hzero t ht le_rfl y
    have hflat : ∀ y : M, S.base.rm04 t y = 0 := by
      intro y
      exact ricci_flat_of_scalar_zero_dim3 (I := I) (M := M) S (hdim y)
        (hRicNonneg t ht y) (hsliceZero y)
    have hbaseZero :
        S.scalar t₀ x₀ = 0 :=
      scalar_zero_preserved_forward (I := I) (M := M) S hsol ht hflat
        t₀ ht₀ (le_of_lt hlt) x₀
    linarith

end

end RicciFlow
end RicciFlower
