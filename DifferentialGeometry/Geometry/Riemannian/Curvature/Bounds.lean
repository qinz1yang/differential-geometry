import DifferentialGeometry.Geometry.Riemannian.Curvature.Sectional
import DifferentialGeometry.Geometry.Riemannian.Curvature.Einstein

/-!
# Curvature bound predicates

This file ships four predicates expressing standard curvature bounds for a
smooth Riemannian metric `g` on a boundaryless smooth manifold `M`:

* `HasNonnegSectionalCurvature g`,
* `HasNonposSectionalCurvature g`,
* `HasRicciBoundBelow g K`,
* `HasNonnegRicci g`,

together with their basic consequences and the link to `IsEinstein`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- A smooth Riemannian metric `g` has **nonnegative sectional curvature**
iff `K(V, W) ≥ 0` for every point and every pair of tangent vectors.
Using the `gramDeterminant`-multiplied form, this means
`g(R(V,W) W, V) ≥ 0` whenever the Gram determinant is nonnegative —
which holds always by Cauchy-Schwarz, so the predicate reduces to a
pointwise nonneg statement on the numerator. -/
def HasNonnegSectionalCurvature (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ (x : M) (V W : TangentSpace I x),
    0 ≤ g.inner x (intrinsicRiemann (I := I) g x V W W) V

/-- A smooth Riemannian metric `g` has **nonpositive sectional curvature**
iff `K(V, W) ≤ 0`. By the same Cauchy-Schwarz observation, this reduces
to `g(R(V,W) W, V) ≤ 0` pointwise. -/
def HasNonposSectionalCurvature (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ (x : M) (V W : TangentSpace I x),
    g.inner x (intrinsicRiemann (I := I) g x V W W) V ≤ 0

/-- A smooth Riemannian metric `g` has **Ricci curvature bounded below
by `K`** iff `Ric(V, V) ≥ K · g(V, V)` for every point and every
tangent vector. This is the fundamental hypothesis of Myers-type theorems. -/
def HasRicciBoundBelow (g : SmoothRiemannianMetric I M) (K : ℝ) : Prop :=
  ∀ (x : M) (V : TangentSpace I x),
    K * g.inner x V V ≤ ricciTensor (I := I) g x V V

/-- A smooth Riemannian metric `g` has **nonnegative Ricci curvature**
iff `Ric(V, V) ≥ 0` for every point and every tangent vector. -/
def HasNonnegRicci (g : SmoothRiemannianMetric I M) : Prop :=
  HasRicciBoundBelow (I := I) g 0

/-- Direct unfolding: `HasNonnegRicci g ↔ ∀ x V, 0 ≤ Ric(V, V)`. -/
theorem hasNonnegRicci_iff_nonneg
    {g : SmoothRiemannianMetric I M} :
    HasNonnegRicci (I := I) g ↔
      ∀ (x : M) (V : TangentSpace I x),
        0 ≤ ricciTensor (I := I) g x V V := by
  unfold HasNonnegRicci HasRicciBoundBelow
  refine ⟨fun h x V => ?_, fun h x V => ?_⟩
  · have := h x V
    -- 0 * g.inner x V V ≤ ricciTensor g x V V
    rw [zero_mul] at this
    exact this
  · have := h x V
    -- 0 ≤ ricciTensor g x V V → 0 * g.inner x V V ≤ ricciTensor g x V V
    rw [zero_mul]
    exact this

/-- An Einstein metric with Einstein constant `K ≥ 0` has Ricci
curvature bounded below by `K`. -/
theorem IsEinstein.ricciBoundBelow_of_nonneg
    {g : SmoothRiemannianMetric I M} {K : ℝ}
    (h : IsEinstein (I := I) g K) (_hK : 0 ≤ K) :
    HasRicciBoundBelow (I := I) g K := by
  intro x V
  -- Ric(V, V) = K * g(V, V) on the Einstein metric, so the bound is an equality.
  rw [h x V V]

/-- An Einstein metric with constant zero has nonneg Ricci. -/
theorem IsEinstein.hasNonnegRicci_of_zero
    {g : SmoothRiemannianMetric I M}
    (h : IsEinstein (I := I) g 0) :
    HasNonnegRicci (I := I) g := by
  unfold HasNonnegRicci
  exact h.ricciBoundBelow_of_nonneg (le_refl 0)

end Curvature
end Riemannian
end Geometry
end DifferentialGeometry

end
