import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.CurvatureBundling

/-!
# Intrinsic Riemann curvature at a point

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`, the bundled
Levi-Civita covariant derivative gives at each base point `x : M` a continuous
trilinear form on the tangent space — the value at `x` of the Riemann curvature
endomorphism `(V, W) ↦ R(V, W) X`.

This file packages that bundled form as `intrinsicRiemann g x`, specialised to the
tangent-bundle case `V = TangentSpace I` of the general `riemannOp`. The
chart-independence is built in: `intrinsicRiemann` is defined directly as the
bundled fibre-trilinear form, not via any specific chart.

## Main contents

* `intrinsicRiemann g x` — the bundled trilinear form
  `T_x M →L[ℝ] T_x M →L[ℝ] T_x M →L[ℝ] T_x M`.
* `intrinsicRiemann_apply_smooth` — the section-evaluation formula on smooth global
  tangent-bundle sections, identifying `intrinsicRiemann g x (X x) (Y x) (Z x)` with
  `riemannSec (LeviCivita g) X Y Z x`.
* `intrinsicRiemann_swap` — antisymmetry in the first two arguments.
* `intrinsicRiemann_self_eq_zero` — vanishing on coincident first two arguments.
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

/-- **Intrinsic Riemann curvature operator at a point.** For a smooth
Riemannian metric `g` on a boundaryless smooth manifold `M`, the bundled
Levi-Civita connection provides at each `x : M` a continuous trilinear
form `T_x M × T_x M × T_x M → T_x M` — the value of the curvature
endomorphism `(X, Y) ↦ R(X, Y) Z` at `x`.

This is the intrinsic counterpart of the chart-local
`chartRiemannTensor` in `Geometry/Curvature/Riemann.lean`. The two are
related by the standard component formula but the intrinsic version is
chart-independent by construction. -/
noncomputable def intrinsicRiemann
    (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x :=
  riemannOp (cov := LeviCivita (I := I) g) x

/-- **Smooth-section application formula for `intrinsicRiemann`.** For
smooth global tangent-bundle sections `X, Y, Z`, the value of
`intrinsicRiemann g x` on `(X x, Y x, Z x)` equals the section-level
Riemann tensor `riemannSec (LeviCivita g) X Y Z` at `x`. -/
theorem intrinsicRiemann_apply_smooth
    (g : SmoothRiemannianMetric I M) {x : M}
    {X Y Z : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    intrinsicRiemann (I := I) g x (X x) (Y x) (Z x) =
      riemannSec (LeviCivita (I := I) g) X Y Z x := by
  unfold intrinsicRiemann
  exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g) hX hY hZ

/-- **Antisymmetry in the first two arguments.** The intrinsic curvature
satisfies `R(V, W) X = -R(W, V) X` at every point. Inherited from the
general `riemannOp_swap` valid for every `CovariantDerivative`. -/
theorem intrinsicRiemann_swap
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W X : TangentSpace I x) :
    intrinsicRiemann (I := I) g x V W X =
      -intrinsicRiemann (I := I) g x W V X := by
  unfold intrinsicRiemann
  exact riemannOp_swap (cov := LeviCivita (I := I) g) x V W X

/-- **Antisymmetry at coincident slots.** `R(V, V) X = 0` for every
tangent vector `V` and every `X` at `x`. From antisymmetry with `W = V`:
`R(V, V) X = -R(V, V) X`, hence `2 · R(V, V) X = 0`, hence `R(V, V) X = 0`. -/
theorem intrinsicRiemann_self_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (V X : TangentSpace I x) :
    intrinsicRiemann (I := I) g x V V X = 0 := by
  have h := intrinsicRiemann_swap (I := I) g x V V X
  -- `h : intrinsicRiemann g x V V X = -intrinsicRiemann g x V V X`.
  -- Hence `2 • a = 0` and so `a = 0`, since `2 ≠ 0` in `ℝ`.
  set a : TangentSpace I x := intrinsicRiemann (I := I) g x V V X with ha
  have ha_eq : a = -a := h
  have hsum : a + a = 0 := by
    nth_rewrite 2 [ha_eq]
    exact add_neg_cancel a
  have h2 : (2 : ℝ) • a = 0 := by
    rw [two_smul]; exact hsum
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp h2).resolve_left h2ne

end Curvature
end Riemannian
end Geometry
end DifferentialGeometry

end
