import DifferentialGeometry.Geometry.Riemannian.Curvature.Sectional

/-!
# Constant sectional curvature

A smooth Riemannian metric `g` on a boundaryless smooth manifold `M` has
**constant sectional curvature `K`** when the numerator of the sectional
curvature formula equals `K` times the Gram determinant on every pair of
tangent vectors at every point:
$$
  g\bigl(R(V, W) W,\, V\bigr) \;=\; K \cdot \bigl(|V|^2 |W|^2 - g(V, W)^2\bigr).
$$

Formulating the predicate at the level of the numerator (rather than the
quotient) avoids any case-split on the Gram determinant: it automatically
covers the degenerate case where `V` and `W` are linearly dependent, in
which both sides vanish.

This file ships:

* the predicate `HasConstantSectionalCurvature g K`;
* a pointwise re-statement `HasConstantSectionalCurvature.apply`;
* the consequence that the sectional curvature reads `K` on every
  non-degenerate two-plane;
* invariance under rescaling in the first slot.
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

/-- A smooth Riemannian metric `g` on `M` has **constant sectional
curvature `K`** iff for every point `x : M` and every pair of tangent
vectors `V, W : T_x M`, the *numerator* of the sectional curvature
formula equals `K · gramDeterminant g x V W`:
$$
  g(R(V, W) W, V) = K \cdot (|V|^2 |W|^2 - g(V, W)^2).
$$
This formulation avoids any case-split on the Gram determinant: when
`V, W` are linearly independent the standard `sectionalCurvature g x V W
= K` follows by division; when they are linearly dependent both sides
are zero (the right-hand side is zero by the Gram-zero condition; the
left-hand side is zero because `R(V, W)` and the inner product behave
appropriately under linear dependence). -/
def HasConstantSectionalCurvature (g : SmoothRiemannianMetric I M) (K : ℝ) : Prop :=
  ∀ (x : M) (V W : TangentSpace I x),
    g.inner x (intrinsicRiemann (I := I) g x V W W) V =
      K * gramDeterminant (I := I) g x V W

/-- The constant-sectional-curvature equation specialised to a single
quadruple. A useful direct restatement of the predicate. -/
theorem HasConstantSectionalCurvature.apply
    {g : SmoothRiemannianMetric I M} {K : ℝ}
    (h : HasConstantSectionalCurvature (I := I) g K)
    (x : M) (V W : TangentSpace I x) :
    g.inner x (intrinsicRiemann (I := I) g x V W W) V =
      K * gramDeterminant (I := I) g x V W :=
  h x V W

/-- **Sectional curvature reads `K` on every non-degenerate two-plane.**
When the Gram determinant `|V|² |W|² − g(V, W)²` is nonzero (equivalently,
`V` and `W` are linearly independent), the sectional curvature
`sectionalCurvature g x V W` is exactly `K`. -/
theorem HasConstantSectionalCurvature.sectionalCurvature_eq
    {g : SmoothRiemannianMetric I M} {K : ℝ}
    (h : HasConstantSectionalCurvature (I := I) g K)
    {x : M} {V W : TangentSpace I x}
    (hVW : gramDeterminant (I := I) g x V W ≠ 0) :
    sectionalCurvature (I := I) g x V W = K := by
  unfold sectionalCurvature
  rw [show g.inner x V V * g.inner x W W - g.inner x V W ^ 2 =
         gramDeterminant (I := I) g x V W from rfl]
  rw [h x V W, mul_comm K (gramDeterminant (I := I) g x V W)]
  exact mul_div_cancel_left₀ K hVW

/-- Constant sectional curvature is preserved under scaling: if `g` has
constant sectional curvature `K`, then the same equation holds for the
rescaled pair `(c • V, W)` automatically (both sides scale by `c²`). -/
theorem HasConstantSectionalCurvature.smul_left
    {g : SmoothRiemannianMetric I M} {K : ℝ}
    (h : HasConstantSectionalCurvature (I := I) g K) (c : ℝ)
    (x : M) (V W : TangentSpace I x) :
    g.inner x (intrinsicRiemann (I := I) g x (c • V) W W) (c • V) =
      K * gramDeterminant (I := I) g x (c • V) W := by
  -- Both sides scale by c² when V is replaced by c • V; the original
  -- relation lifts.
  have hVW := h x V W
  -- LHS scale: by trilinearity in slot 1 and bilinearity of g.
  have hR : intrinsicRiemann (I := I) g x (c • V) W W =
      c • intrinsicRiemann (I := I) g x V W W := by
    have hW1 : intrinsicRiemann (I := I) g x (c • V) W =
        c • intrinsicRiemann (I := I) g x V W :=
      (intrinsicRiemann (I := I) g x).map_smul c V ▸ rfl
    rw [hW1]; rfl
  rw [hR]
  -- LHS becomes c² · g.inner x R V W W V.
  have hLHS :
      g.inner x (c • intrinsicRiemann (I := I) g x V W W) (c • V) =
        c ^ 2 * g.inner x (intrinsicRiemann (I := I) g x V W W) V := by
    rw [(g.inner x).map_smul c (intrinsicRiemann (I := I) g x V W W),
        ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul (g.inner x (intrinsicRiemann (I := I) g x V W W)) c V,
        smul_eq_mul, smul_eq_mul]
    ring
  rw [hLHS]
  -- RHS scale: gramDeterminant scales by c².
  have hGr : gramDeterminant (I := I) g x (c • V) W =
      c ^ 2 * gramDeterminant (I := I) g x V W := by
    unfold gramDeterminant
    have hVV : g.inner x (c • V) (c • V) = c ^ 2 * g.inner x V V := by
      rw [(g.inner x).map_smul c V, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.map_smul (g.inner x V) c V, smul_eq_mul, smul_eq_mul]
      ring
    have hVW' : g.inner x (c • V) W = c * g.inner x V W := by
      rw [(g.inner x).map_smul c V, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hVV, hVW']
    ring
  rw [hGr]
  -- Both sides equal c² · (the original equation), so done by `hVW`.
  rw [hVW]
  ring

end Curvature
end Riemannian
end Geometry
end DifferentialGeometry

end
