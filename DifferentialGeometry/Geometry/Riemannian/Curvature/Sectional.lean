import DifferentialGeometry.Geometry.Riemannian.Curvature.Intrinsic

/-!
# Sectional curvature

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`, and two
tangent vectors `V, W : T_x M`, the *sectional curvature* of the two-plane
`span {V, W}` at `x` is
$$
  K(V, W) \;=\; \frac{g\bigl(R(V, W) W,\, V\bigr)}{|V|^2\, |W|^2 - g(V, W)^2}.
$$
This file defines `sectionalCurvature` together with its denominator
`gramDeterminant` and the basic invariance properties:

* swap symmetry of the Gram determinant,
* swap symmetry of the numerator (from the pair-swap symmetry of the
  intrinsic Riemann tensor),
* swap symmetry of the sectional curvature `K(V, W) = K(W, V)`,
* vanishing on coincident arguments `K(V, V) = 0`.

When `V` and `W` are linearly dependent the denominator vanishes and Lean's
convention `0 / 0 = 0` returns `0` for the expression, the standard
mathematical extension to the degenerate case.
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

/-- **Sectional curvature.** For a smooth Riemannian metric `g` on `M`
and two tangent vectors `V, W : T_x M`, the sectional curvature of the
two-plane `span {V, W}` at `x` is
$$
  K(V, W) = \frac{g\bigl(R(V, W) W, V\bigr)}{|V|^2 |W|^2 - g(V, W)^2}.
$$
When `V` and `W` are linearly dependent the denominator vanishes; in
that case Lean's convention `0 / 0 = 0` returns the value `0` for the
expression, which is the standard mathematical extension (the plane
they span is degenerate). -/
noncomputable def sectionalCurvature
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) : ℝ :=
  g.inner x (intrinsicRiemann (I := I) g x V W W) V /
    (g.inner x V V * g.inner x W W - (g.inner x V W) ^ 2)

/-- The Gram determinant `|V|² |W|² - g(V, W)²` is the standard
denominator of `sectionalCurvature`. -/
noncomputable def gramDeterminant
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) : ℝ :=
  g.inner x V V * g.inner x W W - (g.inner x V W) ^ 2

@[simp] lemma sectionalCurvature_def
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    sectionalCurvature (I := I) g x V W =
      g.inner x (intrinsicRiemann (I := I) g x V W W) V /
        (g.inner x V V * g.inner x W W - (g.inner x V W) ^ 2) := rfl

@[simp] lemma gramDeterminant_def
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    gramDeterminant (I := I) g x V W =
      g.inner x V V * g.inner x W W - (g.inner x V W) ^ 2 := rfl

/-- **Swap symmetry of the Gram determinant.** `Γ(V, W) = Γ(W, V)`. -/
lemma gramDeterminant_swap
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    gramDeterminant (I := I) g x V W = gramDeterminant (I := I) g x W V := by
  unfold gramDeterminant
  have hsym : g.inner x V W = g.inner x W V := g.symm x V W
  rw [hsym]
  ring

/-- The numerator of the sectional curvature, `g(R(V, W) W, V)`, is
symmetric under the swap `(V, W) ↔ (W, V)`. By the pair-swap symmetry
of the intrinsic Riemann tensor `g(R(V, W) X, Y) = g(R(X, Y) V, W)`,
applied to `(X, Y) := (W, V)`, the numerator equals `g(R(W, V) V, W)`,
which is also the numerator with `V` and `W` exchanged. -/
lemma sectionalCurvature_numerator_swap
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    g.inner x (intrinsicRiemann (I := I) g x V W W) V =
      g.inner x (intrinsicRiemann (I := I) g x W V V) W := by
  -- Pair-swap with X = W, Y = V:  g(R(V,W) W, V) = g(R(W,V) V, W).
  exact intrinsicRiemann_metric_pair_swap (I := I) g x V W W V

/-- **Swap symmetry of the sectional curvature.** `K(V, W) = K(W, V)`. -/
theorem sectionalCurvature_swap
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    sectionalCurvature (I := I) g x V W = sectionalCurvature (I := I) g x W V := by
  unfold sectionalCurvature
  -- Both numerator and denominator are symmetric under V ↔ W.
  have hN := sectionalCurvature_numerator_swap (I := I) g x V W
  -- Replace the numerator.
  rw [hN]
  -- The remaining denominator differs by `V ↔ W` in the inner product. Use g.symm.
  have hsym : g.inner x V W = g.inner x W V := g.symm x V W
  have hden :
      g.inner x V V * g.inner x W W - (g.inner x V W) ^ 2 =
        g.inner x W W * g.inner x V V - (g.inner x W V) ^ 2 := by
    rw [hsym]; ring
  rw [hden]

/-- **Trivial vanishing on coincident arguments.** When `V = W`, the
numerator of sectional curvature involves `R(V, V) V = 0`, so the value
is `0 / (something)` (which is `0`) — and in the degenerate case where
the denominator also vanishes Lean's convention `0 / 0 = 0` still gives
`0`. -/
@[simp] theorem sectionalCurvature_self
    (g : SmoothRiemannianMetric I M) (x : M) (V : TangentSpace I x) :
    sectionalCurvature (I := I) g x V V = 0 := by
  unfold sectionalCurvature
  -- Numerator: g(R(V, V) V, V) = g(0, V) = 0 since R(V, V) = 0.
  have hR : intrinsicRiemann (I := I) g x V V V = 0 :=
    intrinsicRiemann_self_eq_zero (I := I) g x V V
  rw [hR]
  -- `g.inner x 0 = 0` as a CLM, so applied to `V` it is `0`.
  have h0 : g.inner x (0 : TangentSpace I x) V = 0 := by
    simp
  rw [h0]
  simp

/-- **Scale invariance in the first slot.** For any nonzero scalar `c`,
the sectional curvature is unchanged when the first slot is rescaled by
`c`: `K(c • V, W) = K(V, W)`. Both the numerator and the denominator
acquire a factor of `c²` from the trilinearity of the curvature operator
and the bilinearity of the inner product, which cancel. -/
theorem sectionalCurvature_smul_left
    (g : SmoothRiemannianMetric I M) (x : M)
    {c : ℝ} (hc : c ≠ 0) (V W : TangentSpace I x) :
    sectionalCurvature (I := I) g x (c • V) W =
      sectionalCurvature (I := I) g x V W := by
  unfold sectionalCurvature
  -- The Riemann tensor is linear in the first slot.
  have hW1 : intrinsicRiemann (I := I) g x (c • V) W =
      c • intrinsicRiemann (I := I) g x V W :=
    (intrinsicRiemann (I := I) g x).map_smul c V ▸ rfl
  have hR : intrinsicRiemann (I := I) g x (c • V) W W =
      c • intrinsicRiemann (I := I) g x V W W := by
    rw [hW1]; rfl
  rw [hR]
  -- Numerator: `g(c • R(V,W) W, c • V) = c² · g(R(V,W) W, V)`.
  have hnum :
      g.inner x (c • intrinsicRiemann (I := I) g x V W W) (c • V) =
        c ^ 2 * g.inner x (intrinsicRiemann (I := I) g x V W W) V := by
    rw [(g.inner x).map_smul c (intrinsicRiemann (I := I) g x V W W),
        ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul (g.inner x (intrinsicRiemann (I := I) g x V W W)) c V,
        smul_eq_mul, smul_eq_mul]
    ring
  rw [hnum]
  -- Denominator: `g(c • V, c • V) g(W, W) - g(c • V, W)² = c² · (g(V,V) g(W,W) - g(V,W)²)`.
  have hVV : g.inner x (c • V) (c • V) = c ^ 2 * g.inner x V V := by
    rw [(g.inner x).map_smul c V, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul (g.inner x V) c V, smul_eq_mul, smul_eq_mul]
    ring
  have hVW : g.inner x (c • V) W = c * g.inner x V W := by
    rw [(g.inner x).map_smul c V, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hVV, hVW]
  have hden_eq :
      c ^ 2 * g.inner x V V * g.inner x W W - (c * g.inner x V W) ^ 2 =
        c ^ 2 * (g.inner x V V * g.inner x W W - g.inner x V W ^ 2) := by
    ring
  rw [hden_eq]
  -- Cancel the common nonzero `c²` factor.
  have hcsq : (c ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hc
  rw [mul_div_mul_left _ _ hcsq]

/-- **Scale invariance in the second slot.** For any nonzero scalar `c`,
the sectional curvature is unchanged when the second slot is rescaled by
`c`: `K(V, c • W) = K(V, W)`. Follows from the first-slot version by
the swap symmetry. -/
theorem sectionalCurvature_smul_right
    (g : SmoothRiemannianMetric I M) (x : M)
    {c : ℝ} (hc : c ≠ 0) (V W : TangentSpace I x) :
    sectionalCurvature (I := I) g x V (c • W) =
      sectionalCurvature (I := I) g x V W := by
  rw [sectionalCurvature_swap (I := I) g x V (c • W),
      sectionalCurvature_smul_left (I := I) g x hc W V,
      sectionalCurvature_swap (I := I) g x W V]

end Curvature
end Riemannian
end Geometry
end DifferentialGeometry

end
