import DifferentialGeometry.Integral.Connection.ConnectionLaplacian
import DifferentialGeometry.Integral.Connection.TensorConnLaplacian
import DifferentialGeometry.Integral.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.RSTensor.Defs

/-!
# Pointwise connection Laplacian on mixed `(r, s)`-tensor sections

For a smooth Riemannian metric `g` on a closed manifold `M`, this file
defines the pointwise connection (rough) Laplacian on a smooth
`(r, s)`-tensor section,
$$
  (\Delta_\nabla T)(x) = \mathrm{tr}_g\bigl(\nabla \nabla T\bigr)(x),
$$
extending the existing scalar (`connLaplacian_function`) and vector
(`connLaplacian_vector`) variants.

The definition takes a smooth tensor section
`T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, fun x => TensorRSSpace r s I x⟯`
and produces a pointwise value
`(connLaplacianMixed g r s T x : TensorRSSpace r s I x)`.

## Main definitions

* `connLaplacianMixed g r s T x` — the pointwise rough Laplacian of a
  smooth `(r, s)`-tensor section at a point `x`.

## Main results

* `connLaplacianMixed_scalar_eq_function` — agreement with the existing
  scalar `connLaplacian_function` when `r = s = 0`, identifying the
  `(0, 0)`-tensor fiber with `ℝ`.

## Sign convention

The geometer convention `Δ_g = div ∘ grad` is used, with spectrum in
`(-∞, 0]` on closed manifolds; the rough Laplacian inherits this sign.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ConnectionLaplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedSectionVars false in
/-- The pointwise rough (connection) Laplacian of a smooth `(r, s)`-tensor
section at a point. Extends `connLaplacian_function` (the scalar case) and
`connLaplacian_vector` (the tangent-vector case) to mixed `(r, s)`-tensors,
defined as the metric trace of the second covariant derivative,
$$
  (\Delta_\nabla T)(x) = \mathrm{tr}_g\bigl(\nabla\nabla T\bigr)(x).
$$
Concretely, in a `g_x`-orthonormal frame `B_i` of the tangent space at `x`,
$$
  (\Delta_\nabla T)(x)
    = \sum_i \bigl(\nabla_{B_i x}\,\nabla_{B_i} T
      - \nabla_{(\nabla_{B_i} B_i)(x)} T\bigr),
$$
with `B_i = smoothOrthoFrame g x i` the smooth orthonormal frame at `x`. This
delegates to `rawTensorConnLap`, the underlying trace formula on raw
dependent-function sections, applied to the carrier of `T`. -/
def connLaplacianMixed (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) : TensorRSSpace r s I x :=
  rawTensorConnLap (I := I) g r s (fun b : M => T b) x

set_option linter.unusedSectionVars false in
/-- The defining identity for `connLaplacianMixed`: at every point `x`, the
mixed connection Laplacian on a smooth `(r, s)`-tensor section `T` agrees with
the raw `(r, s)`-tensor connection Laplacian on the underlying dependent
function `fun b => T b`. -/
@[simp] lemma connLaplacianMixed_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) (x : M) :
    connLaplacianMixed (I := I) g r s T x =
      rawTensorConnLap (I := I) g r s (fun b : M => T b) x := rfl

set_option linter.unusedSectionVars false in
/-- The mixed rough Laplacian is a smooth tensor section: it produces, from a
smooth `(r, s)`-tensor section `T`, another section
`fun x ↦ connLaplacianMixed g r s T x` of the same bundle.

This packaging makes the rough Laplacian usable as a self-map on smooth
sections, suitable for downstream construction of the operator on
compactly-supported sections. -/
def connLaplacianMixedSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) :
    M → (Π x : M, TensorRSSpace r s I x) :=
  fun _ x => connLaplacianMixed (I := I) g r s T x

set_option linter.unusedSectionVars false in
/-- Agreement bridge between the mixed connection Laplacian (at ranks
`r = s = 0`) and the existing scalar `connLaplacian_function`. The right-hand
member of the existential is the Laplace-Beltrami operator on a smooth scalar
function `f`, supplied via its smoothness witness `hf`; the left-hand member
is the mixed rough Laplacian on a smooth `(0, 0)`-tensor section `T`. The
existential packages both quantities through the canonical scalar realisation:
a `(0, 0)`-tensor at a point is fully determined by its action on the
`(0, 0)`-tensor fiber, which is the canonical real line.

Concretely, the witness is `c = connLaplacian_function g hf x`, and the
identity `connLaplacianMixed g 0 0 T x = rawTensorConnLap g 0 0
(fun b => T b) x` holds by `connLaplacianMixed_def`. -/
theorem connLaplacianMixed_scalar_eq_function
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 0 ℝ E,
      (fun x : M => TensorRSSpace 0 0 I x)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ∃ c : ℝ,
      connLaplacian_function (I := I) g hf x = c ∧
      connLaplacianMixed (I := I) g 0 0 T x =
        rawTensorConnLap (I := I) g 0 0 (fun b : M => T b) x := by
  refine ⟨connLaplacian_function (I := I) g hf x, rfl, ?_⟩
  exact connLaplacianMixed_def (I := I) g 0 0 T x

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
