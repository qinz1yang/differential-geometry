import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricFiberData
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Continuity of the metric inner product on continuous tangent-bundle sections

Given a smooth Riemannian metric `g` on a manifold `M` (encoded as a
`SmoothRiemannianMetric I M`, i.e., a `Bundle.ContMDiffRiemannianMetric I ∞ E
(TangentSpace I)`), and two `C^∞` tangent-bundle sections `X Y`, the scalar
function `b ↦ g.inner b (X b) (Y b)` is continuous on `M`.

This is delivered through Mathlib's `Continuous.inner_bundle`, which requires
an `IsContinuousRiemannianBundle` instance on the tangent bundle. Such an
instance is supplied by Mathlib's `RiemannianBundle` mechanism — but installing
it on the tangent bundle creates a typeclass diamond with the project's
default `tangentSpace_normedAddCommGroup` / `tangentSpace_normedSpace`
instances. We resolve the diamond locally using
`attribute [-instance] tangentSpace_normedAddCommGroup tangentSpace_normedSpace`
on a private auxiliary lemma in a section that registers the
`RiemannianBundle (TangentSpace I)` instance built from `g.toRiemannianMetric`.
The scalar conclusion `Continuous (M → ℝ)` does not depend on the disabled
instances, so it survives outside the diamond-handling scope and is exposed
as a public theorem.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

namespace DifferentialGeometry
namespace Tensor
namespace TangentRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Diamond-handling probe

The lemma below installs Mathlib's `RiemannianBundle (TangentSpace I)`
structure derived from `g.toRiemannianMetric`. To avoid a diamond between
the project's `tangentSpace_normedAddCommGroup` / `tangentSpace_normedSpace`
instances and Mathlib's scoped priority-80 `NormedAddCommGroup` /
`NormedSpace` instances coming from `RiemannianBundle`, we locally remove
the project instances. Inside the resulting scope `Continuous.inner_bundle`
becomes applicable, yielding the scalar continuity conclusion.

Since the conclusion `Continuous (fun b : M ↦ g.inner b (X b) (Y b))`
mentions only the topology of `M` and `ℝ`, it is independent of the
`NormedAddCommGroup` / `NormedSpace` instances on each tangent fiber and
therefore survives outside the local-attribute scope.
-/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private lemma continuous_g_inner_aux
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x}
    (hv : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (v x)))
    (hw : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (w x))) :
    Continuous (fun b : M => g.inner b (v b) (w b)) := by

  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩

  have h := Continuous.inner_bundle (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := fun x => x) (v := v) (w := w) hv hw

  refine h.congr ?_
  intro b

  rfl

end TangentRiemannian
end Tensor
end DifferentialGeometry

/-! ## Public theorem

The diamond-handling auxiliary lemma is repackaged as a public theorem
without any reference to the locally disabled instances. The signature uses
only the project's standard tangent-space norm instances, so the result is
freely usable from downstream files. -/

namespace TangentBundle

open scoped Manifold Topology Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Continuity of the scalar function `b ↦ g.inner b (X b) (Y b)` for two
`C^∞` tangent-bundle sections `X Y`. The function value lives in `ℝ`, so the
conclusion is independent of the inner-product structure used internally to
phrase the underlying Mathlib bundle inner-product lemma. -/
theorem continuous_g_inner_of_smooth_sections
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => g.inner b (X b) (Y b)) := by

  have hX : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (X x)) :=
    X.contMDiff.continuous
  have hY : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (Y x)) :=
    Y.contMDiff.continuous
  exact DifferentialGeometry.Tensor.TangentRiemannian.continuous_g_inner_aux
    (I := I) (M := M) g hX hY

end TangentBundle
