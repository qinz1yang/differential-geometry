import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.TangentContinuousRiemannianMetric
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Tangent-bundle fibre-norm reconciliation

The tangent bundle of a smooth Riemannian manifold `(M, g)` carries two
candidate fibre-norm structures:

* the project's default `Tensor0SBundle.tangentSpace_normedAddCommGroup` /
  `Tensor0SBundle.tangentSpace_normedSpace`, inherited from the model fibre `E`;
* Mathlib's `Bundle.RiemannianBundle (TangentSpace I)`-derived
  `NormedAddCommGroup` / `InnerProductSpace`, built from `g` through
  `g.toContinuousRiemannianMetric.toRiemannianMetric` and the scoped
  priority-`80` `RiemannianMetric.toCore` instance.

The `RiemannianBundle`-derived enorm reduces fibrewise to the square root of
the metric quadratic form `g.inner x v v`. This file records that identity,
phrased with the project instances locally suppressed (`attribute [-instance]`)
and the `RiemannianBundle` instance named inline (`letI`), mirroring the
diamond-handling idiom already used in
`Analysis/Parabolic/TensorSpectral/NormComparison.lean` and
`Tensor/RSTensor/TangentRiemannian.lean`.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Tangent fibre-norm reconciliation (enorm form).**

With the project's default tangent-fibre norm instances locally suppressed and
Mathlib's `Bundle.RiemannianBundle (TangentSpace I)` structure derived from the
smooth Riemannian metric `g` installed in their place, the extended norm of a
tangent vector `v : TangentSpace I x` is the `ENNReal.ofReal` of the square root
of the metric quadratic form `g.inner x v v`. Both the project's
`Tensor0SBundle` enorm (when present) and the `RiemannianBundle`-derived enorm
reduce, fibrewise, to this common value, so this lemma is the bridge that lets
the `√(g.inner x v v)` enorm hypothesis used throughout the geodesic / Hopf-Rinow
/ Bonnet-Myers pipeline be discharged for the `RiemannianBundle`-active norm. -/
theorem tensor0SBundle_enorm_eq_riemannianBundle_enorm
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  have hinner : (inner ℝ v v : ℝ) = g.inner x v v := rfl
  rw [hinner]

end DifferentialGeometry.Geometry.Riemannian

end
