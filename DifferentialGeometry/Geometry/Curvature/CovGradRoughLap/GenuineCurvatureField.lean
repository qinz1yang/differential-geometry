import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup

/-!
# Smooth genuine third-order curvature fields and finite-sum section lemmas

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file packages the two genuine curvature contributions of the
order-`2` rough-Laplacian / covariant-gradient commutator defect as honest smooth
compactly-supported `(0, s + 1)`-tensor fields, together with the finite-sum compatibility
lemmas for `SmoothCcTensor` that the section-level genuine/bracket split consumes.

## Finite-sum section lemmas

The wrapper `SmoothCcTensor g r s` carries its `AddCommGroup` structure through the injective
projection to the underlying smooth section (`SmoothCcTensor.toSectionAddHom`). The two
finite-sum lemmas `SmoothCcTensor.toSection_sum` / `SmoothCcTensor.toFun_sum` push a finite
`Finset.sum` of `SmoothCcTensor`s through the section / function coercion; both are immediate
from `map_sum` on the relevant additive monoid homomorphism. They let the genuine curvature
field, defined as a frame sum of curvature contractions, be read fibrewise as the corresponding
sum of fibre values.

## The smooth genuine curvature fields

For a smooth `(0, s)`-tensor section `S` and a smooth global tangent field `W`, the genuine
curvature contributions of the directional commutator defect are:

* the pure-Riemann contraction `R(Bᵢ, W)(∇_{Bᵢ} S)` summed over a fixed smooth orthonormal frame
  `Bᵢ := smoothOrthoFrame g α i` — packaged via `curvatureContraction` of the gradient field
  `∇S = covGrad g 0 s S`;
* the differentiated-curvature contraction `∇_{Bᵢ}(R(Bᵢ, W) S)` — packaged via
  `covGradCurvatureContraction` of `S`.

Both are honest smooth compactly-supported sections (`curvatureContraction` /
`covGradCurvatureContraction` are smooth by `riemannSec_contMDiff`; the frame fields are smooth by
`smoothOrthoFrame_smooth` and `smoothExtensionTangent_contMDiff`), and on the closed manifold they
have compact support automatically. Summing over the frame index `i` produces the two genuine
fields `genuineRiemannField` and `genuineCovRiemannField`.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s`
raises the tensor rank from `(0, s)` to `(0, s + 1)`; all fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothCcTensor

set_option linter.unusedSectionVars false in
/-- The additive monoid homomorphism from `SmoothCcTensor g r s` to the underlying
function `M → TensorRSModel r s ℝ E`. -/
def toFunAddHom {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    SmoothCcTensor g r s →+ (M → TensorRSModel r s ℝ E) where
  toFun := fun S => S.toFun
  map_zero' := SmoothCcTensor.toFun_zero
  map_add' := SmoothCcTensor.toFun_add

set_option linter.unusedSectionVars false in
/-- **A finite sum of `SmoothCcTensor`s, read through the section coercion.** The underlying
smooth section of a finite `Finset.sum` of `SmoothCcTensor`s is the corresponding sum of the
underlying sections. Immediate from `map_sum` on `SmoothCcTensor.toSectionAddHom`. -/
lemma toSection_sum {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {ι : Type*} (t : Finset ι) (F : ι → SmoothCcTensor g r s) :
    (∑ i ∈ t, F i).toSection = ∑ i ∈ t, (F i).toSection :=
  map_sum (SmoothCcTensor.toSectionAddHom (I := I) (M := M) (g := g) (r := r) (s := s)) F t

set_option linter.unusedSectionVars false in
/-- **A finite sum of `SmoothCcTensor`s, read through the function coercion.** The underlying
function of a finite `Finset.sum` of `SmoothCcTensor`s is the corresponding sum of the underlying
functions. Immediate from `map_sum` on `SmoothCcTensor.toFunAddHom`. -/
lemma toFun_sum {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {ι : Type*} (t : Finset ι) (F : ι → SmoothCcTensor g r s) :
    (∑ i ∈ t, F i).toFun = ∑ i ∈ t, (F i).toFun :=
  map_sum (SmoothCcTensor.toFunAddHom (I := I) (M := M) (g := g) (r := r) (s := s)) F t

set_option linter.unusedSectionVars false in
/-- **A finite sum of `SmoothCcTensor`s, read fibrewise through the section coercion.** The
underlying section value at `x` of a finite `Finset.sum` of `SmoothCcTensor`s is the
corresponding sum of fibre values. This is `toSection_sum` evaluated at `x` through the
`ContMDiffSection` finite-sum coercion. -/
lemma toSection_sum_apply {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {ι : Type*} (t : Finset ι) (F : ι → SmoothCcTensor g r s) (x : M) :
    (∑ i ∈ t, F i).toSection x = ∑ i ∈ t, (F i).toSection x := by
  rw [toSection_sum]
  have hcoe : (⇑(∑ i ∈ t, (F i).toSection) :
        Π x : M, TensorRSSpace r s I x) =
      ∑ i ∈ t, (⇑((F i).toSection) : Π x : M, TensorRSSpace r s I x) :=
    map_sum (ContMDiffSection.coeAddHom I (TensorRSModel r s ℝ E) ∞
      (fun x : M => TensorRSSpace r s I x)) (fun i => (F i).toSection) t
  calc (∑ i ∈ t, (F i).toSection) x
      = (⇑(∑ i ∈ t, (F i).toSection) : Π x : M, TensorRSSpace r s I x) x := rfl
    _ = (∑ i ∈ t, (⇑((F i).toSection) : Π x : M, TensorRSSpace r s I x)) x := by rw [hcoe]
    _ = ∑ i ∈ t, (F i).toSection x := Finset.sum_apply x t _

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
