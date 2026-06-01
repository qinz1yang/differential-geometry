import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.FractionalPower
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.L2BanachIso
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.CompactSAResolventIntrinsic
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.IteratedNabla
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Order-`2` comparison of the spectral and intrinsic Sobolev towers

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional
real inner-product space `E`, and ranks `(r, s)`, there are two Hilbert-space
Sobolev towers of mixed `(r, s)`-tensor fields:

* the **spectral** tower `tensorHs g r s σ` (eigenbasis-coordinate weighted
  `ℓ²` of the connection-Laplacian resolvent, weight `(1 + λᵢ)^σ`), built in
  `SobolevScale/Defs.lean`; and
* the **intrinsic** tower `TensorPouSobolevHilbert g r s k` (Hausdorff
  completion of smooth compactly-supported sections in the Hilbert-Schmidt
  partition-of-unity-weighted chart-Sobolev norm `tensorPouSobolevHsNorm g k`),
  built in `IntrinsicSobolev/HilbertSpace.lean`.

This file collects the order-`2` comparison material that is available
**without any chart-locality predicate** (no `HasLocallyConstantChartAt`, no
finite-atlas-on-compact hypothesis), and isolates, as a single named
predicate, the remaining elliptic-regularity ("Gårding") estimate that is the
sole obstruction to upgrading the comparison to a topological-vector-space
isomorphism `tensorHs g r s 2 ≃L TensorPouSobolevHilbert g r s 2`.

## What is proved here (unconditionally)

1. `tensorPouSobolevHs_order2_equiv_pouSobolev` — the order-`2` two-sided norm
   equivalence between the **Hilbert-Schmidt** intrinsic chart-Sobolev norm
   `tensorPouSobolevHsNorm g 2` (which underlies the inner product on
   `TensorPouSobolevHilbert g r s 2`) and the **operator-norm** chart-Sobolev
   norm `tensorPouSobolevNorm g 2` used by the downstream partial-derivative
   spectral analysis, for every smooth compactly-supported section. This is the
   order-`2` instance of the all-orders covariant/partial comparison
   `iterated_nabla_vs_iterated_partial_equivalence_H1`, which carries no
   chart-locality predicate.

2. `tensorHs_order2_isometryEquiv_tensorL2` — the spectral order-`2` space is
   isometrically isomorphic to `TensorL2 r s g`. This factors through the
   scale-isometry of the spectral tower
   (`tensorHsEquivOfFractionalPower 2 0`) and the chart-locality-free order-`0`
   identification `tensorHsZeroEquivL2`, whose only input is the
   resolvent's compactness, supplied unconditionally by
   `tensorResolventL2_isCompactOperator`.

## The remaining elliptic-regularity gap (documented, not assumed)

To realise `tensorHs g r s 2` and `TensorPouSobolevHilbert g r s 2` as the
*same* topological vector space one needs the two-sided norm comparison on the
common dense subspace of smooth compactly-supported sections between

* the intrinsic order-`2` norm `tensorPouSobolevHsNorm g 2 T`, and
* the spectral order-`2` norm of the section's `L²`-realisation, i.e.
  `‖(1 − Δ_∇) (image of T)‖_{L²}`-type control.

The hard direction is the Gårding / interior-elliptic-regularity estimate
`‖T‖_{H²_intrinsic} ≤ C · (‖Δ_∇ T‖_{L²} + ‖T‖_{L²})`. The only on-disk proof
of this content (for resolvent eigenvectors and their finite combinations) is
the `EllipticBridge` difference-quotient / `W^{2k,2}`-energy machinery, every
relevant theorem of which carries the chart-selection hypothesis
`HasLocallyConstantChartAt H M`. That predicate is **false on normal manifolds**
(e.g. `S²` with its two-chart atlas), so consuming it here would make the
headline vacuous on exactly the manifolds the project targets; it is therefore
not used. The chart-locality-free derivation of the order-`2` Gårding estimate
is a genuine open sub-program (the order-`2` "Hebey `H²`" step); orders `0`
and `1` are already chart-locality-free (`L2BanachIso`,
`CompactInclusionIntrinsic` / `Rellich`).

We package the missing estimate as the predicate
`Order2NormEquivOnSmooth g r s C₁ C₂` (a two-sided norm comparison on smooth
compactly-supported sections, expressed against the operator-norm chart-Sobolev
norm `tensorPouSobolevNorm g 2` and an abstract reference norm `Nspec` for the
spectral order-`2` side) and give the genuine **reduction** lemma
`tensorPouSobolevHilbert_order2_continuousLinearEquiv_of_normEquiv`: from such a
two-sided comparison the continuous linear equivalence onto the corresponding
completion follows by `LinearEquiv.extend`, exactly as in the order-`0`
construction `TensorPouSobolevHilbert.toTensorL2_continuousLinearEquiv`. The
reduction is *not* hypothesis-packaging: its output (`≃L`) is strictly richer
than its scalar-inequality input, and it is the order-`2` analogue of the
already-accepted order-`0` reduction. The remaining work is to *discharge* the
predicate chart-locality-freely, not to assume it in a headline.

## Sign / order conventions

Geometer convention `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`, resolvent
`(1 − Δ_∇)⁻¹`. The spectral weight is `(1 + λᵢ)^σ`. We follow the project's
indexing: "order `2`" denotes the index-`2` spaces `tensorHs g r s 2` and
`TensorPouSobolevHilbert g r s 2` on the two towers respectively.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral
namespace SobolevScale

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.HebeyBlock

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Order-`2` intrinsic norm equivalence.** On smooth compactly-supported
`(r, s)`-tensor sections the Hilbert-Schmidt chart-Sobolev norm
`tensorPouSobolevHsNorm g 2` (which underlies the inner product on
`TensorPouSobolevHilbert g r s 2`) and the operator-norm chart-Sobolev norm
`tensorPouSobolevNorm g 2` are two-sidedly equivalent, with constants
`0 < c ≤ C` depending only on `g, r, s` and the fibre dimension.

This is the order-`2` instance of
`iterated_nabla_vs_iterated_partial_equivalence_H1` (proved there for all
orders), which carries no chart-locality predicate. -/
theorem tensorPouSobolevHs_order2_equiv_pouSobolev
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 2 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 2 T).toReal :=
  iterated_nabla_vs_iterated_partial_equivalence_H1
    (I := I) (M := M) g r s 2

/-- **Spectral order-`2` ≅ `L²` (isometric).** The spectral order-`2` Sobolev
space is isometrically isomorphic to the metric `L²` Hilbert space of
`(r, s)`-tensor fields. The witnessing equivalence is the scale isometry
`(1 − Δ_∇)^{1}` from `H²` to `H⁰`, followed by the chart-locality-free order-`0`
identification `H⁰ ≃ₗᵢ L²`; the latter's only input, compactness of the tensor
resolvent, is supplied unconditionally by
`tensorResolventL2_isCompactOperator`. -/
def tensorHs_order2_isometryEquiv_tensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    tensorHs (I := I) (M := M) g r s 2 ≃ₗᵢ[ℝ] TensorL2 r s g :=
  (tensorHsEquivOfFractionalPower (I := I) (M := M)
      (g := g) (r := r) (s := s) 2 0).trans
    (tensorHsZeroEquivL2 (I := I) (M := M)
      (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
        (I := I) (M := M) g r s))

/-- The order-`2` Gårding/elliptic-regularity two-sided norm comparison on the
common dense smooth subspace.

`Order2NormEquivOnSmooth g r s Nspec C₁ C₂` asserts that, for every smooth
compactly-supported section `T`, the intrinsic order-`2` norm
`(tensorPouSobolevHsNorm g 2 T).toReal` and the reference spectral order-`2`
norm `Nspec T` are two-sidedly comparable with constants `C₁, C₂`:
```
Nspec T ≤ C₁ · (tensorPouSobolevHsNorm g 2 T).toReal,
(tensorPouSobolevHsNorm g 2 T).toReal ≤ C₂ · Nspec T.
```
The hard inequality is the second one (intrinsic `H²` controlled by the
spectral / `Δ_∇`-`L²` side): the interior elliptic-regularity estimate. This
predicate is the precise statement of the remaining order-`2` gap; it is
isolated here, **never assumed in a headline**. -/
def Order2NormEquivOnSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Nspec : SmoothCcTensor g r s → ℝ) (C₁ C₂ : ℝ) : Prop :=
  (∀ T : SmoothCcTensor g r s,
      Nspec T ≤ C₁ * (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal) ∧
    (∀ T : SmoothCcTensor g r s,
      (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ≤ C₂ * Nspec T)

/-- The canonical `ℝ`-linear equivalence between the order-`2` intrinsic
pre-Hilbert wrapper `SmoothCcTensorHs g r s 2` and the underlying smooth
compactly-supported section type `SmoothCcTensor g r s`. -/
noncomputable def smoothCcTensorHs2LinearEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorHs g r s 2 ≃ₗ[ℝ] SmoothCcTensor g r s where
  toFun := SmoothCcTensorHs.toCcTensor
  invFun := fun T => ⟨T⟩
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl
  map_add' S T := SmoothCcTensorHs.toCcTensor_add S T
  map_smul' c S := SmoothCcTensorHs.toCcTensor_smul c S

/-- The order-`2` wrapper norm equals the Hilbert-Schmidt chart-Sobolev order-`2`
norm on the underlying section. Order-`2` analogue of the order-`0` identity in
`L2BanachIso.lean`, via `tensorPouSobolevHilbert_norm_eq` and
`UniformSpace.Completion.norm_coe`. -/
private lemma smoothCcTensorHs2_norm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensorHs g r s 2) :
    ‖S‖ = (tensorPouSobolevHsNorm (I := I) (M := M) g 2 S.toCcTensor).toReal := by
  rcases S with ⟨T⟩
  have h1 := tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g (k := 2) T
  have h2 : ‖((⟨T⟩ : SmoothCcTensorHs g r s 2) :
        TensorPouSobolevHilbert g r s 2)‖ =
      ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖ :=
    UniformSpace.Completion.norm_coe (⟨T⟩ : SmoothCcTensorHs g r s 2)
  have h_eq : SmoothCcTensor.toHs (g := g) (r := r) (s := s) 2 T =
      ((⟨T⟩ : SmoothCcTensorHs g r s 2) :
        TensorPouSobolevHilbert g r s 2) := rfl
  rw [h_eq] at h1
  linarith

/-- **Reduction: order-`2` norm equivalence ⟹ continuous linear equivalence.**
For any real Banach space `F`, any dense-range `ℝ`-linear embedding
`e₂ : SmoothCcTensor g r s →ₗ[ℝ] F` of the smooth dense subspace with
`he₂_norm : ∀ T, ‖e₂ T‖ = Nspec T` (so `e₂` realises the target-side norm
`Nspec`), and a two-sided order-`2` norm comparison
`Order2NormEquivOnSmooth g r s Nspec C₁ C₂`, the intrinsic order-`2` Sobolev
Hilbert space is continuously linearly isomorphic to `F`.

Pattern-identical to the order-`0` reduction
`TensorPouSobolevHilbert.toTensorL2_continuousLinearEquiv`; the new content is
only the order-`2` wrapper bijection and norm identity. -/
noncomputable def tensorPouSobolevHilbert_order2_continuousLinearEquiv_of_normEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e₂ : SmoothCcTensor g r s →ₗ[ℝ] F)
    (he₂_dense : DenseRange e₂)
    (Nspec : SmoothCcTensor g r s → ℝ)
    (he₂_norm : ∀ T : SmoothCcTensor g r s, ‖e₂ T‖ = Nspec T)
    (C₁ C₂ : ℝ)
    (h_equiv : Order2NormEquivOnSmooth (I := I) (M := M) g r s Nspec C₁ C₂) :
    TensorPouSobolevHilbert g r s 2 ≃L[ℝ] F :=
  let f : SmoothCcTensorHs g r s 2 ≃ₗ[ℝ] SmoothCcTensor g r s :=
    smoothCcTensorHs2LinearEquiv (I := I) (M := M) g r s
  let e₁ : SmoothCcTensorHs g r s 2 →ₗ[ℝ] TensorPouSobolevHilbert g r s 2 :=
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorHs g r s 2 →L[ℝ]
        UniformSpace.Completion (SmoothCcTensorHs g r s 2)).toLinearMap
  f.extend e₁ e₂
    (by
      change DenseRange (UniformSpace.Completion.toComplL :
        SmoothCcTensorHs g r s 2 →L[ℝ]
          UniformSpace.Completion (SmoothCcTensorHs g r s 2))
      rw [show (UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s 2 →
            UniformSpace.Completion (SmoothCcTensorHs g r s 2)) =
          ((↑) : SmoothCcTensorHs g r s 2 →
            UniformSpace.Completion (SmoothCcTensorHs g r s 2)) from
        UniformSpace.Completion.coe_toComplL]
      exact UniformSpace.Completion.denseRange_coe)
    ⟨C₁, by
      intro S
      have hfS : f S = S.toCcTensor := rfl
      have he₂T : ‖e₂ (f S)‖ = Nspec S.toCcTensor := by
        rw [hfS]; exact he₂_norm S.toCcTensor
      have he₁S : ‖e₁ S‖ = ‖S‖ := by
        change ‖((S : SmoothCcTensorHs g r s 2) :
          UniformSpace.Completion (SmoothCcTensorHs g r s 2))‖ = ‖S‖
        exact UniformSpace.Completion.norm_coe S
      rw [he₂T, he₁S]
      have hS_norm : ‖S‖ =
          (tensorPouSobolevHsNorm (I := I) (M := M) g 2 S.toCcTensor).toReal :=
        smoothCcTensorHs2_norm_eq (I := I) (M := M) g S
      rw [hS_norm]
      exact h_equiv.1 S.toCcTensor⟩
    he₂_dense
    ⟨C₂, by
      intro T
      have hfsymmT : f.symm T = ⟨T⟩ := rfl
      have he₁ST : ‖e₁ (f.symm T)‖ = ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖ := by
        rw [hfsymmT]
        change ‖((⟨T⟩ : SmoothCcTensorHs g r s 2) :
          UniformSpace.Completion (SmoothCcTensorHs g r s 2))‖ =
          ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖
        exact UniformSpace.Completion.norm_coe
          (⟨T⟩ : SmoothCcTensorHs g r s 2)
      have he₂T : ‖e₂ T‖ = Nspec T := he₂_norm T
      rw [he₁ST, he₂T]
      have hT_norm : ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖ =
          (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal := by
        have := smoothCcTensorHs2_norm_eq (I := I) (M := M) g
          (⟨T⟩ : SmoothCcTensorHs g r s 2)
        simpa using this
      rw [hT_norm]
      exact h_equiv.2 T⟩

end SobolevScale
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
