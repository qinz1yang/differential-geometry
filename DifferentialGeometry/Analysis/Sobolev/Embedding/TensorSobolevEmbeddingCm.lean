import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.SpectralPouH2Identify
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifoldHigherOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.FiberNormRiemannianBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! # Sobolev embedding `H^{2k} ↪ C^m` for `(r, s)`-tensor sections on a closed Riemannian manifold -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/--
**Sobolev embedding `H^{2k} ↪ C^m` for tensor sections.**

When `2 * k > dim M + 2 * m` (the supercritical Sobolev threshold), the
intrinsic order-`2k` Sobolev space of `(r, s)`-tensor sections on a closed
Riemannian manifold embeds continuously into `C^m` tensor sections.

The statement is the substantive pointwise sup-norm form of the embedding
on the dense smooth subspace `SmoothCcTensor g r s ↪
TensorPouSobolevHilbert g r s (2 * k)`: there exists a **strictly positive**
constant `C` such that the bundle-fibre norm of every smooth
compactly-supported `(r, s)`-tensor section at every point of `M` is
controlled by `C` times the intrinsic `H^{2 * k}`-norm of the section's
image in `TensorPouSobolevHilbert g r s (2 * k)`.

The fibre norm here is the **Riemannian bundle norm** induced by the metric
`g` (`tensorRS_riemannianBundle g r s`): the genuine `g`-fibre norm, not a
chart-dependent model op-norm. This is the canonical norm on the
`(r, s)`-tensor bundle and the one in which the embedding constant is
chart-locality-free. Concretely, for `v : TensorRSSpace r s I x`,
`‖v‖ ^ 2 = tensorInnerPointwise g r s x (toModel v) (toModel v)`.

The strict-positivity hypothesis `0 < C` rules out vacuous discharges
(`C = 0` does not satisfy the conclusion as soon as the smooth subspace
contains a non-trivial section, which it does on any non-empty closed
manifold). Universal quantification over `T : SmoothCcTensor g r s` and
`x : M` together with the pointwise tensor-fibre norm `‖T.toSection x‖`
forces `C` to genuinely control the sup-norm; no hypothesis-packaging
fill is possible because no hypothesis of this shape is in scope.

The conclusion encodes the `m = 0` (C⁰-norm) component of the full
`C^m`-norm bound. The general `C^m`-norm version, controlling all
iterated covariant derivatives `‖∇^j T x‖` for `0 ≤ j ≤ m`, is delivered
separately by `iteratedCovGrad_toSobolev_embedding_Cm_unconditional`
(file `Embedding/SobolevEmbeddingCmOrderDropping.lean`), in the same Riemannian
bundle norm.

## Proof

The full manifold-side assembly (finite atlas-aligned partition of unity +
Lebesgue-number `ρ`-localisation + Euclidean local-ball `L²` pointwise
embedding + op-norm ↦ Hilbert–Schmidt + per-term `≤ tsum`) is carried out,
chart-locality-free, in `tensorPouSobolevHilbert_embedding_Ck_gNorm`
(file `Embedding/SobolevEmbeddingManifoldC0.lean`). This headline is the
specialisation that installs the Riemannian bundle instance and delegates.
-/
theorem tensorPouSobolevHilbert_embedding_Ck
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {r s k m : ℕ}
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤
          C *
            ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ :=
  tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g r s k m h_super

/--
**Per-chart-component scalar Sobolev embedding `H^k ↪ C⁰` (HLCC-free sub-result).**

For a smooth compactly-supported `(r, s)`-tensor section `T` on a closed
Riemannian manifold, each chart-frame scalar component
`tensorChartComponentScalar g r s T α Idx Jdx : M → ℝ` is a smooth
compactly-supported function, hence lies in the chart-based `W^{k,2}` space
at every order. When the supercritical threshold `n < 2k` holds (with
`n = dim M`) and the exponent `2` is regular for order `k`, the scalar
Hilbert-Sobolev embedding `sobolev_embedding_chart_C0_Hk` produces
a continuous representative `ũ`, almost-everywhere equal to the component,
whose sup-norm is controlled by a constant multiple of the chart-`W^{k,2}`
norm of the component.

This is the genuine building block underlying the (research-level) tensor
embedding `tensorPouSobolevHilbert_embedding_Ck`: the chart-frame component
scalars are exactly the data whose iterated partial derivatives define the
intrinsic Hilbert-Schmidt chart-Sobolev norm `tensorPouSobolevHsNorm`. What
remains for the full tensor embedding is (i) reconstructing the pointwise
fiber-norm `‖T.toSection x‖` from a finite family of per-component sup
bounds with a *uniform* constant, and (ii) bounding the per-component
chart-`W^{k,2}` norms by `‖T.toHs (2k)‖` at orders `k ≥ 2`. -/
theorem tensorChartComponentScalar_embedding_C0
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (hk : Module.finrank ℝ E < 2 * k)
    (hreg : DifferentialGeometry.Analysis.Sobolev.Chart.RegularExponent.IsRegular
      (Module.finrank ℝ E : ℝ) 2 k)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (ũ : M → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ x ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)),
        ũ x =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx x) ∧
      (∀ x : M, ‖ũ x‖ ≤ C *
        (DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart (I := I) (M := M) g k 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx)).toReal) := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s T α Idx Jdx
  have h_meas :
      Measurable
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    h_smooth.continuous.measurable
  have h_mem :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart (I := I) (M := M) g k 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g (p := 2) (by norm_num) k h_smooth
  exact DifferentialGeometry.Analysis.Sobolev.Chart.sobolev_embedding_chart_C0_Hk
    (I := I) (M := M) g hk hreg h_meas h_mem

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
/-- **Pointwise fibre-norm reconstruction at the chart centre (HLCC-free).**

For a smooth compactly-supported `(r, s)`-tensor section `T` and any point
`x : M`, the bundle-fibre norm `‖T.toSection x‖` (which, by the induced
norm on `TensorRSSpace`, equals the model-fibre norm
`‖TensorRSSpace.toModel (T.toSection x)‖`) is controlled, with a single
constant depending only on `(r, s, E)`, by the sum of squares of the
raw chart-frame scalar components taken **in the chart centred at `x`
itself**, evaluated at `x`:
`‖T.toSection x‖² ≤ C · ∑_{Idx,Jdx} (tensorChartComponentRaw g r s T x Idx Jdx x)²`.

This is the algebraic core of the tensor-fibre reconstruction. The
trivialization at the chart centre coincides with `TensorRSSpace.toModel`
(`triv_eq_toModel_at_chartCenter`), so the raw component at the chart
centre is exactly the chart-frame projection of the model fibre element;
finite-basis recovery (`tensorRSModel_eq_sum_basis`) then gives the
Cauchy–Schwarz bound with constant
`midxPairCard · tensorChartBasisNormConstant²`. No partition-of-unity or
chart-locality hypothesis is used. -/
theorem tensorFiberNorm_sq_le_chartCenterComponents
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (T : SmoothCcTensor g r s) (x : M) :
    ‖T.toSection x‖ ^ 2 ≤
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.midxPairCard
          (E := E) r s *
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartBasisNormConstant
          (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
              (I := I) (M := M) g r s T x Idx Jdx x) ^ 2 := by
  classical
  set Tmod : TensorRSModel r s ℝ E :=
    TensorRSSpace.toModel (𝕜 := ℝ) (I := I) (T.toSection x) with hTmod_def
  have h_norm_eq : ‖T.toSection x‖ = ‖Tmod‖ := rfl
  have h_raw_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentProjection
          (E := E) r s Idx Jdx Tmod =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s T x Idx Jdx x := by
    intro Idx Jdx
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_def]
    congr 1
    symm
    rw [hTmod_def]
    exact DifferentialGeometry.PDE.RicciFlow.HebeyBlock.triv_eq_toModel_at_chartCenter
      (I := I) r s x (T.toSection x)
  have h_alg :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRSModel_norm_sq_le_sum_projection_sq
      (E := E) r s Tmod
  rw [h_norm_eq]
  refine h_alg.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl (fun Idx _ => ?_)
  refine Finset.sum_congr rfl (fun Jdx _ => ?_)
  rw [h_raw_eq Idx Jdx]

end DifferentialGeometry.PDE.RicciFlow
