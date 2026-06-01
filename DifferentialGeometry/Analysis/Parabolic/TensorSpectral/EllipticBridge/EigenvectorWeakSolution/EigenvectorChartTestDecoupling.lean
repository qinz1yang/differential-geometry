import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightLimit
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.WeakSolutionHeadline

/-!
# Decoupling the test section from the cross-term chart components

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, fix a chart center
`α : M`, a component multi-index `P₀`, and a scalar test function `ψ` on the
Euclidean chart target. Write `ζ_α := chartAtlasPOU I M α` for the chart-atlas
partition-of-unity weight, `χ := chartTestPullback I α ψ` for the manifold-side
chart bump attached to `ψ`, and `S := rotatedTestSection g r s α P₀ χ` for the
inverse-Gram-rotated tensor test section.

The covariant-Leibniz CROSS terms of the per-approximant chart-bilinear identity
are chart-pulled (by `tensorCovDerivCrossLeft_integral_eq_chartPull` and
`tensorCovDerivCrossRight_integral_eq_chartPull`) into single-chart integrals
that couple the eigenvector-side data to the TEST-SECTION-side raw chart
components:

* cross-left: `tensorComponentEuclid g r (s + 1)
  (prependCovGradSlot g r s ζ_α S) α Q`;
* cross-right: `tensorComponentEuclid g r s
  (covDerivAlongGrad g r s S ζ_α) α Q`.

To collapse the downstream variational identity into a single
`∫ densityOnEuclid · f_chart · ψ` (plus a principal `∫ … · ∂ψ` term) with a
TEST-INDEPENDENT `f_chart`, those test-section-side chart components must be
DECOUPLED — written as explicit finite combinations of `ψ` and its
chart-Euclidean partials `euclidPartial l ψ`, with test-independent `C^∞`
coefficients. This file proves those decoupling identities.

## The cross-left decoupling

`prependCovGradSlot g r s ζ S` carries the exterior derivative `dζ` in its
leftmost covariant slot, with `S` UN-differentiated: its directional value is
`v ↦ (extDerivFun ζ x v) • S.toSection x`. Reading the raw chart component at a
component multi-index `Q : CompIdx E r (s + 1)` therefore factors, on the chart
base set, as the scalar `extDerivFun ζ b (chartBasisVecFiber α (Q.2 0) b)` —
which involves no derivative of `S` — times the raw chart component of `S` at
`(Q.1, Matrix.vecTail Q.2)` (`tensorChartComponentRaw_prependCovGradSlot`).

For `S = rotatedTestSection g r s α P₀ χ` the latter component is, by
`rotatedTestSection_chartComp`, the inverse-Gram entry
`covChartMetricGramInv g r s α y (Q.1, vecTail Q.2) P₀` times the chart-pushed
bump `chartPushedRaw I α χ`. So the cross-left chart component is a single
`(test-independent C^∞ coefficient) · chartPushedRaw I α χ` — `χ`
UN-differentiated, no partials.

## The cross-right decoupling

`covDerivAlongGrad g r s S ζ` is the covariant derivative of `S` along the
gradient of `ζ`; for `S = rotatedTestSection g r s α P₀ χ` it DIFFERENTIATES the
test section. Expanding the gradient `gradFun g ζ b` on the chart-`α` frame
`chartBasisVecFiber α m` (`gradChartLocal_eq_gradFun`), the directional
covariant-derivative chart component decomposes — by
`covDerivComponent_eq_euclidPartial_add_lowerOrder` — into a chart-Euclidean
partial of the raw component of `S` plus a zeroth-order Christoffel correction.
For `S = rotatedTestSection g r s α P₀ χ`, the Leibniz split
`euclidPartial_chartPushedRaw_rotatedTestSection_eqOn` of the chart-Euclidean
partial of the rotated test section's push-forward splits the first-order part
into the chart-pushed-bump term and the inverse-Gram-coefficient term. So the
cross-right chart component is a finite sum of
`(test-independent C^∞ coeff) · chartPushedRaw I α χ` plus
`∑ l (test-independent C^∞ coeff) · euclidPartial l (chartPushedRaw I α χ)`.

## The round trip

For `χ := chartTestPullback I α ψ`, the round-trip identities
`chartPushedRaw_chartTestPullback_eqOn` and
`euclidPartial_chartPushedRaw_chartTestPullback_eqOn` rewrite `chartPushedRaw I α
χ` back to `ψ` (and its partials back to `euclidPartial l ψ`) on the chart
target. Composing, the deliverable lemmas express the cross chart components
directly in terms of `ψ` and `euclidPartial l ψ`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The exterior derivative of an `ℝ`-valued function, applied to a tangent
vector, is the manifold-Fréchet derivative: the `NormedSpace.fromTangentSpace`
coercion on the `ℝ` value side is the identity. -/
private lemma extDerivFun_apply_scalar (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [extDerivFun, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.coe_mk]
  rfl

/-- The chart-`α`-trivialisation fibre of a covariant-gradient bundle element
`Φ` (a continuous linear map from a tangent vector to an `(r, s)`-tensor) is, on
the chart source, the continuous linear map post-composing `Φ` (with its tangent
input re-trivialised through `triv_{TM}.symmL`) with the `(r, s)`-tensor-bundle
`continuousLinearMapAt`. This is the `Trivialization.continuousLinearMap`
formula for the hom bundle, holding definitionally. -/
private lemma covGradBundle_trivFibre_eq
    (r s : ℕ) (α : M) (b : M)
    (Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) :
    (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, Φ⟩).2 =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
        (Φ.comp ((trivializationAt E (TangentSpace I) α).symmL ℝ b)) :=
  rfl

/-- **The cross-left chart-component formula.** For a smooth scalar `ζ`, a
smooth compactly-supported `(r, s)`-tensor section `S`, a chart center `α`, and
a component multi-index pair `(Idx, Jdx)` with `Jdx : Fin (s + 1) → Fin n`, the
raw chart-frame scalar component of the covector-prepend section
`prependCovGradSlot g r s ζ S` at `(Idx, Jdx)`, at any chart-source point `b`,
equals the directional derivative `extDerivFun ζ b (chartBasisVecFiber α (Jdx 0)
b)` of `ζ` along the `(Jdx 0)`-th chart-frame basis vector, times the raw chart
component of `S` at `(Idx, Matrix.vecTail Jdx)` — the same multi-index with the
leftmost covariant slot removed.

The covector-prepend section carries `dζ` in its leftmost covariant slot with
`S` un-differentiated: its directional value is `v ↦ (extDerivFun ζ b v) •
S.toSection b`. The chart component is read off via the trivialisation
compatibility `covGradBundleEquiv_trivializationAt_eq` of the covariant-gradient
bundle equivalence and the leftmost-slot evaluation of `covGradModelEquiv`. -/
theorem tensorChartComponentRaw_prependCovGradSlot
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s ζ S) α Idx Jdx b =
      extDerivFun (I := I) (ζ : M → ℝ) b
          (chartBasisVecFiber (I := I) α (Jdx 0) b) *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx
          (Matrix.vecTail Jdx) b := by
  classical
  letI : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y)) := tensor0SBundle_topology r
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun y : M => Tensor0SSpace (s + 1) I y)) := tensor0SBundle_topology (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y)) :=
    tensorRSBundle_topology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_fiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_vector r (s + 1)
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb
  have hb_baseS1 : b ∈ (trivializationAt (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) α).baseSet := by
    change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun y : M => Tensor0SSpace (s + 1) I y) α).baseSet)
    exact ⟨hb_base, hb_base⟩
  set Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    (extDerivFun (I := I) (ζ : M → ℝ) b).smulRight (S.toSection b) with hΦ_def
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [prependCovGradSlot_toSection_apply (I := I) (M := M) g r s ζ S b]
  rw [show ((extDerivFun (I := I) (ζ : M → ℝ) b).smulRight (S.toSection b)) = Φ
    from rfl]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
    (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hb_baseS1]
  beta_reduce
  rw [covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s α hb_base Φ]
  rw [tensorChartComponentProjection_apply,
    covGradModelEquiv_apply (E := E) r s]
  rw [covGradBundle_trivFibre_eq (I := I) (M := M) r s α b Φ]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hsymmL : (trivializationAt E (TangentSpace I) α).symmL ℝ b
      ((chartModelBasis E) (Jdx 0)) =
      chartBasisVecFiber (I := I) α (Jdx 0) b := rfl
  rw [hsymmL]
  rw [hΦ_def, ContinuousLinearMap.smulRight_apply]
  rw [map_smul, ContinuousLinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1

/-- On the Euclidean chart target the directional derivative of a smooth scalar
`ζ` along the `m`-th chart-frame basis vector, read at the chart-source preimage
of `y`, equals the `m`-th chart-Euclidean partial derivative `euclidPartial m`
of the Euclidean push-forward `chartPushedRaw I α ζ` of `ζ`.

The exterior derivative of a scalar is the manifold-Fréchet derivative
(`extDerivFun_apply_scalar`); along the chart-frame basis vector it is, by
`mfderiv_chartBasisVecFiber_of_mdifferentiableAt`, the chart-coordinate partial
of `scalarOnE`. The chain rule through the linear isometry `toEuclidean.symm`
transports this to the Euclidean chart-target partial. -/
private lemma partialDeriv_scalarOnE_eq_euclidPartial
    (f : M → ℝ) (α : M) (m : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    partialDeriv (E := E) m (scalarOnE (I := I) α f)
        (extChartAt I α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      euclidPartial (E := E) m (chartPushedRaw I α f) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  rw [euclidPartial_def]
  have hpushed_eq :
      chartPushedRaw I α f =ᶠ[𝓝 y]
        ((scalarOnE (I := I) α f) ∘ (toEuclidean (E := E)).symm) := by
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    filter_upwards [hopen.mem_nhds hy] with z hz
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α f hz]
    rfl
  rw [Filter.EventuallyEq.fderiv_eq hpushed_eq]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv
    (f := scalarOnE (I := I) α f) (x := y)]
  rw [ContinuousLinearMap.comp_apply]
  rw [show (toEuclidean (E := E)).symm.toContinuousLinearMap
      (EuclideanSpace.single m (1 : ℝ)) = (chartModelBasis E) m from by
    rw [chartModelBasis_apply]; rfl]
  rw [partialDeriv]
  rw [show (toEuclidean (E := E)).symm y = extChartAt I α b from hphi_b.symm]

private lemma extDerivFun_chartBasisVecFiber_eq_euclidPartial
    (ζ : C^∞⟮I, M; ℝ⟯) (α : M)
    (m : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    extDerivFun (I := I) (ζ : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartBasisVecFiber (I := I) α m
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      euclidPartial (E := E) m (chartPushedRaw I α (ζ : M → ℝ)) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  rw [extDerivFun_apply_scalar (I := I) (ζ : M → ℝ) b
    (chartBasisVecFiber (I := I) α m b)]
  rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) α
    (ζ.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
    hb_chart hb_int m]
  exact partialDeriv_scalarOnE_eq_euclidPartial (I := I) (M := M)
    (ζ : M → ℝ) α m hy

/-- The directional covariant derivative `tensorCovDerivAt g r s S b` is a
continuous linear map in the direction: it distributes over a finite sum of
scalar-weighted directions. -/
private lemma tensorCovDerivAt_sum_smul_dir
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (b : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) (v : Fin (Module.finrank ℝ E) → E) :
    tensorCovDerivAt (I := I) (M := M) g r s S b
        (∑ m : Fin (Module.finrank ℝ E), c m • v m) =
      ∑ m : Fin (Module.finrank ℝ E),
        c m • tensorCovDerivAt (I := I) (M := M) g r s S b (v m) := by
  classical
  rw [tensorCovDerivAt_def]
  rw [show (∑ m : Fin (Module.finrank ℝ E), c m • v m) =
      (∑ m : Fin (Module.finrank ℝ E), c m • v m :
        TangentSpace I b) from rfl]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul]
  rfl

/-- The chart-source preimage of a Euclidean-chart-target point lies in the
chart-`α` Levi-Civita good set. -/
private lemma symm_mem_chartLeviCivitaGoodSet
    (α : M) {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      chartLeviCivitaGoodSet (I := I) α := by
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  refine ⟨⟨?_, ?_⟩, hb_int⟩
  · rw [extChartAt_source]; exact hb_chart
  · rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart

/-- **The cross-right chart-component formula.** For a smooth scalar `ζ`, a
smooth compactly-supported `(r, s)`-tensor section `S`, a chart center `α`, a
component multi-index pair `(Idx, Jdx)`, and a Euclidean-chart-target point `y`,
the raw chart-frame scalar component of the covariant derivative
`covDerivAlongGrad g r s S ζ` of `S` along the gradient of `ζ`, read at the
chart-source preimage of `y`, equals the finite sum over chart directions `m` of
the gradient chart-frame coefficient `gradChartCoeff g α ζ m` times the sum of
the `m`-th chart-Euclidean partial derivative of the Euclidean push-forward of
the raw component of `S` and the zeroth-order Christoffel correction term
`covDerivLowerOrderTerm g r s S α m Idx Jdx`.

The directional covariant derivative is continuous-linear in the direction; the
gradient expands on the chart-`α` frame `chartBasisVecFiber α m` with
coefficients `gradChartCoeff g α ζ m`. Each frame-directional chart component is
the chart-coordinate covariant-derivative component formula
`covDerivComponent_eq_euclidPartial_add_lowerOrder`. -/
theorem tensorChartComponentRaw_covDerivAlongGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (covDerivAlongGrad (I := I) (M := M) g r s S ζ) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      ∑ m : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α (ζ : M → ℝ) m
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          (euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
              y +
            covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
    symm_mem_chartLeviCivitaGoodSet (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [covDerivAlongGrad_toSection_apply (I := I) (M := M) g r s S ζ b]
  have hgrad : gradFun (I := I) g (ζ : M → ℝ) b =
      ∑ m : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α (ζ : M → ℝ) m b •
          chartBasisVecFiber (I := I) α m b := by
    rw [← gradChartLocal_eq_gradFun (I := I) g α
      (ζ.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
      hb_base hb_int]
    rfl
  rw [hgrad]
  rw [tensorCovDerivAt_sum_smul_dir (I := I) (M := M) g r s S b
    (fun m => gradChartCoeff (I := I) g α (ζ : M → ℝ) m b)
    (fun m => chartBasisVecFiber (I := I) α m b)]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul, map_smul, smul_eq_mul]
  congr 1
  rw [tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
    g r s S α m hb_good]
  exact covDerivComponent_eq_euclidPartial_add_lowerOrder (I := I) (M := M)
    g r s S α m Idx Jdx hy

/-- **The cross-left test-decoupling coefficient.** For a chart center `α`,
ranks `(r, s)`, a base component multi-index `P₀ : CompIdx E r s`, and a target
component multi-index `Q : CompIdx E r (s + 1)`, this is the test-independent
`C^∞` Euclidean coefficient that multiplies the chart-pushed bump in the
decoupled cross-left chart component: the `(Q.2 0)`-th chart-Euclidean partial
derivative of the Euclidean push-forward of the chart-atlas partition-of-unity
weight, times the inverse-Gram entry `covChartMetricGramInv g r s α ·
(Q.1, Matrix.vecTail Q.2) P₀`. -/
noncomputable def crossLeftTestCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r (s + 1)) : EuclN → ℝ :=
  fun y =>
    euclidPartial (E := E) (Q.2 0)
        (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
      covChartMetricGramInv (I := I) (M := M) g r s α y
        (Q.1, Matrix.vecTail Q.2) P₀

/-- Unfolding lemma for `crossLeftTestCoeff`. -/
lemma crossLeftTestCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r (s + 1)) (y : EuclN) :
    crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y =
      euclidPartial (E := E) (Q.2 0)
          (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
        covChartMetricGramInv (I := I) (M := M) g r s α y
          (Q.1, Matrix.vecTail Q.2) P₀ := rfl

/-- **The cross-left test-decoupling coefficient is `C^∞`.** On the Euclidean
chart target the cross-left coefficient `crossLeftTestCoeff` is `ContDiffOn ℝ ∞`:
it is the product of the chart-Euclidean partial of the `C^∞` chart-pushed
partition-of-unity weight (`euclidPartial_contDiffOn_target` of
`chartPushedRaw_bump_contDiffOn`) and the `C^∞` inverse-Gram entry
(`covChartMetricGramInv_entry_contDiffOn`). -/
theorem crossLeftTestCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r (s + 1)) :
    ContDiffOn ℝ ∞ (crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hbump : ContDiffOn ℝ ∞
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_bump_contDiffOn (I := I) (M := M) α
      (chartAtlasPOU I M α).contMDiff.contMDiffOn
  have hpartial : ContDiffOn ℝ ∞
      (euclidPartial (E := E) (Q.2 0)
        (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_contDiffOn_target (I := I) (M := M) α (Q.2 0) hbump
  have hGinv : ContDiffOn ℝ ∞
      (fun y : EuclN => covChartMetricGramInv (I := I) (M := M) g r s α y
        (Q.1, Matrix.vecTail Q.2) P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α
      (Q.1, Matrix.vecTail Q.2) P₀
  exact hpartial.mul hGinv

/-- **The cross-left test-decoupling.** For a chart center `α`, ranks `(r, s)`, a
base component multi-index `P₀`, a scalar bump `χ` smooth on the chart source
with closed support inside it, and a target component multi-index
`Q : CompIdx E r (s + 1)`, the cross-left chart component
`tensorComponentEuclid g r (s + 1) (prependCovGradSlot g r s (chartAtlasPOU I M
α) (rotatedTestSection g r s α P₀ χ)) α Q` agrees, on the Euclidean chart
target, with the test-independent `C^∞` coefficient `crossLeftTestCoeff` times
the chart-pushed bump `chartPushedRaw I α χ`.

`prependCovGradSlot` carries the partition-of-unity weight differentiated and the
rotated test section un-differentiated; `tensorChartComponentRaw_prependCovGradSlot`
splits the chart component into the directional derivative of the weight times
the raw chart component of the rotated test section, which
`rotatedTestSection_chartComp` resolves to the inverse-Gram entry times the
chart-pushed bump. -/
theorem tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r (s + 1)) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt))
        α Q)
      (fun y => crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
        chartPushedRaw I α χ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r (s + 1)
    (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
      (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)) α Q hy]
  have hb_chart : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [tensorChartComponentRaw_prependCovGradSlot (I := I) (M := M) g r s
    (chartAtlasPOU I M α)
    (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α Q.1 Q.2
    hb_chart]
  rw [show tensorChartComponentRaw (I := I) (M := M) g r s
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α Q.1
        (Matrix.vecTail Q.2)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      tensorChartComponentRaw (I := I) (M := M) g r s
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α
        (Q.1, Matrix.vecTail Q.2).1 (Q.1, Matrix.vecTail Q.2).2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) from rfl]
  rw [rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀ hχs hχt
    (Q.1, Matrix.vecTail Q.2) hy]
  rw [extDerivFun_chartBasisVecFiber_eq_euclidPartial (I := I) (M := M)
    (chartAtlasPOU I M α) α (Q.2 0) hy]
  simp only [crossLeftTestCoeff_def]
  ring

/-- **The Euclidean gradient chart-frame coefficient.** The chart-frame
coefficient `gradChartCoeff g α ζ m` of the gradient of a smooth scalar `ζ`,
recast as a function on the Euclidean chart target: the inverse-Gram-weighted
combination `∑_j chartInvGramEuclid g α m j · euclidPartial j (chartPushedRaw I α
ζ)` of the chart-Euclidean partials of the Euclidean push-forward of `ζ`. -/
noncomputable def gradChartCoeffEuclid
    (g : SmoothRiemannianMetric I M) (α : M) (ζ : M → ℝ)
    (m : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramEuclid (I := I) g α m j y *
        euclidPartial (E := E) j (chartPushedRaw I α ζ) y

/-- On the Euclidean chart target the gradient chart-frame coefficient
`gradChartCoeff g α ζ m`, read at the chart-source preimage of `y`, equals its
Euclidean recast `gradChartCoeffEuclid g α ζ m`. The inverse-Gram-matrix entry is
the Euclidean inverse-Gram entry (`chartInvGramEuclid`), and the chart-coordinate
partial of `scalarOnE` is the chart-Euclidean partial of the push-forward
(`partialDeriv_scalarOnE_eq_euclidPartial`). -/
theorem gradChartCoeff_eq_gradChartCoeffEuclid
    (g : SmoothRiemannianMetric I M) (α : M) (ζ : M → ℝ)
    (m : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    gradChartCoeff (I := I) g α ζ m
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      gradChartCoeffEuclid (I := I) (M := M) g α ζ m y := by
  classical
  rw [gradChartCoeff_def, gradChartCoeffEuclid]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show chartInvGramMatrix (I := I) g α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) m j =
      chartInvGramEuclid (I := I) g α m j y from by
    rw [chartInvGramEuclid_def, chartInvGramOnE_def]]
  rw [partialDeriv_scalarOnE_eq_euclidPartial (I := I) (M := M) ζ α j hy]

/-- **The Euclidean gradient chart-frame coefficient is `C^∞`.** For a smooth
scalar `ζ`, the coefficient `gradChartCoeffEuclid g α ζ m` is `ContDiffOn ℝ ∞` on
the Euclidean chart target: it is a finite sum of products of the `C^∞` Euclidean
inverse-Gram entries `chartInvGramEuclid` and the chart-Euclidean partials of the
`C^∞` chart-pushed scalar. -/
theorem gradChartCoeffEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {ζ : M → ℝ} (hζ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ (chartAt H α).source)
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (gradChartCoeffEuclid (I := I) (M := M) g α ζ m)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hbump : ContDiffOn ℝ ∞ (chartPushedRaw I α ζ)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_bump_contDiffOn (I := I) (M := M) α hζ
  refine ContDiffOn.sum (fun j _ => ?_)
  exact (chartInvGramEuclid_contDiffOn (I := I) (M := M) g α m j).mul
    (euclidPartial_contDiffOn_target (I := I) (M := M) α j hbump)

/-- On the Euclidean chart target the Christoffel correction
`covDerivLowerOrderTerm g r s (rotatedTestSection …) α m Q.1 Q.2` collapses to
the collapsed coefficient `lowerOrderRotationLOCoeff` times the chart-pushed
bump. Unfolding `covDerivLowerOrderTerm` and substituting the rotated test
section's raw-component identity `rotatedTestSection_chartComp` factors the
chart-pushed bump out of the finite sum. -/
private lemma covDerivLowerOrderTerm_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (m : Fin (Module.finrank ℝ E)) (Q : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
        α m Q.1 Q.2 y =
      lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q y *
        chartPushedRaw I α χ y := by
  classical
  rw [covDerivLowerOrderTerm_def, lowerOrderRotationLOCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀ hχs hχt p hy]
  ring

/-- **The cross-right test-decoupling gradient coefficient.** For a chart center
`α`, ranks `(r, s)`, a base component multi-index `P₀`, a target component
multi-index `Q : CompIdx E r s`, and a chart direction `l`, this is the
test-independent `C^∞` Euclidean coefficient that multiplies the chart-Euclidean
partial `euclidPartial l (chartPushedRaw I α χ)` in the decoupled cross-right
chart component: the `l`-th Euclidean gradient chart-frame coefficient of the
chart-atlas partition-of-unity weight, times the inverse-Gram entry
`gramInvEntry g r s α Q P₀`. -/
noncomputable def crossRightTestGradCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    gradChartCoeffEuclid (I := I) (M := M) g α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) l y *
      gramInvEntry (I := I) (M := M) g r s α Q P₀ y

/-- Unfolding lemma for `crossRightTestGradCoeff`. -/
lemma crossRightTestGradCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) (y : EuclN) :
    crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y =
      gradChartCoeffEuclid (I := I) (M := M) g α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) l y *
        gramInvEntry (I := I) (M := M) g r s α Q P₀ y := rfl

/-- **The cross-right test-decoupling value coefficient.** For a chart center
`α`, ranks `(r, s)`, a base component multi-index `P₀`, and a target component
multi-index `Q : CompIdx E r s`, this is the test-independent `C^∞` Euclidean
coefficient that multiplies the chart-pushed bump `chartPushedRaw I α χ` in the
decoupled cross-right chart component: the finite sum, over chart directions `m`,
of the `m`-th Euclidean gradient chart-frame coefficient of the chart-atlas
partition-of-unity weight, times the sum of the `m`-th chart-Euclidean partial of
the inverse-Gram entry `gramInvEntry g r s α Q P₀` and the collapsed lower-order
coefficient `lowerOrderRotationLOCoeff`. -/
noncomputable def crossRightTestValueCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s) : EuclN → ℝ :=
  fun y =>
    ∑ m : Fin (Module.finrank ℝ E),
      gradChartCoeffEuclid (I := I) (M := M) g α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m y *
        (euclidPartial (E := E) m
            (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
          lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q y)

/-- Unfolding lemma for `crossRightTestValueCoeff`. -/
lemma crossRightTestValueCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s) (y : EuclN) :
    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y =
      ∑ m : Fin (Module.finrank ℝ E),
        gradChartCoeffEuclid (I := I) (M := M) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m y *
          (euclidPartial (E := E) m
              (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
            lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q y) := rfl

/-- **The cross-right test-decoupling gradient coefficient is `C^∞`.** On the
Euclidean chart target `crossRightTestGradCoeff` is `ContDiffOn ℝ ∞`: it is the
product of the `C^∞` Euclidean gradient chart-frame coefficient
`gradChartCoeffEuclid` of the partition-of-unity weight and the `C^∞` inverse-Gram
entry `gramInvEntry`. -/
theorem crossRightTestGradCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (gradChartCoeffEuclid_contDiffOn (I := I) (M := M) g α
      (chartAtlasPOU I M α).contMDiff.contMDiffOn l).mul
    (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀)

/-- **The cross-right test-decoupling value coefficient is `C^∞`.** On the
Euclidean chart target `crossRightTestValueCoeff` is `ContDiffOn ℝ ∞`: it is a
finite sum of products of the `C^∞` Euclidean gradient chart-frame coefficient
`gradChartCoeffEuclid`, the chart-Euclidean partial of the `C^∞` inverse-Gram
entry `gramInvEntry`, and the `C^∞` collapsed lower-order coefficient
`lowerOrderRotationLOCoeff`. -/
theorem crossRightTestValueCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s) :
    ContDiffOn ℝ ∞ (crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ContDiffOn.sum (fun m _ => ?_)
  have hgrad : ContDiffOn ℝ ∞
      (gradChartCoeffEuclid (I := I) (M := M) g α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m)
      (chartTargetEuclid (I := I) (M := M) α) :=
    gradChartCoeffEuclid_contDiffOn (I := I) (M := M) g α
      (chartAtlasPOU I M α).contMDiff.contMDiffOn m
  have hGinvPartial : ContDiffOn ℝ ∞
      (euclidPartial (E := E) m
        (gramInvEntry (I := I) (M := M) g r s α Q P₀))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_contDiffOn_target (I := I) (M := M) α m
      (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀)
  have hLO : ContDiffOn ℝ ∞
      (lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
    lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M) g r s α P₀ m Q
  exact hgrad.mul (hGinvPartial.add hLO)

/-- **The cross-right test-decoupling.** For a chart center `α`, ranks `(r, s)`,
a base component multi-index `P₀`, a scalar bump `χ` smooth on the chart source
with closed support inside it, and a target component multi-index
`Q : CompIdx E r s`, the cross-right chart component
`tensorComponentEuclid g r s (covDerivAlongGrad g r s (rotatedTestSection g r s α
P₀ χ) (chartAtlasPOU I M α)) α Q` agrees, on the Euclidean chart target, with the
test-independent `C^∞` value coefficient `crossRightTestValueCoeff` times the
chart-pushed bump `chartPushedRaw I α χ` plus the finite sum, over chart
directions `l`, of the test-independent `C^∞` gradient coefficient
`crossRightTestGradCoeff` times the chart-Euclidean partial
`euclidPartial l (chartPushedRaw I α χ)`.

`covDerivAlongGrad` differentiates the rotated test section;
`tensorChartComponentRaw_covDerivAlongGrad` writes the chart component as a sum
over chart directions of the gradient chart-frame coefficient times the
chart-Euclidean partial of the raw component of `S` plus the Christoffel
correction. `euclidPartial_chartPushedRaw_rotatedTestSection_eqOn` splits the
chart-Euclidean partial of the rotated test section's push-forward into the
chart-pushed-bump term and the inverse-Gram-coefficient term, and
`covDerivLowerOrderTerm_rotatedTestSection_eqOn` collapses the Christoffel
correction to the chart-pushed bump times the lower-order coefficient. -/
theorem tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r s
        (covDerivAlongGrad (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
          (chartAtlasPOU I M α))
        α Q)
      (fun y => crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          chartPushedRaw I α χ y +
        ∑ l : Fin (Module.finrank ℝ E),
          crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro y hy
  rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s
    (covDerivAlongGrad (I := I) (M := M) g r s
      (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
      (chartAtlasPOU I M α)) α Q hy]
  rw [tensorChartComponentRaw_covDerivAlongGrad (I := I) (M := M) g r s
    (chartAtlasPOU I M α)
    (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α Q.1 Q.2 hy]
  have hterm : ∀ m : Fin (Module.finrank ℝ E),
      gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          (euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α
                  Q.1 Q.2)) y +
            covDerivLowerOrderTerm (I := I) (M := M) g r s
              (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
              α m Q.1 Q.2 y) =
        gradChartCoeffEuclid (I := I) (M := M) g α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m y *
            (euclidPartial (E := E) m
                (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
              lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q y) *
          chartPushedRaw I α χ y +
        gradChartCoeffEuclid (I := I) (M := M) g α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m y *
            gramInvEntry (I := I) (M := M) g r s α Q P₀ y *
          euclidPartial (E := E) m (chartPushedRaw I α χ) y := by
    intro m
    rw [gradChartCoeff_eq_gradChartCoeffEuclid (I := I) (M := M) g α
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m hy]
    rw [show tensorChartComponentRaw (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α Q.1 Q.2 =
        tensorChartComponentRaw (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α
          Q.1 Q.2 from rfl]
    rw [euclidPartial_chartPushedRaw_rotatedTestSection_eqOn (I := I) (M := M)
      g r s α P₀ hχs hχt Q m hy]
    rw [covDerivLowerOrderTerm_rotatedTestSection_eqOn (I := I) (M := M)
      g r s α P₀ hχs hχt m Q hy]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [Finset.sum_add_distrib]
  simp only [crossRightTestValueCoeff_def, crossRightTestGradCoeff_def,
    Finset.sum_mul]

/-- **The cross-left chart component in terms of the Euclidean test function.**
For a Euclidean test function `ψ`, `C^∞` and compactly supported inside the
Euclidean chart target, the cross-left chart component
`tensorComponentEuclid g r (s + 1) (prependCovGradSlot g r s (chartAtlasPOU I M
α) (rotatedTestSection g r s α P₀ (chartTestPullback I α ψ))) α Q` agrees, on the
Euclidean chart target, with the test-independent `C^∞` coefficient
`crossLeftTestCoeff` times `ψ` — no chart-Euclidean partial of `ψ` appears.

Composes the cross-left test-decoupling
`tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_eqOn` with the
round-trip identity `chartPushedRaw_chartTestPullback_eqOn`. -/
theorem tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_chartTestPullback_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (Q : CompIdx E r (s + 1)) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
          (rotatedTestSection (I := I) (M := M) g r s α P₀
            (chartTestPullback (I := I) (M := M) α ψ)
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_supp)))
        α Q)
      (fun y => crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_eqOn
    (I := I) (M := M) g r s α P₀
    (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_supp)
    Q hy]
  beta_reduce
  rw [chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α ψ hy]

/-- **The cross-right chart component in terms of the Euclidean test function.**
For a Euclidean test function `ψ`, `C^∞` and compactly supported inside the
Euclidean chart target, the cross-right chart component
`tensorComponentEuclid g r s (covDerivAlongGrad g r s (rotatedTestSection g r s α
P₀ (chartTestPullback I α ψ)) (chartAtlasPOU I M α)) α Q` agrees, on the
Euclidean chart target, with the test-independent `C^∞` value coefficient
`crossRightTestValueCoeff` times `ψ` plus the finite sum, over chart directions
`l`, of the test-independent `C^∞` gradient coefficient `crossRightTestGradCoeff`
times the chart-Euclidean partial `euclidPartial l ψ`.

Composes the cross-right test-decoupling
`tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_eqOn` with the
round-trip identities `chartPushedRaw_chartTestPullback_eqOn` and
`euclidPartial_chartPushedRaw_chartTestPullback_eqOn`. -/
theorem tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_chartTestPullback_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (Q : CompIdx E r s) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r s
        (covDerivAlongGrad (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀
            (chartTestPullback (I := I) (M := M) α ψ)
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_supp))
          (chartAtlasPOU I M α))
        α Q)
      (fun y => crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          ψ y +
        ∑ l : Fin (Module.finrank ℝ E),
          crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
            euclidPartial (E := E) l ψ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_eqOn
    (I := I) (M := M) g r s α P₀
    (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_supp)
    Q hy]
  beta_reduce
  rw [chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α ψ hy]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [euclidPartial_chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M)
    α ψ l hy]

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
  (P₀ : CompIdx E r s)

example (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E))
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s)
    {b : M} (hb : b ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s ζ S) α Idx Jdx b =
      extDerivFun (I := I) (ζ : M → ℝ) b
          (chartBasisVecFiber (I := I) α (Jdx 0) b) *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx
          (Matrix.vecTail Jdx) b :=
  tensorChartComponentRaw_prependCovGradSlot (I := I) (M := M) g r s ζ S α
    Idx Jdx hb

example {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) (Q : CompIdx E r (s + 1)) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt))
        α Q)
      (fun y => crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
        chartPushedRaw I α χ y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_eqOn
    (I := I) (M := M) g r s α P₀ hχs hχt Q

example {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) (Q : CompIdx E r s) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r s
        (covDerivAlongGrad (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
          (chartAtlasPOU I M α))
        α Q)
      (fun y => crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          chartPushedRaw I α χ y +
        ∑ l : Fin (Module.finrank ℝ E),
          crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_eqOn
    (I := I) (M := M) g r s α P₀ hχs hχt Q

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
