import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartTestDecoupling

/-!
# The raw chart-component formula for the section-level covariant gradient

For a closed Riemannian manifold `(M, g)` modelled on a real inner-product space
`E`, ranks `(r, s)`, and a smooth compactly-supported `(r, s)`-tensor section
`S`, the section-level covariant gradient `covGrad g r s S` is a smooth
compactly-supported `(r, s + 1)`-tensor section: the extra covariant slot is the
slot carrying the differentiation direction.

This file proves the **raw chart-component formula** for `covGrad`: the raw
chart-frame `(r, s + 1)`-component of `covGrad g r s S`, read at the
chart-source preimage of a Euclidean-chart-target point `y`, equals a
chart-Euclidean partial derivative of the raw `(r, s)`-component of `S` plus a
zeroth-order Christoffel correction. Concretely, writing
`m := Jdx 0` for the leftmost covariant index of the target multi-index `Jdx`
and `Jdx' := Matrix.vecTail Jdx` for the remaining `Fin s`-tuple,

`tensorChartComponentRaw g r (s + 1) (covGrad g r s S) α Idx Jdx b
  = euclidPartial m (chartPushedRaw I α (tensorChartComponentRaw g r s S α Idx Jdx')) y
    + covDerivLowerOrderTerm g r s S α m Idx Jdx' y`,

with `b := (extChartAt I α).symm (toEuclidean.symm y)`.

## Proof route

The underlying section value of `covGrad g r s S` at `b` is, by
`covGrad_toSection_apply`, the image under the covariant-gradient bundle
equivalence `covGradBundleEquiv r s b` of the bundled directional covariant
derivative `Φ := tensorRSCovariantDerivative I M r s (LeviCivita g) S.toSection b`.

Reading the raw chart-frame scalar component at rank `(r, s + 1)`, the
trivialisation-compatibility identity `covGradBundleEquiv_trivializationAt_eq`
reduces the chart-`α`-trivialised representation of the covariant-gradient
bundle equivalence to the constant model equivalence `covGradModelEquiv`, whose
leftmost-slot evaluation `covGradModelEquiv_apply` reads the direction off the
slot indexed by `Jdx 0`. The chart component therefore factors as the
`(r, s)`-component projection, at `(Idx, Matrix.vecTail Jdx)`, of the
directional covariant derivative `Φ` taken along the `(Jdx 0)`-th chart-frame
basis vector.

That directional covariant derivative is `tensorCovDerivAt g r s S b
(chartBasisVecFiber α (Jdx 0) b)`, which on the chart-`α` Levi-Civita good set
equals the chart-coordinate covariant derivative
(`tensorCovDerivAt_eq_chartTensorRSCovariantDerivative`). Its raw chart-frame
component is then the chart-Euclidean partial plus the Christoffel correction by
the chart-coordinate covariant-derivative component formula
`covDerivComponent_eq_euclidPartial_add_lowerOrder`.

This is the direct `covGrad`-analogue of `tensorChartComponentRaw_prependCovGradSlot`.

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

/-- The chart-`α`-trivialisation fibre of a covariant-gradient bundle element
`Φ` (a continuous linear map from a tangent vector to an `(r, s)`-tensor) is the
continuous linear map post-composing `Φ` (with its tangent input re-trivialised
through `triv_{TM}.symmL`) with the `(r, s)`-tensor-bundle
`continuousLinearMapAt`. -/
private lemma covGradBundle_trivFibre_eq'
    (r s : ℕ) (α : M) (b : M)
    (Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) :
    (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, Φ⟩).2 =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
        (Φ.comp ((trivializationAt E (TangentSpace I) α).symmL ℝ b)) :=
  rfl

/-- **The raw chart-component formula for the section-level covariant
gradient.** For a smooth compactly-supported `(r, s)`-tensor section `S`, a
chart center `α`, a component multi-index `Idx : Fin r → Fin n`, a target
covariant multi-index `Jdx : Fin (s + 1) → Fin n`, and a Euclidean-chart-target
point `y`, the raw chart-frame scalar component of the section-level covariant
gradient `covGrad g r s S` at `(Idx, Jdx)`, read at the chart-source preimage
`b := (extChartAt I α).symm (toEuclidean.symm y)` of `y`, equals the
`(Jdx 0)`-th chart-Euclidean partial derivative of the Euclidean push-forward of
the raw `(r, s)`-component of `S` at `(Idx, Matrix.vecTail Jdx)`, plus the
zeroth-order Christoffel correction term
`covDerivLowerOrderTerm g r s S α (Jdx 0) Idx (Matrix.vecTail Jdx)`.

The section value of `covGrad g r s S` at `b` is, by `covGrad_toSection_apply`,
the image under the covariant-gradient bundle equivalence of the bundled
directional covariant derivative `Φ` of `S`. The trivialisation-compatibility
identity `covGradBundleEquiv_trivializationAt_eq`, together with the
leftmost-slot evaluation `covGradModelEquiv_apply`, projects the `(r, s + 1)`-
component onto the `(r, s)`-component of `Φ` taken along the `(Jdx 0)`-th
chart-frame basis vector. On the chart-`α` Levi-Civita good set that directional
covariant derivative agrees with the chart-coordinate covariant derivative
(`tensorCovDerivAt_eq_chartTensorRSCovariantDerivative`), whose raw chart-frame
component is `euclidPartial + covDerivLowerOrderTerm`
(`covDerivComponent_eq_euclidPartial_add_lowerOrder`). -/
theorem tensorChartComponentRaw_covGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Jdx 0)
          (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx
            (Matrix.vecTail Jdx))) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α (Jdx 0) Idx
            (Matrix.vecTail Jdx) y := by
  classical
  letI : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E)
      (fun z : M => Tensor0SSpace r I z)) := tensor0SBundle_topology r
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun z : M => Tensor0SSpace (s + 1) I z)) := tensor0SBundle_topology (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z)) :=
    tensorRSBundle_topology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) :=
    tensorRSBundle_fiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) :=
    tensorRSBundle_vector r (s + 1)
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have hb_baseS1 : b ∈ (trivializationAt (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) α).baseSet := by
    change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
        (fun z : M => Tensor0SSpace r I z) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) α).baseSet)
    exact ⟨hb_base, hb_base⟩
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    refine ⟨⟨?_, ?_⟩, hb_int⟩
    · rw [extChartAt_source]; exact hb_chart
    · rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
  set Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
      (fun z : M => S.toSection z) b with hΦ_def
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [covGrad_toSection_apply (I := I) (M := M) g r s S b]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun z : M => S.toSection z) b) = Φ from rfl]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
    (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun z : M => TensorRSSpace r (s + 1) I z) α).coe_linearMapAt_of_mem
      (R := ℝ) hb_baseS1]
  beta_reduce
  rw [covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s α hb_base Φ]
  rw [tensorChartComponentProjection_apply,
    covGradModelEquiv_apply (E := E) r s]
  rw [covGradBundle_trivFibre_eq' (I := I) (M := M) r s α b Φ]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hsymmL : (trivializationAt E (TangentSpace I) α).symmL ℝ b
      ((chartModelBasis E) (Jdx 0)) =
      chartBasisVecFiber (I := I) α (Jdx 0) b := rfl
  rw [hsymmL]
  rw [show Φ (chartBasisVecFiber (I := I) α (Jdx 0) b) =
      tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α (Jdx 0) b) from rfl]
  rw [tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
    g r s S α (Jdx 0) hb_good]
  exact covDerivComponent_eq_euclidPartial_add_lowerOrder (I := I) (M := M)
    g r s S α (Jdx 0) Idx (Matrix.vecTail Jdx) hy

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
