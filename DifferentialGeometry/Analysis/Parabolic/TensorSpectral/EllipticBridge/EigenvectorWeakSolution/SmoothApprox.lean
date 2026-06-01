import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenBasis
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.CanonicalTensorRepr
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.CompactSAResolventIntrinsic

/-!
# Smooth `H¹`-approximation of a connection-Laplacian eigenvector

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, fix a nonzero
resolvent eigenvalue `μ` and an eigenvector `φ := tensorResolventEigenbasisVec`
of the `L²`-side tensor resolvent `R = tensorResolventL2 g r s`. The eigenvector
`φ` is an abstract element of the `L²` Hilbert space `TensorL2 r s g`; the
elliptic-regularity argument that promotes it to a `C^∞` section needs `φ` to be
realised as the `L²`-coercion of an `H¹` element, approximated in `H¹` norm by
genuine smooth compactly-supported tensor sections.

This file assembles exactly that setup.

* `eigenvectorResolvent g r s i` is the `H¹`-completion element
  `tensorResolvent g r s φ`. Because `φ` lies in the resolvent eigenspace at the
  nonzero eigenvalue `μ`, the membership equation `R φ = μ • φ` rearranges to

  ```
  φ = μ⁻¹ • TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s i),
  ```

  i.e. `φ` itself is `μ⁻¹` times the `L²`-coercion of an `H¹` element.

* The canonical Euclidean chart components of `φ` are accordingly `μ⁻¹` times
  the chart components of that `L²`-coercion.

* The `H¹`-completion element `eigenvectorResolvent g r s i` is the
  limit, in `TensorH1Compl g r s`, of a sequence of (coercions of) smooth
  compactly-supported `H¹` tensor sections, by density of the completion
  embedding.

* `eigenvectorResolvent g r s i` solves the eigenvector weak
  equation: testing against any smooth compactly-supported `H¹` section `S`, its
  `H¹` pairing with `S` equals the `L²` pairing of the underlying smooth `L²`
  section with the eigenvector `φ`. This is the variational identity defining the
  resolvent.

* For a fixed smooth test section `S`, the Dirichlet (covariant-gradient)
  pairing of the approximating sequence against `S` converges. This is extracted
  from convergence of the full `H¹` pairing — continuity of the inner product —
  by subtracting the `L²` part, which converges by continuity of the `H¹`-to-`L²`
  inclusion.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The sigma-index type of the resolvent eigenbasis: a nonzero eigenvalue `μ`
paired with an index `k` into the standard orthonormal basis of the eigenspace
at `μ`. -/
abbrev TensorEigenIdx
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  Σ μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s,
    Fin (Module.finrank ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val))

/-- The `H¹` pairing of two completion-embedded smooth `H¹` sections equals the
pre-Hilbert `H¹` inner product of the underlying sections. -/
private lemma inner_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensorH1 g r s) :
    ⟪smoothToTensorH1Compl (I := I) (M := M) g r s S,
        smoothToTensorH1Compl (I := I) (M := M) g r s T⟫_ℝ =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor := by
  rw [smoothToTensorH1Compl_apply, smoothToTensorH1Compl_apply]
  rw [UniformSpace.Completion.inner_coe]
  exact SmoothCcTensorH1.inner_def S T

/-- The `H¹` pairing of two completion-embedded smooth `H¹` sections is the `L²`
pairing of the underlying smooth `L²` sections plus the integrated
covariant-gradient pairing. -/
private lemma inner_smoothToTensorH1Compl_eq_l2_add_dirichlet
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensorH1 g r s) :
    ⟪smoothToTensorH1Compl (I := I) (M := M) g r s S,
        smoothToTensorH1Compl (I := I) (M := M) g r s T⟫_ℝ =
      ⟪(S.toCcTensor : TensorL2 r s g),
          (T.toCcTensor : TensorL2 r s g)⟫_ℝ +
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            S.toCcTensor T.toCcTensor x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [inner_smoothToTensorH1Compl (I := I) (M := M) g r s S T,
    tensorH1Inner_def]
  have h_l2 :
      tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun T.toCcTensor.toFun =
        ⟪(S.toCcTensor : TensorL2 r s g),
          (T.toCcTensor : TensorL2 r s g)⟫_ℝ := by
    rw [UniformSpace.Completion.inner_coe]
    exact (SmoothCcTensor.inner_def S.toCcTensor T.toCcTensor).symm
  rw [h_l2]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The eigenvector resolvent (chart-locality-free).** The `H¹`-completion
element obtained by applying the resolvent `tensorResolvent g r s` to the
chart-locality-free eigenbasis vector `tensorResolventEigenbasisVec`
at the unconditional compactness witness. No chart-selection hypothesis. -/
noncomputable def eigenvectorResolvent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1Compl g r s :=
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  tensorResolvent (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The eigenvector is a rescaled `L²`-coercion of an `H¹` element
(chart-locality-free).** The eigenbasis vector `φ` equals `μ⁻¹` times the
`L²`-coercion of the `H¹`-completion element `eigenvectorResolvent g r s i`,
keyed on the unconditional compactness witness. -/
theorem eigenvector_eq_resolvent_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i =
      (i.fst.val)⁻¹ •
        TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hc_def
  have h_mem :
      tensorResolventEigenbasisVec (I := I) (M := M) hc i ∈
        tensorResolventEigenspace (I := I) (M := M) g r s i.fst.val :=
    tensorResolventEigenbasisVec_mem (I := I) (M := M) hc i
  have h_eig :
      tensorResolventL2 (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) hc i) =
        i.fst.val • tensorResolventEigenbasisVec (I := I) (M := M) hc i :=
    (mem_tensorResolventEigenspace_iff (I := I) (M := M) g r s i.fst.val
      (tensorResolventEigenbasisVec (I := I) (M := M) hc i)).mp h_mem
  have h_eig' :
      TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i) =
        i.fst.val • tensorResolventEigenbasisVec (I := I) (M := M) hc i := by
    rw [eigenvectorResolvent]
    rw [← tensorResolventL2_apply (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) hc i)]
    exact h_eig
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [h_eig', smul_smul, inv_mul_cancel₀ hμ_ne, one_smul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The chart components of the eigenvector are rescaled chart components of
the resolvent (chart-locality-free).** Each canonical Euclidean chart component
of the eigenbasis vector equals `μ⁻¹` times the corresponding chart component of
the `L²`-coercion of `eigenvectorResolvent g r s i`. -/
theorem eigenvector_chartComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
        α P₀ =
      (i.fst.val)⁻¹ •
        tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) α P₀ := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [eigenvector_eq_resolvent_smul (I := I) (M := M) g r s i]
  exact tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i)) α P₀

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Smooth `H¹`-approximating sequence of the eigenvector resolvent
(chart-locality-free).** There is a sequence of smooth compactly-supported `H¹`
tensor sections whose completion embeddings converge in `TensorH1Compl g r s` to
`eigenvectorResolvent g r s i`, by density of the completion embedding. -/
theorem exists_smoothApprox
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ∃ w : ℕ → SmoothCcTensorH1 g r s,
      Filter.Tendsto
        (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s (w n))
        atTop
        (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s i)) := by
  have h_dense :
      DenseRange
        ((↑) : SmoothCcTensorH1 g r s → TensorH1Compl g r s) :=
    UniformSpace.Completion.denseRange_coe
  have h_mem_closure :
      eigenvectorResolvent (I := I) (M := M) g r s i ∈
        closure (Set.range
          ((↑) : SmoothCcTensorH1 g r s → TensorH1Compl g r s)) :=
    h_dense (eigenvectorResolvent (I := I) (M := M) g r s i)
  rw [mem_closure_iff_seq_limit] at h_mem_closure
  obtain ⟨x, hx_range, hx_tendsto⟩ := h_mem_closure
  choose w hw using hx_range
  refine ⟨w, ?_⟩
  have h_eq : (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s (w n)) = x := by
    funext n
    rw [smoothToTensorH1Compl_apply]
    exact hw n
  rw [h_eq]
  exact hx_tendsto

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The eigenvector weak equation (chart-locality-free).** Testing
`eigenvectorResolvent g r s i` against a smooth compactly-supported `H¹` section
`S`, its `H¹` pairing with the embedded `S` equals the `L²` pairing of
`S.toCcTensor` with the eigenbasis vector. -/
theorem eigenWeakEquation
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S : SmoothCcTensorH1 g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    ⟪eigenvectorResolvent (I := I) (M := M) g r s i,
        (smoothToTensorH1Compl (I := I) (M := M) g r s S)⟫_ℝ =
      ⟪(S.toCcTensor : TensorL2 r s g),
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i⟫_ℝ := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_var := tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    (smoothToTensorH1Compl (I := I) (M := M) g r s S)
  rw [← eigenvectorResolvent] at h_var
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
    (I := I) (M := M) g r s S] at h_var
  exact h_var

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Convergence of the Dirichlet pairing of the approximating sequence
(chart-locality-free).** For a fixed smooth test section `S` and any `H¹`
-approximating sequence `w` of `eigenvectorResolvent g r s i`, the integrated
covariant-gradient (Dirichlet) pairing of `w n` against `S` converges to the
full `H¹` pairing minus the `L²` pairing. -/
theorem smoothApprox_dirichlet_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S : SmoothCcTensorH1 g r s)
    {w : ℕ → SmoothCcTensorH1 g r s}
    (hw : Filter.Tendsto
        (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s (w n))
        atTop
        (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s i))) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (w n).toCcTensor S.toCcTensor x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 (⟪eigenvectorResolvent (I := I) (M := M) g r s i,
              smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ -
            ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i),
              (S.toCcTensor : TensorL2 r s g)⟫_ℝ)) := by
  have h_dirichlet_eq :
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (w n).toCcTensor S.toCcTensor x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        fun n => ⟪smoothToTensorH1Compl (I := I) (M := M) g r s (w n),
              smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ -
            ⟪((w n).toCcTensor : TensorL2 r s g),
              (S.toCcTensor : TensorL2 r s g)⟫_ℝ := by
    funext n
    have h_decomp := inner_smoothToTensorH1Compl_eq_l2_add_dirichlet
      (I := I) (M := M) g r s (w n) S
    linarith [h_decomp]
  rw [h_dirichlet_eq]
  have h_h1 :
      Filter.Tendsto
        (fun n => ⟪smoothToTensorH1Compl (I := I) (M := M) g r s (w n),
            smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ)
        atTop
        (𝓝 (⟪eigenvectorResolvent (I := I) (M := M) g r s i,
            smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ)) := by
    have h_cont :
        Continuous (fun u : TensorH1Compl g r s =>
          ⟪u, smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ) :=
      (innerSL ℝ).continuous₂.comp
        (continuous_id.prodMk continuous_const)
    exact (h_cont.tendsto _).comp hw
  have h_l2 :
      Filter.Tendsto
        (fun n => ⟪((w n).toCcTensor : TensorL2 r s g),
            (S.toCcTensor : TensorL2 r s g)⟫_ℝ)
        atTop
        (𝓝 (⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i),
            (S.toCcTensor : TensorL2 r s g)⟫_ℝ)) := by
    have h_rewrite :
        (fun n => ⟪((w n).toCcTensor : TensorL2 r s g),
            (S.toCcTensor : TensorL2 r s g)⟫_ℝ) =
          fun n => ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (smoothToTensorH1Compl (I := I) (M := M) g r s (w n)),
              (S.toCcTensor : TensorL2 r s g)⟫_ℝ := by
      funext n
      rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
        (I := I) (M := M) g r s (w n)]
    rw [h_rewrite]
    have h_cont :
        Continuous (fun u : TensorH1Compl g r s =>
          ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s u,
            (S.toCcTensor : TensorL2 r s g)⟫_ℝ) := by
      have h_cont_inner :
          Continuous (fun v : TensorL2 r s g =>
            ⟪v, (S.toCcTensor : TensorL2 r s g)⟫_ℝ) :=
        (innerSL ℝ).continuous₂.comp
          (continuous_id.prodMk continuous_const)
      exact h_cont_inner.comp
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous
    exact (h_cont.tendsto _).comp hw
  exact h_h1.sub h_l2

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
