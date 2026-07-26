import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Intrinsic
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm

/-!
# Parabolic smoothing of the intrinsic tensor heat semigroup into every `Hˢ`

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the
intrinsic tensor heat semigroup `tensorHeatSemigroup g r s t`
(built in `HeatSemigroup/Intrinsic.lean` from the chart-locality-free
resolvent eigenbasis) acts diagonally on that eigenbasis, multiplying the
`i`-th Fourier coefficient by `exp(-λᵢ t)` with `λᵢ ≥ 0` the
connection-Laplacian eigenvalue.

Because positive time provides spectral decay that beats every polynomial
weight `(1 + λᵢ)^σ`, the heat semigroup is a **parabolic smoothing**
operator: for `t > 0` the output `e^{tΔ} u₀` lies in the spectral Sobolev
space `Hˢ` for *every* exponent `σ ≥ 0`, even though the initial datum
`u₀` is only `L²`. The witness is the heat-rescaled coordinate family,
whose weighted-`ℓ²` summability at every exponent is the spectral lemma
`tensorHs.heatHs_weighted_summable` (file `SmoothingHs.lean`).

## Main results

* `tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact` — the intrinsic
  eigenbasis coordinate of `e^{tΔ} u₀` is `exp(-λᵢ t)` times the
  coordinate of `u₀`.
* `heat_semigroup_into_tensorHs` — for `0 < t`, `u₀ : L²`, and any
  `σ ≥ 0`, there is an element `v : tensorHs g r s σ` whose
  chart-locality-free `L²` realization `tensorHsToL2` is exactly
  `e^{tΔ} u₀`. Equivalently: `e^{tΔ} u₀ ∈ Hˢ`.
* `heat_semigroup_into_all_tensorHs` — the simultaneous-in-`σ` packaging:
  a single `u₀`-dependent family `σ ↦ vσ` of `Hˢ` witnesses, all
  realizing the *same* `L²` element `e^{tΔ} u₀`. This is the precise
  statement that `e^{tΔ} u₀` lies in the **spectral smooth subspace**
  `⋂_σ Hˢ` for `t > 0`.

## The reduction of the smooth-representative gate

The companion direction — that an element of the spectral smooth subspace
has a genuine `C^∞` (`SmoothCcTensor`) representative — is **not** proved
here; it is the deepest analytic gate of the construction. This file
records its precise reduction in `SpectralSmoothRealizesAsSmooth` and the
documentation lemma `spectral_smooth_realization_reduction`, which spell
out the two analytic ingredients (an *all-orders, unconditional, tensor*
elliptic-regularity bootstrap, and the unconditional `C^m` tensor Sobolev
embedding `iteratedCovGrad_toSobolev_embedding_Cm`) on which it depends.
See the section header below for the exact landscape of which bootstrap
lemmas already exist unconditionally and which remain.

## Sign convention

Geometer convention `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; the resolvent is
`(1 - Δ_∇)⁻¹`, eigenvalues `λᵢ ≥ 0`, heat factor `exp(-λᵢ t) ∈ (0, 1]`
for `t ≥ 0`, and weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Heat-output coordinate formula.** For `t ≥ 0`, the intrinsic
eigenbasis coordinate of `e^{tΔ} u₀` is `exp(-λᵢ t)` times the coordinate
of `u₀`. Here the coordinate functional `tensorL2Coeff` is taken
against the intrinsic compactness witness
`tensorResolventL2_isCompactOperator g r s`. -/
theorem tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (u₀ : TensorL2 r s g)
    (i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (tensorHeatSemigroup (I := I) (M := M) g r s t u₀) i =
      Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          u₀ i := by
  rw [tensorL2Coeff_eq_inner, tensorL2Coeff_eq_inner]
  exact tensorHeatSemigroup_intrinsic_inner_eigenbasis
    (I := I) (M := M) g r s ht u₀ i

/-- The `H⁰` element carrying the intrinsic eigenbasis coordinate family of
`u₀`: its `i`-th coordinate is `tensorL2Coeff … u₀ i`. -/
private def baseHZero (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) :
    tensorHs (I := I) (M := M) g r s 0 :=
  (tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)).symm u₀

private lemma baseHZero_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) (i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    (baseHZero (I := I) (M := M) g r s u₀).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        u₀ i :=
  tensorHsZeroEquivL2_symm_coeff (I := I) (M := M) _ u₀ i

/-- The `Hˢ` witness for the heat output: the heat-rescaling
`heatHsFun σ ht` applied to the `H⁰` base coordinate family of `u₀`.
Its `i`-th coordinate is `exp(-λᵢ t) · ⟪bᵢ, u₀⟫`, square-summable against
the weight `(1 + λᵢ)^σ` for every `σ` by `heatHs_weighted_summable`. -/
def heatHsWitness (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    tensorHs (I := I) (M := M) g r s σ :=
  tensorHs.heatHsFun (I := I) (M := M) σ ht
    (baseHZero (I := I) (M := M) g r s u₀)

/-- The `i`-th coordinate of the heat witness is `exp(-λᵢ t)` times the
intrinsic eigenbasis coordinate of `u₀`. -/
@[simp] theorem heatHsWitness_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    (heatHsWitness (I := I) (M := M) g r s σ ht u₀).coeff i =
      Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          u₀ i := by
  unfold heatHsWitness
  rw [tensorHs.heatHsFun_coeff, baseHZero_coeff]

/-- **Parabolic smoothing into `Hˢ`.** For `0 < t`, any initial datum
`u₀ : L²`, and any exponent `σ ≥ 0`, the heat output `e^{tΔ} u₀` is the
chart-locality-free `L²` realization of the `Hˢ` element
`heatHsWitness g r s σ ht u₀`:

  `tensorHsToL2 h_compact hσ (heatHsWitness … σ ht u₀)
      = tensorHeatSemigroup g r s t u₀`.

Thus `e^{tΔ} u₀` lies in the image of `Hˢ` in `L²` — it is `σ`-smooth —
for *every* `σ ≥ 0`. The proof matches the two `L²` tensors on their
intrinsic eigenbasis coordinates: the witness side equals
`exp(-λᵢ t) · ⟪bᵢ, u₀⟫` by `heatHsWitness_coeff` (after the inclusion's
coordinate-faithfulness `tensorHsToL2_tensorL2Coeff`),
and the heat-output side equals the same by
`tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact`. -/
theorem heat_semigroup_into_tensorHs (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        hσ (heatHsWitness (I := I) (M := M) g r s σ ht u₀) =
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀ := by
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  refine (tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact).repr.injective ?_
  ext i
  have hlhs :
      ((tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact).repr
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          h_compact hσ (heatHsWitness (I := I) (M := M) g r s σ ht u₀))) i =
        Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          tensorL2Coeff (I := I) (M := M) h_compact u₀ i := by
    have h := tensorHsToL2_tensorL2Coeff
      (I := I) (M := M) (h_compact := h_compact) hσ
      (heatHsWitness (I := I) (M := M) g r s σ ht u₀) i
    rw [heatHsWitness_coeff] at h
    simpa only [tensorL2Coeff] using h
  have hrhs :
      ((tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact).repr
        (tensorHeatSemigroup (I := I) (M := M) g r s t u₀)) i =
        Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          tensorL2Coeff (I := I) (M := M) h_compact u₀ i := by
    have h := tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact
      (I := I) (M := M) g r s ht.le u₀ i
    simpa only [tensorL2Coeff] using h
  rw [hlhs, hrhs]

/-- **Simultaneous parabolic smoothing into every `Hˢ`.** For `0 < t` and
`u₀ : L²`, there is a family `vσ : Hˢ` (one element per exponent `σ ≥ 0`)
all realizing the *same* `L²` element `e^{tΔ} u₀`. This is the precise
statement that `e^{tΔ} u₀` lies in the spectral smooth subspace
`⋂_σ Hˢ`: every Sobolev order is attained, witnessed coherently by the
single heat output. -/
theorem heat_semigroup_into_all_tensorHs (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) hσ v =
          tensorHeatSemigroup (I := I) (M := M) g r s t u₀ :=
  fun σ hσ =>
    ⟨heatHsWitness (I := I) (M := M) g r s σ ht u₀,
      heat_semigroup_into_tensorHs (I := I) (M := M) g r s hσ ht u₀⟩

/-- **The smooth-representative gate (predicate on the data).**

`SpectralSmoothRealizesAsSmooth g r s` holds when every `L²` tensor `u`
that lies (via the chart-locality-free inclusion) in `Hˢ` for *every*
exponent `σ ≥ 0` admits a genuine `C^∞` representative: a
`SmoothCcTensor g r s` whose `L²` class `(↑T : TensorL2 r s g)` equals
`u`.

The hypothesis "`u ∈ Hˢ for every σ`" is phrased as: for each `σ ≥ 0`
there is an `Hˢ` element whose `tensorHsToL2` realization is `u`
(the same shape produced by `heat_semigroup_into_all_tensorHs`). This is
the spectral smooth subspace `⋂_σ Hˢ`.

No term in this file assumes this predicate; it is the precise remaining
analytic content (an unconditional tensor all-orders elliptic-regularity
bootstrap composed with the unconditional `C^m` Sobolev embedding;
see the section header for the landscape). -/
def SpectralSmoothRealizesAsSmooth (g : SmoothRiemannianMetric I M)
    (r s : ℕ) : Prop :=
  ∀ u : TensorL2 r s g,
    (∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) hσ v = u) →
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u

/-- **Documented reduction of the smooth-representative gate to the heat
output.** Granting the gate predicate `SpectralSmoothRealizesAsSmooth`, the
heat output `e^{tΔ} u₀` (for `0 < t`) — which lies in every `Hˢ` by
`heat_semigroup_into_all_tensorHs` — has a genuine `C^∞`
(`SmoothCcTensor`) representative.

This is *not* an unconditional theorem: it consumes the gate as a
hypothesis. It is recorded to make the reduction explicit — the heat
smoothing supplies the all-orders membership `⋂_σ Hˢ` unconditionally
(`heat_semigroup_into_all_tensorHs`, proved above with axioms exactly
`{propext, Classical.choice, Quot.sound}`); the *only* remaining gap to a
`C^∞` representative is the gate, whose two analytic ingredients are
documented in the section header. -/
theorem spectral_smooth_realization_reduction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_gate : SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    ∃ T : SmoothCcTensor g r s,
      (T : TensorL2 r s g) =
        tensorHeatSemigroup (I := I) (M := M) g r s t u₀ :=
  h_gate _ (fun σ hσ =>
    ⟨heatHsWitness (I := I) (M := M) g r s σ ht u₀,
      heat_semigroup_into_tensorHs (I := I) (M := M) g r s hσ ht u₀⟩)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
