import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Defs
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Inclusion
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CompactResolvent
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckPrincipalPartMatch

/-!
# Design of the Ricci–DeTurck nonlinearity on the spectral Sobolev scale

The quasilinear strong-existence engine
`quasilinear_strong_existence`
(`Analysis/Parabolic/QuasiLinear/MaxRegFixedPoint.lean`) consumes a
nonlinearity

  `N : tensorHs g r s (a + 2) → tensorHs g r s a`

with `LipschitzWith L N` and `2 L < 1`, and produces a strong solution of
`∂_t u = Δ_∇ u + N(u)`.  The spectral operator `Δ_∇` whose eigenvalues
`λᵢ ≥ 0` scale the `tensorHs` tower is, by the principal-part match recorded
in `DeTurckPrincipalPartMatch.lean`, exactly the second-order part of the
Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg ·`.  The remainder

  `N(u) := deTurckRicciRHS g_bg (g_bg + h) − Δ_∇ h`,   `h = realize u`,

is therefore genuinely first order in `h`.

This file does **not** assert the engine's `LipschitzWith` hypothesis.  It
records the *design* of `N`, builds the chart-locality-free pieces that
genuinely exist, and states the single analytic gate that the remainder of
the construction depends on.

## The type-level obstruction (the gate)

`tensorHs g r s σ` is, by `SobolevScale/Defs.lean`, a structure carrying an
abstract spectral coordinate family
`coeff : TensorEigenIdx g r s → ℝ` together with a weighted-`ℓ²` summability
witness — *not* a pointwise tensor field, and certainly not a
`SmoothRiemannianMetric`.  Meanwhile `deTurckRicciRHS g_bg g`
(`DeTurckRHS.lean`) consumes a `SmoothRiemannianMetric I M` and evaluates it
pointwise through `ricciTensor`, `deTurckVF`, and `lieDerivMetricClm`.  To
even *write* `N(u)` one must realize a `tensorHs (a+2)` element as a tensor
field.

The realization splits into two maps of very different difficulty:

* **`H^{a+2} → TensorL2`** — *available, chart-locality-free*: the
  inclusion `tensorHsToL2` (re-exported below as `realizeToL2`)
  reconstructs the `L²` tensor with the prescribed eigenbasis coordinates
  via the inverse Hilbert-basis representation against
  `tensorResolventHilbertEigenbasisSigma`.  It is linear,
  continuous, norm-non-increasing, and needs no chart-locality witness.

* **`TensorL2 → SmoothRiemannianMetric`** — *the gate, NOT available*:
  `TensorL2 r s g = UniformSpace.Completion (SmoothCcTensor g r s)`
  (`Integral/L2/Hilbert/Defs.lean`), an abstract metric completion.  A
  generic element is an equivalence class of Cauchy sequences with no
  pointwise values.  Promoting it to a `SmoothRiemannianMetric` requires
  (i) a continuous-representative Sobolev embedding `H^{a+2} ↪ C²`
  (the key tensor lemma `tensorPouSobolevHilbert_embedding_Ck` in
  `SobolevEmbedding.lean` is itself still unproved), valid only when
  `2(a+2) > dim M + 4`, and (ii) a positive-definiteness argument making
  `g_bg + h` an honest metric for `h` small in `C⁰`.  The only existing
  `tensorHs → SmoothCcTensor` realization, `tensorHsSmoothRepr`
  (`EllipticBridge/.../EigenvectorTensorHsToWtwokTwo.lean`), is defined
  **only on finitely-supported** coordinate families and uses `h_atlas`
  (HLCC); it does not extend to general `H^{a+2}` elements without exactly
  the embedding above.

## What is delivered here (all chart-locality-free)

* `realizeToL2` — the `H^{a+2} →L[ℝ] TensorL2` realization CLM, with norm
  `≤ 1` and explicit eigenbasis coordinates.
* `firstOrderRemainderInclusion` — the order bookkeeping CLM
  `H^{a+1} →L[ℝ] H^a` witnessing "the first-order remainder loses one
  derivative and lands in `H^a`", with norm `≤ 1`.  This is the abstract
  shape that the geometric remainder must factor through; see
  `firstOrderRemainder_lands_in_Ha`.
* `deTurckNonlinearitySpectral_principalPart_cancels` — re-export of the
  symbol-level cancellation `deTurckRicciRHS_minus_roughLaplacian_…` from
  `DeTurckPrincipalPartMatch.lean`, the mathematical justification that the
  remainder is first order.

## Sign convention

Geometer convention `Δ_∇ = −∇*∇`, spectrum `⊆ (−∞, 0]`; the resolvent is
`(1 − Δ_∇)⁻¹`, weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The realization-to-`L²` continuous linear map of a metric perturbation
in the order-`(a+2)` spectral Sobolev space of `(0,2)`-tensors.

For a closed Riemannian manifold `(M, g_bg)` with the resolvent-compactness
witness `h_compact`, this sends `u ∈ H^{a+2}` to the `L²` `(0,2)`-tensor
field with the same eigenbasis coordinates.  It is linear, continuous, and
norm-non-increasing (operator norm `≤ 1`).  This is the only part of the
spectral-coordinate ↔ tensor-field realization that exists unconditionally;
the further promotion to a pointwise smooth metric is the remaining analytic
gate documented in the module header. -/
def realizeToL2 (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g_bg 0 2)) :
    tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2) →L[ℝ]
      TensorL2 0 2 g_bg :=
  tensorHsToL2 (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
    h_compact (by have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith)

/-- `realizeToL2` is norm-non-increasing: its operator norm is `≤ 1`. -/
theorem realizeToL2_opNorm_le_one (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g_bg 0 2)) :
    ‖realizeToL2 (I := I) (M := M) g_bg a h_compact‖ ≤ 1 :=
  tensorHsToL2_opNorm_le_one (I := I) (M := M)
    (g := g_bg) (r := 0) (s := 2)
    (by have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith)

/-- The `L²` eigenbasis coordinate of `realizeToL2 u` equals the spectral
coordinate of `u`: the realization is faithful on coordinates. -/
@[simp] theorem realizeToL2_tensorL2Coeff_ofCompact
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g_bg 0 2))
    (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (i : TensorEigenIdx (I := I) (M := M) g_bg 0 2) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (realizeToL2 (I := I) (M := M) g_bg a h_compact u) i = u.coeff i :=
  tensorHsToL2_tensorL2Coeff (I := I) (M := M)
    (by have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith) u i

/-- The realization-to-`L²` map sends `0` to `0` (it is linear). -/
@[simp] theorem realizeToL2_zero (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g_bg 0 2)) :
    realizeToL2 (I := I) (M := M) g_bg a h_compact 0 = 0 :=
  map_zero _

/-- The continuous linear inclusion `H^{a+1} →L[ℝ] H^a` of `(0,2)`-tensor
fields.  This is the order-bookkeeping step: a first-order operator out of
`H^{a+2}` produces an element of `H^{a+1}`, and this inclusion places it in
the engine's target space `H^a`.  Operator norm `≤ 1`. -/
def firstOrderRemainderInclusion (g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
  tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
    (by linarith : (a : ℝ) ≤ (a : ℝ) + 1)

/-- The order-bookkeeping inclusion is norm-non-increasing. -/
theorem firstOrderRemainderInclusion_opNorm_le_one
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    ‖firstOrderRemainderInclusion (I := I) (M := M) g_bg a‖ ≤ 1 :=
  tensorHsInclusion_opNorm_le_one (I := I) (M := M)
    (g := g_bg) (r := 0) (s := 2) (by linarith)

/-- The order-bookkeeping inclusion preserves the eigenbasis coordinate
family: it is the identity on coordinates, only the ambient weight changes. -/
@[simp] theorem firstOrderRemainderInclusion_coeff
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (v : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (i : TensorEigenIdx (I := I) (M := M) g_bg 0 2) :
    (firstOrderRemainderInclusion (I := I) (M := M) g_bg a v).coeff i =
      v.coeff i :=
  tensorHsInclusion_coeff_apply (I := I) (M := M) (by linarith) v i

/-- **Order-bookkeeping check: a first-order remainder lands in `H^a`.**

If the geometric remainder is realized as a continuous linear map
`R : H^{a+2} →L[ℝ] H^{a+1}` (the first-order drop of exactly one derivative),
then composing with `firstOrderRemainderInclusion` produces a continuous
linear map `H^{a+2} →L[ℝ] H^a` into the engine's codomain, with operator
norm bounded by `‖R‖`.  This confirms the codomain bookkeeping demanded by
`quasilinear_strong_existence` (which needs `N : H^{a+2} → H^a`):
the loss of one derivative places the output in `H^{a+1} ⊆ H^a`. -/
theorem firstOrderRemainder_lands_in_Ha
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (R : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1)) :
    ∃ R' : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2) →L[ℝ]
        tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ),
      (∀ u, (R' u).coeff = (R u).coeff) ∧ ‖R'‖ ≤ ‖R‖ := by
  refine ⟨(firstOrderRemainderInclusion (I := I) (M := M) g_bg a).comp R,
    ?_, ?_⟩
  · intro u
    funext i
    simp [firstOrderRemainderInclusion_coeff]
  · calc ‖(firstOrderRemainderInclusion (I := I) (M := M) g_bg a).comp R‖
        ≤ ‖firstOrderRemainderInclusion (I := I) (M := M) g_bg a‖ * ‖R‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖R‖ :=
          mul_le_mul_of_nonneg_right
            (firstOrderRemainderInclusion_opNorm_le_one (I := I) (M := M) g_bg a)
            (norm_nonneg _)
      _ = ‖R‖ := one_mul _

/-- **The remainder is principal-symbol-free (re-export).**

On a symmetric `(0,2)` perturbation `t`, the Ricci–DeTurck principal symbol
coincides with the (negated, gauge-cancelled) rough-Laplacian symbol: the two
candidate second-order parts differ by zero.  This is the mathematical
justification that `N(g) = deTurckRicciRHS g_bg g − Δ_∇ g` has no
second-order content, hence is genuinely first order — the property that
makes the codomain bookkeeping of `firstOrderRemainder_lands_in_Ha`
applicable. -/
theorem deTurckNonlinearitySpectral_principalPart_cancels
    (g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t
      = - DifferentialGeometry.PDE.DeTurck.deTurckSymbol (I := I) g₀ g_bg x ξ t :=
  deturck_ricci_principal_symbol_matches_rough_laplacian_of_symm
    (I := I) g₀ g_bg x ξ t ht

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
