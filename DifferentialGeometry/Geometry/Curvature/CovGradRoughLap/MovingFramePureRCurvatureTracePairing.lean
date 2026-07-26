import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs

/-!
# The pure-Riemann genuine curvature-trace `L²` pairing as a curvature bilinear of `∇S`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file rewrites the global
metric `L²` pairing of the concrete moving-centre pure-Riemann genuine curvature section
`GcurvSection g s S` (`MovingFrameCurvatureTraceSmooth`, the slot-`0` assembly of the tensorial
moving-frame trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, the `R(∇S)` contraction) against the covariant gradient
`∇S = covGrad g 0 s S` as a *clean curvature bilinear of `∇S` with itself*.

## Why this is the right object

The pure-Riemann section is **frame-free and tensorial**: it is the action of the *order-`0`* moving-frame
pure-Riemann curvature operator on the gradient field,
`GcurvSection g s S = pureRGenuineDiffOp g 0 (s + 1) (∇S)` (`pureRGenuineDiffOp0_eq_GcurvSection`,
`FrozenFramePureRCurvatureTower`), equivalently the operator-field action
`appCc (Φ₀ (s + 1)) (∇S)` of the frame-free curvature operator field `Φ₀ (s + 1)`
(`exists_pureRGenuineDiffOp_base_appCc`). It is therefore *not* subject to the `smoothExtensionTangent`
term-by-term obstruction that blocks the moving-frame bracket / discrepancy / residual fields: its `L²`
pairing against `∇S` is genuinely the curvature bilinear `⟨R(∇S), ∇S⟩_{L²}` — the curvature term of the
rank-generic Bochner–Weitzenböck formula on the gradient field — and so is accessible to the integrated
Ricci-identity machinery (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) without any frame freeze.

## Main results

* `tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp` — the **pairing bridge**:
  `⟨GcurvSection g s S, ∇S⟩_{L²} = ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}`, the global metric
  `L²` pairing of the pure-Riemann genuine section against `∇S` rewritten as the order-`0` pure-Riemann
  curvature operator applied to `∇S`, paired against `∇S`. Pure `congrArg` over
  `pureRGenuineDiffOp0_eq_GcurvSection`.

* `exists_GcurvSection_eq_appCc_curvatureOpField` — the **operator-field form**: there is a frame-free
  smooth curvature operator field `Φ₀` (the same one supplied by `exists_pureRGenuineDiffOp_base_appCc`)
  with `GcurvSection g s S = appCc (Φ₀ (s + 1)) (∇S)` at every rank, so the pure-Riemann section is the
  operator-field action of the order-`0` curvature operator on the gradient field. This matches the
  operator-field calculus the differentiated-curvature integration-by-parts identity
  `tensorL2Inner_appCc_covGrad_covGrad_eq_neg` (`OperatorFieldPairingIBP`) is phrased in, so the
  curvature term `⟨GcurvSection, ∇S⟩_{L²}` and the differentiated-curvature term `⟨Gcd, ∇S⟩_{L²}` are
  expressed through the *same* fixed curvature operator field `Φ₀`.

## The gap this localises (the differentiated-curvature genuine leaf)

The genuine differentiated-curvature leaf `genuineDiffCurv_crossPairing_remainder_nullity`
(`MovingFrameDiffCurvTraceSection`) reduces — through the sorry-free producer
`movingFrameNullity_of_genuineCrossPairingValue` (`MovingFrameIntegratedNullity`) — to the cross-pairing
value `hval : ⟨GcurvSection g s S + Gcd, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`. Splitting `hval` by
left additivity and substituting the sorry-free differentiated-curvature integration-by-parts formula
`tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg` for `⟨Gcd, ∇S⟩_{L²}` leaves exactly one
unevaluated curvature term, `⟨GcurvSection g s S, ∇S⟩_{L²}`. This file rewrites that term as the clean
curvature bilinear `⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}` — the precise object whose value
(the rank-generic Bochner curvature term) closes the leaf — so the remaining work is localised to a
single standard curvature integral over the *already-smooth* global section `pureRGenuineDiffOp`, rather
than to the moving-frame bracket family's missing smooth-section reconstructions.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s` raises
the tensor rank from `(0, s)` to `(0, s + 1)`. All `L²` pairings are the global metric `L²` pairing
`tensorL2Inner` against the canonical Riemannian volume measure.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The pure-Riemann genuine curvature-trace `L²` pairing is the order-`0` curvature operator paired
against `∇S`.** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every
smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the concrete
pure-Riemann genuine curvature section `GcurvSection g s S` (the slot-`0` assembly of the tensorial
moving-frame trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`) against `∇S := covGrad g 0 s S` equals the `L²` pairing of
the order-`0` moving-frame pure-Riemann curvature operator applied to `∇S` against `∇S`:

```
⟨GcurvSection g s S, ∇S⟩_{L²} = ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}.
```

**Proof.** The concrete pure-Riemann section is the order-`0` pure-Riemann curvature operator on the
gradient field, `pureRGenuineDiffOp g 0 (s + 1) (∇S) = GcurvSection g s S`
(`pureRGenuineDiffOp0_eq_GcurvSection`, `FrozenFramePureRCurvatureTower`, the bilinear-Parseval
frame-independence of the genuine metric trace read fibrewise); rewriting the left argument by this
section equality (`congrArg` through `tensorL2Inner (·).toFun (∇S).toFun`) gives the identity. The
right-hand pairing is a *clean curvature bilinear of `∇S` with itself* over the already-smooth global
section `pureRGenuineDiffOp g 0 (s + 1) (∇S)` — frame-free, free of the `smoothExtensionTangent`
obstruction. -/
theorem tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  rw [pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S]

/-- **The pure-Riemann genuine curvature section is the operator-field action of a frame-free curvature
operator on `∇S`.** For a closed smooth Riemannian manifold `(M, g)` there is a frame-free smooth
curvature operator field `Φ₀ : ∀ r, SmoothCcTensor g (r + 0) (r + 0)` (the same family supplied by
`exists_pureRGenuineDiffOp_base_appCc`, whose fibre value is the genuine `g`-metric curvature trace
`W ↦ ∑ᵢ R(Bᵢ, ·) W`) such that, at every covariant rank `s` and for every smooth compactly-supported
`(0, s)`-tensor `S`, the concrete pure-Riemann genuine curvature section equals the operator-field
action of the rank-`(s + 1)` curvature operator on the gradient field:

```
GcurvSection g s S = appCc (Φ₀ (s + 1)) (∇S),   ∇S := covGrad g 0 s S.
```

**Proof.** From the operator-field base identity `exists_pureRGenuineDiffOp_base_appCc`,
`pureRGenuineDiffOp g 0 (s + 1) (∇S) = appCc (Φ₀ (s + 1)) (∇S)`; the left side is `GcurvSection g s S`
by `pureRGenuineDiffOp0_eq_GcurvSection`. This expresses the pure-Riemann section in the *same*
operator-field calculus the differentiated-curvature integration-by-parts identity
`tensorL2Inner_appCc_covGrad_covGrad_eq_neg` (`OperatorFieldPairingIBP`) uses, so the curvature term
`⟨GcurvSection, ∇S⟩_{L²}` and the differentiated-curvature term are expressed through one fixed
curvature operator field `Φ₀`. -/
theorem exists_GcurvSection_eq_appCc_curvatureOpField
    (g : SmoothRiemannianMetric I M) :
    ∃ Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0),
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        GcurvSection (I := I) (M := M) g s S =
          appCc (I := I) (M := M) g ((s + 1) + 0) ((s + 1) + 0) (Φ₀ (s + 1))
            (covGrad (I := I) (M := M) g 0 s S) := by
  obtain ⟨Φ₀, hΦ₀⟩ := exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g
  refine ⟨Φ₀, fun s S => ?_⟩
  rw [← pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S]
  exact hΦ₀ (s + 1) (covGrad (I := I) (M := M) g 0 s S)

end Connection
end Integral
end DifferentialGeometry

end
