import DifferentialGeometry.Integral.Connection.TensorConnLapGreenIntertwinerGen
import DifferentialGeometry.Integral.Connection.TensorConnLapGradientL2Bound
import DifferentialGeometry.Integral.L2.SmoothSections.Integrability
import DifferentialGeometry.Integral.L2.Pairing.CauchySchwarz

/-!
# The integrated order-`2` Weitzenböck identity at arbitrary covariant rank

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, and every smooth compactly-supported `(0, s)`-tensor
field `S`, this file proves the **integrated order-`2` Weitzenböck (Bochner)
identity**

```
‖∇²S‖²_{L²} = ‖Δ_∇ S‖²_{L²} − ⟨Curv, ∇S⟩_{L²},
```

where

* `∇S = covGrad g 0 s S` is the covariant gradient (a `(0, s + 1)`-tensor field);
* `∇²S = covGrad g 0 (s+1) (covGrad g 0 s S)` is the iterated covariant gradient
  (a `(0, s + 2)`-tensor field), whose diagonal `L²` self-pairing is `‖∇²S‖²`;
* `Δ_∇ S = rawTensorConnLapSmooth g 0 s S` is the rough (connection) Laplacian;
* `Curv = Δ_∇(∇S) − ∇(Δ_∇ S)` is the rough-Laplacian / covariant-gradient
  commutator defect, a `(0, s + 1)`-tensor field. Per the Ricci identity the
  fibre value of `Curv` is a curvature contraction, controlled pointwise by
  `‖R‖_∞ · (rfns(S) + rfns(∇S))`.

The identity is the integrated (integration-by-parts) form of the order-`2`
elliptic Gårding estimate. Its derivation is purely the two diagonal Green
identities (one at rank `s + 1`, one at rank `s`) of the rough Laplacian, plus
the linearity of the global `L²` pairing — the curvature content is packaged into
the single defect field `Curv`, never differentiating the curvature.

## Main results

* `covGrad_l2Inner_self_eq_neg_rawConnLap_inner_gen` — the diagonal Green identity
  `⟨∇²S, ∇²S⟩_{L²} = − ⟨Δ_∇(∇S), ∇S⟩_{L²}` at rank `s + 1`.
* `covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_gen` — the Laplacian-gradient
  collapse `⟨∇(Δ_∇ S), ∇S⟩_{L²} = − ‖Δ_∇ S‖²_{L²}` at rank `s`.
* `rawConnLap_l2Inner_covGrad_split_gen` — the cross-pairing split
  `⟨Δ_∇(∇S), ∇S⟩_{L²} = − ‖Δ_∇ S‖²_{L²} + ⟨Curv, ∇S⟩_{L²}`.
* `weitzenbock_integrated_covGrad_l2_normSq` — **the integrated Weitzenböck identity**
  `‖∇²S‖²_{L²} = ‖Δ_∇ S‖²_{L²} − ⟨Curv, ∇S⟩_{L²}`, with `Curv` the commutator
  defect.

## Sign / order conventions

Geometer convention `Δ_∇ = -∇*∇` for the rough Laplacian
`rawTensorConnLapSmooth`. The covariant gradient `covGrad g 0 s` raises the
tensor rank from `(0, s)` to `(0, s + 1)`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- **Diagonal Green identity at rank `s + 1`.** For a smooth compactly-supported
`(0, s)`-tensor field `S`, writing `∇S := covGrad g 0 s S` for its `(0, s + 1)`
covariant gradient, the diagonal `L²` self-pairing of `∇²S = ∇(∇S)` equals minus
the `L²` pairing of the rough Laplacian `Δ_∇(∇S)` with `∇S`:

```
⟨∇²S, ∇²S⟩_{L²} = − ⟨Δ_∇(∇S), ∇S⟩_{L²}.
```

This is the diagonal specialisation (at `v := T := ∇S`) of the rank-`(0, s + 1)`
connection-Laplacian Green identity. -/
lemma covGrad_l2Inner_self_eq_neg_rawConnLap_inner_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1 + 1)
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen (I := I) (M := M) g (s + 1)
    (covGrad (I := I) (M := M) g 0 s S)
    (covGrad (I := I) (M := M) g 0 s S)

set_option linter.unusedSectionVars false in
/-- **Laplacian-gradient collapse at rank `s`.** For a smooth compactly-supported
`(0, s)`-tensor field `S`, the `L²` inner product of the covariant gradient of
`Δ_∇ S` with the covariant gradient of `S` equals minus the squared `L²` norm of
`Δ_∇ S`:

```
⟨∇(Δ_∇ S), ∇S⟩_{L²} = − ‖Δ_∇ S‖²_{L²}.
```

This is the rank-`(0, s)` Green identity applied at the pair `(S, Δ_∇ S)`,
together with the symmetry of the global `L²` pairing. -/
lemma covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 := by
  set ΔS : SmoothCcTensor g 0 s := rawTensorConnLapSmooth (I := I) g 0 s S with hΔS_def
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 (s + 1)
    (covGrad (I := I) (M := M) g 0 s ΔS).toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen (I := I) (M := M) g s S ΔS]
  rw [hΔS_def]
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 s
    (rawTensorConnLapSmooth (I := I) g 0 s S)]

set_option linter.unusedSectionVars false in
/-- **Cross-pairing split.** Writing `Curv := Δ_∇(∇S) − ∇(Δ_∇ S)` for the
rough-Laplacian / covariant-gradient commutator defect (a `(0, s + 1)`-tensor
field), the `L²` pairing of `Δ_∇(∇S)` with `∇S` splits as minus the squared `L²`
norm of `Δ_∇ S` plus the curvature cross term:

```
⟨Δ_∇(∇S), ∇S⟩_{L²} = − ‖Δ_∇ S‖²_{L²} + ⟨Curv, ∇S⟩_{L²}.
```
-/
lemma rawConnLap_l2Inner_covGrad_split_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set GS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hGS_def
  set ΔGS : SmoothCcTensor g 0 (s + 1) :=
    rawTensorConnLapSmooth (I := I) g 0 (s + 1) GS with hΔGS_def
  set GΔ : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) with hGΔ_def
  have hcomm : ΔGS = GΔ + (ΔGS - GΔ) := by abel
  nth_rewrite 1 [hcomm]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    GΔ.toFun (ΔGS - GΔ).toFun GS.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GΔ GS)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (ΔGS - GΔ) GS)]
  rw [hGΔ_def, hGS_def]
  rw [covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_gen (I := I) (M := M) g s S]

set_option linter.unusedSectionVars false in
/-- **The integrated order-`2` Weitzenböck identity at arbitrary covariant rank.**
For a smooth compactly-supported `(0, s)`-tensor field `S` on a closed (compact,
boundaryless) Riemannian manifold, the squared `L²` norm of the iterated covariant
gradient `∇²S := covGrad g 0 (s+1) (covGrad g 0 s S)` equals the squared `L²` norm
of the rough Laplacian `Δ_∇ S := rawTensorConnLapSmooth g 0 s S` minus the `L²`
cross term against the commutator defect:

```
‖∇²S‖²_{L²} = ‖Δ_∇ S‖²_{L²} − ⟨Curv, ∇S⟩_{L²},
```

where `∇S := covGrad g 0 s S` and `Curv := Δ_∇(∇S) − ∇(Δ_∇ S)` is the
rough-Laplacian / covariant-gradient commutator defect (a `(0, s + 1)`-tensor field).

The proof chains the diagonal Green identity at rank `s + 1`
(`covGrad_l2Inner_self_eq_neg_rawConnLap_inner_gen`) with the cross-pairing split
through the commutator (`rawConnLap_l2Inner_covGrad_split_gen`), then closes by
ring arithmetic on the resulting linear `L²` pairings. -/
theorem weitzenbock_integrated_covGrad_l2_normSq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (s + 1 + 1)
    (covGrad (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S))]
  rw [covGrad_l2Inner_self_eq_neg_rawConnLap_inner_gen (I := I) (M := M) g s S]
  rw [rawConnLap_l2Inner_covGrad_split_gen (I := I) (M := M) g s S]
  ring

end Connection
end Integral
end DifferentialGeometry

end
