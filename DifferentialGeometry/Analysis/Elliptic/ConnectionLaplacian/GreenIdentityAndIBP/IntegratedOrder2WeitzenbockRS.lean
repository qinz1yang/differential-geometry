import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock

/-!
# The integrated order-`2` Weitzenböck identity at arbitrary contravariant rank `(r, s)`

This is the contravariant-rank-`r` lift of the integrated order-`2` Weitzenböck
(Bochner) identity `weitzenbock_integrated_covGrad_l2_normSq`
(`IntegratedOrder2Weitzenbock`). For a closed smooth Riemannian manifold `(M, g)`
modelled on a real inner-product space `E`, and every smooth compactly-supported
`(r, s)`-tensor field `S`, this file proves

```
‖∇²S‖²_{L²} = ‖Δ_∇ S‖²_{L²} − ⟨Curv, ∇S⟩_{L²},
```

where

* `∇S = covGrad g r s S` is the covariant gradient (an `(r, s + 1)`-tensor field);
* `∇²S = covGrad g r (s+1) (covGrad g r s S)` is the iterated covariant gradient
  (an `(r, s + 2)`-tensor field), whose diagonal `L²` self-pairing is `‖∇²S‖²`;
* `Δ_∇ S = rawTensorConnLapSmooth g r s S` is the rough (connection) Laplacian;
* `Curv = Δ_∇(∇S) − ∇(Δ_∇ S)` is the rough-Laplacian / covariant-gradient
  commutator defect, an `(r, s + 1)`-tensor field.

The derivation is the verbatim rank-`r` analogue of the rank-`0` chain: the
genuinely analytic input is the general-rank connection-Laplacian Green identity
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner`
(`TensorDirichletCurrentGreenIdentityRS`), i.e. integration by parts for the rough
Laplacian on the closed `(r, s)`-bundle, supplied with its metric-lowering
intertwiner witness `loweringIntertwinerRS_holds`. Everything above it — the two
diagonal Green specialisations and the cross-pairing split — is the rank-generic
linearity / symmetry of the global `L²` pairing.

## Main results

* `covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs` — the diagonal Green
  identity `⟨∇²S, ∇²S⟩_{L²} = − ⟨Δ_∇(∇S), ∇S⟩_{L²}` at rank `(r, s + 1)`.
* `covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs` — the
  Laplacian-gradient collapse `⟨∇(Δ_∇ S), ∇S⟩_{L²} = − ‖Δ_∇ S‖²_{L²}` at rank
  `(r, s)`.
* `rawTensorConnLap_l2Inner_covGrad_split_rs` — the cross-pairing split
  `⟨Δ_∇(∇S), ∇S⟩_{L²} = − ‖Δ_∇ S‖²_{L²} + ⟨Curv, ∇S⟩_{L²}`.
* `weitzenbock_integrated_covGrad_l2_normSq_rs` — **the integrated Weitzenböck
  identity** `‖∇²S‖²_{L²} = ‖Δ_∇ S‖²_{L²} − ⟨Curv, ∇S⟩_{L²}` at contravariant
  rank `r`, with `Curv` the commutator defect.

## Sign / order conventions

Geometer convention `Δ_∇ = -∇*∇` for the rough Laplacian
`rawTensorConnLapSmooth`. The covariant gradient `covGrad g r s` raises the
covariant tensor rank from `(r, s)` to `(r, s + 1)`.
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
/-- **Diagonal Green identity at rank `(r, s + 1)`.** For a smooth
compactly-supported `(r, s)`-tensor field `S`, writing `∇S := covGrad g r s S` for
its `(r, s + 1)` covariant gradient, the diagonal `L²` self-pairing of
`∇²S = ∇(∇S)` equals minus the `L²` pairing of the rough Laplacian `Δ_∇(∇S)` with
`∇S`:

```
⟨∇²S, ∇²S⟩_{L²} = − ⟨Δ_∇(∇S), ∇S⟩_{L²}.
```

This is the diagonal specialisation (at `v := T := ∇S`) of the rank-`(r, s + 1)`
connection-Laplacian Green identity
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner`,
supplied with the metric-lowering intertwiner witness `loweringIntertwinerRS_holds`.
The verbatim rank-`r` lift of `covGrad_l2Inner_self_eq_neg_rawConnLap_inner_gen`. -/
lemma covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1 + 1)
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun =
      - tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
            (covGrad (I := I) (M := M) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (I := I) (M := M) g r (s + 1)
    (loweringIntertwinerRS_holds (I := I) (M := M) g r (s + 1))
    (covGrad (I := I) (M := M) g r s S)
    (covGrad (I := I) (M := M) g r s S)

set_option linter.unusedSectionVars false in
/-- **Laplacian-gradient collapse at rank `(r, s)`.** For a smooth
compactly-supported `(r, s)`-tensor field `S`, the `L²` inner product of the
covariant gradient of `Δ_∇ S` with the covariant gradient of `S` equals minus the
squared `L²` norm of `Δ_∇ S`:

```
⟨∇(Δ_∇ S), ∇S⟩_{L²} = − ‖Δ_∇ S‖²_{L²}.
```

This is the rank-`(r, s)` Green identity applied at the pair `(S, Δ_∇ S)`, together
with the symmetry of the global `L²` pairing. The verbatim rank-`r` lift of
`covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_gen`. -/
lemma covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S)).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      - tensorL2Norm (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 := by
  set ΔS : SmoothCcTensor g r s := rawTensorConnLapSmooth (I := I) g r s S with hΔS_def
  rw [tensorL2Inner_symm (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s ΔS).toFun
    (covGrad (I := I) (M := M) g r s S).toFun]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (I := I) (M := M) g r s
    (loweringIntertwinerRS_holds (I := I) (M := M) g r s) S ΔS]
  rw [hΔS_def]
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s S)]

set_option linter.unusedSectionVars false in
/-- **Cross-pairing split at rank `(r, s)`.** Writing `Curv := Δ_∇(∇S) − ∇(Δ_∇ S)`
for the rough-Laplacian / covariant-gradient commutator defect (an
`(r, s + 1)`-tensor field), the `L²` pairing of `Δ_∇(∇S)` with `∇S` splits as minus
the squared `L²` norm of `Δ_∇ S` plus the curvature cross term:

```
⟨Δ_∇(∇S), ∇S⟩_{L²} = − ‖Δ_∇ S‖²_{L²} + ⟨Curv, ∇S⟩_{L²}.
```

The verbatim rank-`r` lift of `rawConnLap_l2Inner_covGrad_split_gen`. -/
lemma rawTensorConnLap_l2Inner_covGrad_split_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (rawTensorConnLapSmooth (I := I) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      - tensorL2Norm (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 +
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
              (covGrad (I := I) (M := M) g r s S) -
            covGrad (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := by
  classical
  set GS : SmoothCcTensor g r (s + 1) := covGrad (I := I) (M := M) g r s S with hGS_def
  set ΔGS : SmoothCcTensor g r (s + 1) :=
    rawTensorConnLapSmooth (I := I) g r (s + 1) GS with hΔGS_def
  set GΔ : SmoothCcTensor g r (s + 1) :=
    covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) with hGΔ_def
  have hcomm : ΔGS = GΔ + (ΔGS - GΔ) := by abel
  nth_rewrite 1 [hcomm]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g r (s + 1)
    GΔ.toFun (ΔGS - GΔ).toFun GS.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GΔ GS)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (ΔGS - GΔ) GS)]
  rw [hGΔ_def, hGS_def]
  rw [covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs (I := I) (M := M) g r s S]

set_option linter.unusedSectionVars false in
/-- **The integrated order-`2` Weitzenböck identity at arbitrary contravariant rank
`(r, s)`.** For a smooth compactly-supported `(r, s)`-tensor field `S` on a closed
(compact, boundaryless) Riemannian manifold, the squared `L²` norm of the iterated
covariant gradient `∇²S := covGrad g r (s+1) (covGrad g r s S)` equals the squared
`L²` norm of the rough Laplacian `Δ_∇ S := rawTensorConnLapSmooth g r s S` minus the
`L²` cross term against the commutator defect:

```
‖∇²S‖²_{L²} = ‖Δ_∇ S‖²_{L²} − ⟨Curv, ∇S⟩_{L²},
```

where `∇S := covGrad g r s S` and `Curv := Δ_∇(∇S) − ∇(Δ_∇ S)` is the
rough-Laplacian / covariant-gradient commutator defect (an `(r, s + 1)`-tensor
field).

The proof chains the diagonal Green identity at rank `(r, s + 1)`
(`covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs`) with the cross-pairing
split through the commutator (`rawTensorConnLap_l2Inner_covGrad_split_rs`), then
closes by ring arithmetic on the resulting linear `L²` pairings. This is the
verbatim contravariant-rank-`r` lift of `weitzenbock_integrated_covGrad_l2_normSq`,
the genuine analytic content being the rank-`r` rough-Laplacian Green identity
(integration by parts) supplied with its metric-lowering intertwiner witness. -/
theorem weitzenbock_integrated_covGrad_l2_normSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun ^ 2 =
      tensorL2Norm (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 -
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
              (covGrad (I := I) (M := M) g r s S) -
            covGrad (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := by
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g r (s + 1 + 1)
    (covGrad (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s S))]
  rw [covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs (I := I) (M := M) g r s S]
  rw [rawTensorConnLap_l2Inner_covGrad_split_rs (I := I) (M := M) g r s S]
  ring

end Connection
end Integral
end DifferentialGeometry

end
