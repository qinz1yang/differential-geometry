import DifferentialGeometry.Integral.Connection.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Integral.Connection.TensorConnLapGradientL2Bound

/-!
# The integrated order-`1` control and the integrated order-`2` Gårding reduction

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, this file develops, at **arbitrary covariant rank** `s`, the
integration-by-parts (Green-identity) form of the interior elliptic estimates for
the rough (connection) Laplacian.

## Order-`1` control at arbitrary rank

The headline `covGrad_l2NormSq_le_rawConnLap_mul_self_gen` is the order-`1`
covariant-gradient `L²` control

```
‖∇S‖²_{L²} ≤ ‖Δ_∇ S‖_{L²} · ‖S‖_{L²}     (every rank `s`, every `(0, s)`-tensor `S`),
```

proved exactly as at rank `(0, 2)` — the diagonal rank-`(0, s)` Green identity
`⟨∇S, ∇S⟩_{L²} = − ⟨Δ_∇ S, S⟩_{L²}` (the unconditional general-rank connection-
Laplacian Green identity `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`),
combined with the global `L²` Cauchy–Schwarz inequality. This is the rank-generic
lift of `covGrad_l2NormSq_le_rawConnLap_mul_self`.

## Order-`2` Gårding from the curvature cross term

The integrated order-`2` Weitzenböck identity `weitzenbock_integrated_covGrad_l2_normSq`
gives, at every rank,

```
‖∇²S‖²_{L²} = ‖Δ_∇ S‖²_{L²} − ⟨Curv, ∇S⟩_{L²},
```

with `Curv = Δ_∇(∇S) − ∇(Δ_∇ S)` the rough-Laplacian / covariant-gradient
commutator defect. The reduction `secondCovGrad_l2NormSq_le_of_cross_bound`
converts a one-sided `L²` bound on the curvature cross term

```
− ⟨Curv, ∇S⟩_{L²} ≤ Ccross · (‖∇S‖²_{L²} + ‖S‖_{L²} · ‖∇S‖_{L²})
```

into the order-`2` Gårding estimate

```
‖∇²S‖²_{L²} ≤ Cg · (‖Δ_∇ S‖²_{L²} + ‖S‖²_{L²}),     Cg = 2 + 2 · Ccross,
```

uniformly in `s`, by feeding the order-`1` control `‖∇S‖² ≤ ‖Δ_∇ S‖ · ‖S‖` into the
cross-term bound and absorbing the `‖Δ_∇ S‖ · ‖S‖` and `‖S‖²` contributions with
Young's inequality. The cross-term bound is the integrated curvature content — the
fibrewise `R`-contraction of the Ricci identity on the gradient field, controlled by
the uniform sup `‖R‖_∞` over the compact manifold (the rank-generic curvature
fibre-norm bound `riemannOp_covGrad_fiberNormSq_le_gen`). The reduction is the
analytic spine of the integrated route: it never reads the gradient slot pointwise
and never differentiates the curvature.

## Sign / order conventions

Geometer convention `Δ_∇ = -∇*∇` for the rough Laplacian
`rawTensorConnLapSmooth`. The covariant gradient `covGrad g 0 s` raises the tensor
rank from `(0, s)` to `(0, s + 1)`.
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
/-- **Diagonal Green identity at rank `s`.** For a smooth compactly-supported
`(0, s)`-tensor field `S`, the diagonal `L²` self-pairing of the covariant gradient
equals minus the `L²` pairing of the rough Laplacian with `S`:

```
⟨∇S, ∇S⟩_{L²} = − ⟨Δ_∇ S, S⟩_{L²}.
```

This is the diagonal specialisation (at `v := S`) of the unconditional general-rank
connection-Laplacian Green identity. -/
lemma tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun S.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen (I := I) (M := M) g s S S

set_option linter.unusedSectionVars false in
/-- **First-order covariant-gradient `L²` control at arbitrary rank.** For a smooth
compactly-supported `(0, s)`-tensor field `S` on a closed Riemannian manifold, the
squared `L²` norm of the covariant gradient is bounded by the product of the `L²`
norms of the rough Laplacian and of `S`:

```
‖∇S‖²_{L²} ≤ ‖Δ_∇ S‖_{L²} · ‖S‖_{L²}.
```

This is the rank-generic order-`1` interior elliptic estimate. The proof is the
diagonal rank-`(0, s)` Green identity combined with the global `L²` Cauchy–Schwarz
inequality, mirroring the rank-`(0, 2)` `covGrad_l2NormSq_le_rawConnLap_mul_self`. -/
theorem covGrad_l2NormSq_le_rawConnLap_mul_self_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Norm (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun *
        tensorL2Norm (I := I) (M := M) g 0 s S.toFun := by
  set ΔS : SmoothCcTensor g 0 s := rawTensorConnLapSmooth (I := I) g 0 s S with hΔS_def
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 s ΔS.toFun S.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S)]
    rw [hΔS_def]
    exact tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen (I := I) (M := M) g s S
  rw [hgreen]
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 s ΔS.toFun S.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) ΔS)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) ΔS S)
  have hneg_le :
      - tensorL2Inner (I := I) (M := M) g 0 s ΔS.toFun S.toFun ≤
        |tensorL2Inner (I := I) (M := M) g 0 s ΔS.toFun S.toFun| :=
    neg_le_abs _
  exact le_trans hneg_le hcs

set_option linter.unusedSectionVars false in
/-- **Order-`2` Gårding from the integrated curvature cross-term bound.** For a smooth
compactly-supported `(0, s)`-tensor field `S` on a closed Riemannian manifold, writing
`∇S := covGrad g 0 s S`, `Δ_∇ S := rawTensorConnLapSmooth g 0 s S`, and
`Curv := Δ_∇(∇S) − ∇(Δ_∇ S)` for the rough-Laplacian / covariant-gradient commutator
defect, suppose the one-sided `L²` curvature cross-term bound

```
− ⟨Curv, ∇S⟩_{L²} ≤ Ccross · (‖∇S‖²_{L²} + ‖S‖_{L²} · ‖∇S‖_{L²})
```

holds with `Ccross ≥ 0`. Then the order-`2` Gårding estimate

```
‖∇²S‖²_{L²} ≤ (2 + 2 · Ccross) · (‖Δ_∇ S‖²_{L²} + ‖S‖²_{L²})
```

holds, where `∇²S = covGrad g 0 (s+1) (covGrad g 0 s S)`. The proof combines the
integrated order-`2` Weitzenböck identity
`‖∇²S‖² = ‖Δ_∇ S‖² − ⟨Curv, ∇S⟩`, the cross-term hypothesis, the order-`1` control
`‖∇S‖² ≤ ‖Δ_∇ S‖ · ‖S‖`, and Young's inequality `2ab ≤ a² + b²` on the resulting
`‖Δ_∇ S‖ · ‖S‖` and `‖S‖ · √(‖Δ_∇ S‖ · ‖S‖)` cross terms.

The curvature cross-term bound is the integrated curvature content of the route: by
the Ricci identity on the gradient field (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`)
and the uniform fibre-norm curvature bound
(`riemannOp_covGrad_fiberNormSq_le_gen`, the section-uniform `‖R‖_∞` on the compact
manifold), the fibrewise commutator is an `R`-contraction of `∇S`, controlled by
`‖R‖_∞ · (rfns(∇S) + rfns(S))`. The reduction never reads the gradient slot pointwise
and never differentiates the curvature. -/
theorem secondCovGrad_l2NormSq_le_of_cross_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Ccross : ℝ) (hCcross : 0 ≤ Ccross)
    (hcross :
      - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S) -
              covGrad (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun ≤
        Ccross *
          (tensorL2Norm (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 +
            tensorL2Norm (I := I) (M := M) g 0 s S.toFun *
              tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toFun)) :
    tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 ≤
      (2 + 2 * Ccross) *
        (tensorL2Norm (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 s S.toFun ^ 2) := by
  classical
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
    (covGrad (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S)).toFun with hnHess_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1)
    (covGrad (I := I) (M := M) g 0 s S).toFun with hnGrad_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g 0 s
    (rawTensorConnLapSmooth (I := I) g 0 s S).toFun with hnLap_def
  set nS : ℝ := tensorL2Norm (I := I) (M := M) g 0 s S.toFun with hnS_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + 1) _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g 0 s _
  have hnS_nn : 0 ≤ nS := tensorL2Norm_nonneg (I := I) (M := M) g 0 s _
  have hweitz :
      nHess ^ 2 =
        nLap ^ 2 -
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S) -
              covGrad (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [hnHess_def, hnLap_def]
    exact weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g s S
  have horder1 : nGrad ^ 2 ≤ nLap * nS := by
    rw [hnGrad_def, hnLap_def, hnS_def]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self_gen (I := I) (M := M) g s S
  have hstep1 : nHess ^ 2 ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nS * nGrad) := by
    have hcross' :
        - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S) -
                covGrad (I := I) (M := M) g 0 s
                  (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun ≤
          Ccross * (nGrad ^ 2 + nS * nGrad) := by
      rw [hnGrad_def, hnS_def]; exact hcross
    rw [hweitz]
    linarith [hcross']
  have hyoung_ls : nLap * nS ≤ (nLap ^ 2 + nS ^ 2) / 2 := by
    nlinarith [sq_nonneg (nLap - nS)]
  have hyoung_sg : nS * nGrad ≤ (nS ^ 2 + nGrad ^ 2) / 2 := by
    nlinarith [sq_nonneg (nS - nGrad)]
  have hbracket : nGrad ^ 2 + nS * nGrad ≤ 2 * (nLap ^ 2 + nS ^ 2) := by
    have h1 : nGrad ^ 2 ≤ (nLap ^ 2 + nS ^ 2) / 2 := le_trans horder1 hyoung_ls
    have h2 : nS * nGrad ≤ (nS ^ 2 + nGrad ^ 2) / 2 := hyoung_sg
    have h3 : nGrad ^ 2 ≤ (nLap ^ 2 + nS ^ 2) / 2 := h1
    nlinarith [h1, h2, h3]
  have hkey : Ccross * (nGrad ^ 2 + nS * nGrad) ≤ Ccross * (2 * (nLap ^ 2 + nS ^ 2)) :=
    mul_le_mul_of_nonneg_left hbracket hCcross
  have hnLapSq_nn : 0 ≤ nLap ^ 2 := sq_nonneg _
  have hnSSq_nn : 0 ≤ nS ^ 2 := sq_nonneg _
  calc nHess ^ 2
      ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nS * nGrad) := hstep1
    _ ≤ nLap ^ 2 + Ccross * (2 * (nLap ^ 2 + nS ^ 2)) := by linarith [hkey]
    _ ≤ (2 + 2 * Ccross) * (nLap ^ 2 + nS ^ 2) := by nlinarith [hnLapSq_nn, hnSSq_nn]

end Connection
end Integral
end DifferentialGeometry

end
