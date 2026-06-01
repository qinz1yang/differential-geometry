import DifferentialGeometry.Integral.Connection.TensorCovGradL2InnerDirichletBridge
import DifferentialGeometry.Integral.Connection.TensorLoweringParallel

/-!
# Lowered directional reductions for the connection-Laplacian Green identity

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file develops the *lowered directional* reductions
of the pointwise Dirichlet integrand `tensorCovDerivPointwiseInner g 0 s T v`
that feed the integrated Green identity for the rough (connection) Laplacian.

The target Green identity, for two smooth compactly-supported `(0, s)`-tensor
sections `T`, `v`, is

```
tensorL2Inner g 0 (s + 1) (covGrad g 0 s T).toFun (covGrad g 0 s v).toFun
  = − tensorL2Inner g 0 s (rawTensorConnLapSmooth g 0 s T).toFun v.toFun,
```

obtained by combining the gradient-side bridge
`tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner` with the
diagonal-frame reduction and the directional integration-by-parts machinery.

The integration-by-parts machinery is stated entirely in *lowered* directional
form, through `loweredCovDerivAlongVF` and the covariant `(0, r + s)` inner
product `tensorInnerPointwise_0s`, whereas the Dirichlet integrand
`tensorCovDerivPointwiseInner` and the rough Laplacian `rawTensorConnLap` are
phrased through the *un-lowered* `(r, s)`-tensor covariant derivative. The
reductions in this file are the bridge between the two presentations at rank
`r = 0`.

## Main results

* `toModel_liftedTensorSection_zero_eq_apply_unit_reindex` — the general `(0, s)`
  reindexed unit-evaluation of the lifted section (the genuine `(0, s)` analogue
  of the committed `(0, 2)` lemma `liftedTensorSection_zero_eq_apply_unit`,
  recorded through the `Fin.natAdd 0` index reindexing the lowering map inserts).

* `tensorInnerPointwise_covDeriv_eq_tensorInnerPointwise_0s_lowered_two` — at
  `(0, 2)`, the mixed pointwise inner product of two un-lowered directional
  covariant derivatives equals the covariant `(0, 0 + 2)` inner product of the
  corresponding lowered directional derivatives `loweredCovDerivAt`.

* `tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two` — at `(0, 2)`,
  the full diagonal-frame reduction: for a smooth tangent frame field `B` that is
  `g_b`-orthonormal at the evaluation point `b`, the inverse-Gram-weighted
  Dirichlet integrand equals the plain diagonal sum over `B` of the covariant
  `(0, 0 + 2)` inner products of the lowered directional derivatives. This is the
  precise per-point integrand consumed by the directional integration-by-parts
  machinery once a fixed smooth orthonormal frame field is supplied (chart by
  chart through the partition of unity, with `B = chartFrameNormGlobalSmooth`).

At rank `r = 0` the metric index-lowering is metric-free (it contracts no upper
slots), so the lowering intertwiner needs no metric-compatibility input. Rank
`(0, 2)` is the rank that the downstream Ricci–DeTurck application requires (the
metric perturbation is a `(0, 2)`-tensor); there the lowered index `0 + 2`
reduces definitionally to `2`, so the committed `(0, 2)` intertwiner applies
directly.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Rank-`0` lowering is evaluation at the unit `(0, 0)`-tensor (general `(0, s)`),
in reindexed-evaluation form.** At rank `r = 0` the model coercion of the
metric-lowered `(0, 0 + s)`-tensor section value `liftedTensorSection g 0 s S y`,
evaluated on a tuple `u : Fin (0 + s) → E`, equals the model coercion of `S y`
evaluated at the constant unit `(0, 0)`-tensor `ofModel (constOfIsEmpty 1)` and
the reindexed tuple `fun j : Fin s => u (Fin.natAdd 0 j)`. This is the genuine
`(0, s)` analogue of the committed `(0, 2)` lemma
`liftedTensorSection_zero_eq_apply_unit`: at general `s`, the source index `s`
and the lowered index `0 + s` differ as Lean types, so the relation is recorded
through the `Fin.natAdd 0` reindexing inserted by the lowering map. -/
lemma toModel_liftedTensorSection_zero_eq_apply_unit_reindex
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (y : M) (u : Fin (0 + s) → E) :
    Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 s S y) u =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S y)
            (Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))))
        (fun j : Fin s => u (Fin.natAdd 0 j)) := by
  rw [toModel_liftedTensorSection]
  rw [lowerAllUpperIndices_apply]
  rw [separableFormAt_zero]
  rw [toModel_tensorRS_apply (I := I) (M := M) 0 s y (S y)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))]
  rw [Tensor0SSpace.toModel_ofModel]

/-- **Mixed inner product of two un-lowered directional derivatives equals the
covariant `(0, 0 + 2)` inner product of the lowered derivatives (at `(0, 2)`).**
For smooth `(0, 2)`-tensor sections `W`, `S`, a point `x`, and tangent vectors
`a`, `b`,

  `tensorInnerPointwise g 0 2 x (∇_a W) (∇_b S)
     = tensorInnerPointwise_0s (0 + 2) g x (∇_a^lowered W) (∇_b^lowered S)`,

where `∇_·` is the un-lowered `(0, 2)`-tensor covariant derivative and `∇_·^lowered`
the lowered directional derivative `loweredCovDerivAt`. Both sides are the same
metric contraction; the identity is the index-lowering intertwiner applied to
each argument together with the definition of `tensorInnerPointwise`. -/
theorem tensorInnerPointwise_covDeriv_eq_tensorInnerPointwise_0s_lowered_two
    (g : SmoothRiemannianMetric I M)
    (W S : SmoothCcTensor g 0 2) (x : M) (a b : TangentSpace I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 W x a))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 S x b)) =
      tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g 0 2 W.toSection x a))
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g 0 2 S.toSection x b)) := by
  unfold tensorInnerPointwise
  rw [show lowerAllUpperIndices (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 W x a)) =
      Tensor0SSpace.toModel
        (loweredCovDerivAt (I := I) (M := M) g 0 2 W.toSection x a) from
    (loweredCovDerivAt_eq_lower_tensorCovDerivAt (I := I) (M := M) g W.toSection x a).symm]
  rw [show lowerAllUpperIndices (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 S x b)) =
      Tensor0SSpace.toModel
        (loweredCovDerivAt (I := I) (M := M) g 0 2 S.toSection x b) from
    (loweredCovDerivAt_eq_lower_tensorCovDerivAt (I := I) (M := M) g S.toSection x b).symm]

/-- **Diagonal-frame reduction of the Dirichlet integrand into the lowered
directional form (at `(0, 2)`).** For smooth `(0, 2)`-tensor sections `T`, `v`,
a point `b`, and a smooth tangent frame field `B` whose values `B i b` are
`g_b`-orthonormal at `b`, the inverse-Gram-weighted Dirichlet integrand equals
the plain diagonal sum over the frame of the covariant `(0, 0 + 2)` inner
products of the lowered directional covariant derivatives:

```
tensorCovDerivPointwiseInner g 0 2 T v b
  = ∑ i, tensorInnerPointwise_0s (0 + 2) g b
          (loweredCovDerivAt g 0 2 T.toSection b (B i b))
          (loweredCovDerivAt g 0 2 v.toSection b (B i b)).
```
-/
theorem tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (b : M)
    (B : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hB_orth : ∀ i j, g.inner b (B i b) (B j b) = if i = j then (1 : ℝ) else 0) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g b
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g 0 2 T.toSection b (B i b)))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g 0 2 v.toSection b (B i b))) := by
  classical
  have hB_li : LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) => B i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (B k b) (∑ j ∈ fs, c j • B j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner b (B k b) (c j • B j b) =
        c j * g.inner b (B k b) (B j b) := by
      intro j _
      rw [(g.inner b (B k b)).map_smul (c j) (B j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs, c j * g.inner b (B k b) (B j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ E := by
    rw [Fintype.card_fin]
  set frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with hframe_def
  have hframe_eq : ∀ i, frame i = B i b := by
    intro i
    rw [hframe_def]
    change (basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
        Fin (Module.finrank ℝ E) → E) i = B i b
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hframe_orth : ∀ i j,
      g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hframe_eq i, hframe_eq j]
    exact hB_orth i j
  rw [tensorCovDerivPointwiseInner_eq_orthoFrame_diag_sum
    (I := I) (M := M) g 0 2 T v b frame hframe_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe_eq i]
  exact tensorInnerPointwise_covDeriv_eq_tensorInnerPointwise_0s_lowered_two
    (I := I) (M := M) g T v b (B i b) (B i b)

end Connection
end Integral
end DifferentialGeometry

end
