import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerLowerBound
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import DifferentialGeometry.Tensor.Multilinear.Bundle
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Basic

/-!
# Bridge identity between `tensorTrivProj` and the chart-`(α, b)`-twist

For a smooth compactly-supported `(r, s)`-tensor section `S : SmoothCcTensor g r s`
over a closed smooth manifold `M`, two algebraic gadgets describe the same
underlying data in slightly different ways:

* `tensorTrivProj g r s S α b : TensorRSModel r s ℝ E` — the value of the
  Hom-bundle trivialization at chart center `α`, applied at base point `b`,
  to the smooth bundle section `S.toSection b`. Concretely, this is the
  composition
  `(triv_0Ss α).continuousLinearMapAt ℝ b ∘L (S.toSection b) ∘L
   (triv_0Sr α).symmL ℝ b`, where `triv_0Sk α` is the trivialization at `α`
  of the `(0, k)`-tensor bundle (itself derived from the tangent
  trivialization at `α`).

* `S.toFun b : TensorRSModel r s ℝ E` — the value of the canonical bundle-
  to-model identification `TensorRSSpace.toModel`, applied to `S.toSection b`.
  This is `arrowCongr` of the `(0, k)`-fibre `≃L[ℝ]`-equivs, which are
  identity at the function level.

The trivialization-projected value differs from `S.toFun b` by a
`chartJ`/`chartJinv`-twist on the `r`-block input and `s`-block output:
the inverse twist `chartRSTwistInv α b r s` precomposes the input with
`chartJ α b` and postcomposes the output with `chartJinv α b`, which is
exactly the composition pattern produced by the Hom-bundle pretrivialization
formula.

This file ships the identity

```
tensorTrivProj g r s S α b = chartRSTwistInv α b r s (S.toFun b)
```

valid for `b` in the chart-`α` base set.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The `continuousLinearMapAt ℝ b` of the `(0, r)`-tensor trivialization at
`α`, applied to a fibre element `T : Tensor0SSpace r I b`, precomposes the
multilinear slots with `chartJinv α b`. Holds on the chart-`α` base set. -/
private lemma tensor0S_trivialization_continuousLinearMapAt_apply
    (α : M) {b : M} (r : ℕ)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : Tensor0SSpace r I b) :
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b T =
      (T : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ).compContinuousLinearMap
        (fun _ : Fin r => chartJinv (I := I) (M := M) α b) := by
  have hbase : b ∈ (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet := by
    change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact hb
  have hcoe := (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).coe_linearMapAt_of_mem (R := ℝ) hbase
  change ((trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).linearMapAt ℝ b) T = _
  rw [show ((trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).linearMapAt ℝ b) T =
        ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α) ⟨b, T⟩).2 from
      congrFun hcoe T]
  rfl

/-- The `symmL ℝ b` of the `(0, r)`-tensor trivialization at `α`, applied
to a model fibre element `V : Tensor0SModel r ℝ E`, precomposes the
multilinear slots with `chartJ α b`. Holds on the chart-`α` base set. -/
private lemma tensor0S_trivialization_symmL_apply
    (α : M) {b : M} (r : ℕ)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (V : Tensor0SModel r ℝ E) :
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b V =
      V.compContinuousLinearMap
        (fun _ : Fin r => chartJ (I := I) (M := M) α b) := by
  have hbase : b ∈ (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet := by
    change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact hb
  have h := _root_.Pretrivialization.continuousMultilinearMap_symm_apply'
    (𝕜 := ℝ) (s := r) (F := E) (E := (TangentSpace I : M → Type _))
    (e := trivializationAt E (TangentSpace I) α) (b := b) hb V
  change (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).symm b V = _
  rw [show (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).symm b V =
        ((Pretrivialization.continuousMultilinearMap (𝕜 := ℝ) (s := r)
          (F := E) (E := (TangentSpace I : M → Type _))
          (trivializationAt E (TangentSpace I) α)).symm b V) from rfl]
  rw [h]
  rfl

/-- **Bridge identity**: on the chart-`α` base set, the trivialization-`α`
projection of a smooth `(r, s)`-tensor section at `b` equals the inverse
chart-`(α, b)`-twist of the canonical model-fibre value `S.toFun b`.

Explicitly:
```
tensorTrivProj g r s S α b
  = chartRSTwistInv α b r s (S.toFun b)
```

The inverse twist precomposes the input on the `r`-block with `chartJ α b`
and postcomposes the output on the `s`-block with `chartJinv α b`, which is
exactly the composition pattern produced by the Hom-bundle pretrivialization
formula. -/
theorem tensorTrivProj_eq_chartRSTwistInv_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    tensorTrivProj (I := I) (M := M) g r s S α b =
      chartRSTwistInv (I := I) (M := M) α b r s (S.toFun b) := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  unfold tensorTrivProj
  have hbaseHom : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseHom
  change ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b (S.toSection b)) α' = _
  have hval :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b (S.toSection b)) =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, S.toSection b⟩).2 :=
    congrFun hcoeRS (S.toSection b)
  rw [hval]
  have hHom :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, S.toSection b⟩
        = ⟨b, ((trivializationAt (Tensor0SModel s ℝ E)
            (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
            : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
              ((S.toSection b).comp
                ((trivializationAt (Tensor0SModel r ℝ E)
                  (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
                  : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))⟩ := rfl
  rw [hHom]
  change (((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
      ((S.toSection b).comp
        ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
          : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))) α' = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [tensor0S_trivialization_symmL_apply (I := I) (M := M) α r hb α']
  rw [tensor0S_trivialization_continuousLinearMapAt_apply (I := I) (M := M) α s hb
    ((S.toSection b) (α'.compContinuousLinearMap
      (fun _ : Fin r => chartJ (I := I) (M := M) α b)))]
  rw [chartRSTwistInv_apply]
  rfl

/-- **Reverse orientation** of `tensorTrivProj_eq_chartRSTwistInv_toFun`: the
forward twist of `tensorTrivProj` recovers `S.toFun`. -/
theorem chartRSTwist_tensorTrivProj_eq_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartRSTwist (I := I) (M := M) α b r s
        (tensorTrivProj (I := I) (M := M) g r s S α b) =
      S.toFun b := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [tensorTrivProj_eq_chartRSTwistInv_toFun (I := I) (M := M) g r s α S hb]
  rw [chartRSTwist_apply, chartRSTwistInv_apply]
  have hinner :
      (α'.compContinuousLinearMap
          (fun _ : Fin r => chartJinv (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin r => chartJ (I := I) (M := M) α b) = α' := by
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJinv_chartJ_self (I := I) (M := M) α hb (v k)
  rw [hinner]
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext k
  exact chartJinv_chartJ_self (I := I) (M := M) α hb (w k)

/-- **Generalized bridge identity (pointwise, in the fibre)**: on the
chart-`α` source, the trivialization's `continuousLinearMapAt ℝ b` action on
an arbitrary fibre element `T : TensorRSSpace r s I b` equals the inverse
chart-`(α, b)`-twist of the model-fibre value `TensorRSSpace.toModel T`.

Explicitly:
```
(triv_RS α).continuousLinearMapAt ℝ b T
  = chartRSTwistInv α b r s (TensorRSSpace.toModel T)
```

This is the section-independent kernel of
`tensorTrivProj_eq_chartRSTwistInv_toFun`. -/
theorem triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source)
    (T : TensorRSSpace r s I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T =
      chartRSTwistInv (I := I) (M := M) α b r s (TensorRSSpace.toModel T) := by
  classical
  have hb' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  refine ContinuousLinearMap.ext ?_
  intro α'
  have hbaseHom : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb'
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb'
  have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseHom
  change ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b T) α' = _
  have hval :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b T) =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, T⟩).2 :=
    congrFun hcoeRS T
  rw [hval]
  have hHom :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, T⟩
        = ⟨b, ((trivializationAt (Tensor0SModel s ℝ E)
            (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
            : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
              (T.comp
                ((trivializationAt (Tensor0SModel r ℝ E)
                  (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
                  : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))⟩ := rfl
  rw [hHom]
  change (((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
      (T.comp
        ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
          : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))) α' = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [tensor0S_trivialization_symmL_apply (I := I) (M := M) α r hb' α']
  rw [tensor0S_trivialization_continuousLinearMapAt_apply (I := I) (M := M) α s hb'
    (T (α'.compContinuousLinearMap
      (fun _ : Fin r => chartJ (I := I) (M := M) α b)))]
  rw [chartRSTwistInv_apply]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
