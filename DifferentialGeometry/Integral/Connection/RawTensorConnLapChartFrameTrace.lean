import DifferentialGeometry.Integral.Connection.TensorConnLaplacian
import DifferentialGeometry.Integral.Connection.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Integral.L2.SmoothSections.Defs

/-!
# Chart-α frame trace identity for the raw tensor connection Laplacian

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, a smooth
compactly-supported `(r, s)`-tensor section `T : SmoothCcTensor g r s`, and a
chart base point `α : M`, this file ships the identity

```
rawTensorConnLap g r s (fun y => T.toSection y) b =
  rawTensorConnLap_fixedFrame g r s
    (fun i => (chartFrameNormGlobalSmooth g α i).toFun)
    (fun y => T.toSection y) b
```

valid at every base point `b` in the intersection of the chart-α
partition-of-unity tsupport with the chart-α Levi-Civita good set.

This is the chart-α flavour of the frame trace formula: the trace of the second
covariant derivative against the globally smooth chart-α frame realises the raw
connection Laplacian on the chart-α partition-of-unity tsupport portion of the
good set. The identity needs no additional predicate on the atlas; it follows
purely from the orthonormality of `chartFrameNormGlobalSmooth g α i` on the
intersection (shipped in `ChartFrameNormGlobalSmooth.lean`).

The headline composes three discharges into the workhorse lemma
`rawTensorConnLap_eq_fixedFrame_of_orthonormal`:

* smoothness of `T.toSection` as a total-space-valued map, from
  `ContMDiffSection.contMDiff`;
* smoothness of each `chartFrameNormGlobalSmooth g α i` as a total-space-valued
  map, again from `ContMDiffSection.contMDiff`;
* orthonormality of the chart-α frame at `b`, from
  `chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Chart-α frame trace identity for `rawTensorConnLap`.** For a smooth
compactly-supported `(r, s)`-tensor section `T`, a chart base point `α : M`,
and a base point `b` in the chart-α partition-of-unity tsupport intersected
with the chart-α Levi-Civita good set, the raw tensor connection Laplacian at
`b` equals the fixed-frame variant traced against the globally smooth chart-α
frame `chartFrameNormGlobalSmooth g α i`.

No predicate on the atlas (local-constancy of the chart map, chart-source
consistency, …) is required: orthonormality of the chart-α frame on the
intersection of the partition-of-unity tsupport with the chart-α Levi-Civita
good set, which is the genuine mathematical domain of the identity, is
already provided unconditionally by
`chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet`. -/
theorem rawTensorConnLap_via_chartFrameNormGlobalSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {b : M}
    (hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α) :
    rawTensorConnLap (I := I) g r s
        (fun y : M => T.toSection y) b =
      rawTensorConnLap_fixedFrame (I := I) g r s
        (fun i : Fin (Module.finrank ℝ E) =>
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
        (fun y : M => T.toSection y) b := by
  classical
  have hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) :=
    T.toSection.contMDiff
  have hB_smooth : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) y
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun y)) :=
    fun i => (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j =>
      chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
        (I := I) (M := M) g α hb i j
  exact rawTensorConnLap_eq_fixedFrame_of_orthonormal (I := I) g r s
    (fun y : M => T.toSection y) hT_total
    (B := fun i : Fin (Module.finrank ℝ E) =>
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
    hB_smooth b hB_orth

end Connection
end Integral
end DifferentialGeometry
