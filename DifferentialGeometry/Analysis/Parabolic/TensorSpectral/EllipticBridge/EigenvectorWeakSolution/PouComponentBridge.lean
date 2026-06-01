import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.WeakSolutionHeadline
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.CanonicalTensorRepr

/-!
# The partition-of-unity-weighted per-component scalar weak-solution headline

For a smooth Riemannian metric `g` on a closed (compact, boundaryless) smooth
manifold `M`, a chart center `α : M`, tensor ranks `(r, s)`, and a component
multi-index `P₀`, the per-component scalar elliptic-regularity analysis of the
connection Laplacian has two slightly different chart-coordinate scalars in
play.

* The Euclidean object on which the chart-local divergence-form analysis
  operates — and the conclusion of the per-component weak-solution headline
  `tensorComponent_isSmoothWeakSolution` — is the **raw** Euclidean chart
  component `tensorComponentEuclid g r s T α P₀`: the Euclidean push-forward of
  the un-partition-of-unity-weighted chart-frame scalar component
  `tensorChartComponentRaw`.

* The canonical chart component of an abstract `L²` tensor element
  (`tensorL2ChartComponent`) is, on a smooth section, the **partition-of-unity-
  weighted** Euclidean chart component `tensorChartComponent g r s S α P₀.1 P₀.2`:
  the Euclidean push-forward of `tensorChartComponentPou`, the chart-atlas
  partition-of-unity weight `chartAtlasPOU I M α` times `tensorChartComponentRaw`.

This file bridges the two. The partition-of-unity weight `chartAtlasPOU I M α`
is a smooth function on `M`; multiplying a smooth compactly-supported tensor
section `S` by it produces another smooth compactly-supported tensor section
`pouSmul g r s α S`. Because the chart-frame component projection is fibrewise
linear, the raw chart component of `pouSmul g r s α S` equals the partition-of-
unity weight times the raw chart component of `S`, i.e. the weighted component
`tensorChartComponentPou` of `S`. Pushing this identity to Euclidean space
gives

```
tensorChartComponent g r s S α P₀.1 P₀.2 = tensorComponentEuclid g r s (pouSmul g r s α S) α P₀.
```

Substituting `pouSmul g r s α S` for the solution section `T` in
`tensorComponent_isSmoothWeakSolution` therefore yields the partition-of-unity-
weighted analogue of that headline: the canonical chart component
`tensorChartComponent g r s S α P₀.1 P₀.2` is a smooth weak solution of the
principal-part elliptic bilinear form `tensorPrincipalForm g α hK hK_target`.
The chart-source support hypothesis that `tensorComponent_isSmoothWeakSolution`
places on its solution section is automatic for `pouSmul g r s α S`: the
chart-atlas partition of unity is subordinate to the chart cover, so the
support of `chartAtlasPOU I M α • S` lies inside the chart source.

## Main definitions

* `pouSmul g r s α S` — the smooth compactly-supported tensor section
  `chartAtlasPOU I M α • S`, the chart-atlas partition-of-unity weight at `α`
  times the section `S`.

## Main results

* `tensorChartComponentRaw_smul_pou` — the raw chart-frame scalar component of
  `pouSmul g r s α S` is the partition-of-unity weight times the raw chart-frame
  scalar component of `S`.
* `pouSmul_tsupport_subset_chartSource` — `pouSmul g r s α S` is supported
  inside the chart source.
* `tensorChartComponent_eq_tensorComponentEuclid_pouSmul` — the weighted
  Euclidean chart component of `S` equals the raw Euclidean chart component of
  `pouSmul g r s α S`.
* `tensorChartComponent_isSmoothWeakSolution` — the partition-of-unity-weighted
  per-component scalar weak-solution headline: the canonical chart component
  `tensorChartComponent g r s S α P₀.1 P₀.2` is a smooth weak solution of the
  principal-part elliptic bilinear form, with the supplied right-hand side.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The chart-atlas partition-of-unity weight `chartAtlasPOU I M α` times a
smooth compactly-supported `(r, s)`-tensor section `S`, packaged as a smooth
compactly-supported tensor section. The underlying section is the pointwise
scalar product `fun x => chartAtlasPOU I M α x • S.toSection x`. -/
noncomputable def pouSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toSection x
      contMDiff_toFun := by
        exact ContMDiff.smul_section
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff S.toSection.contMDiff }
  hasCompactSupport := by
    classical
    refine HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport ?_
    intro x hx
    rw [Function.mem_support] at hx
    refine subset_tsupport S.toFun ?_
    rw [Function.mem_support]
    intro hS_zero
    apply hx
    change TensorRSSpace.toModel
      (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toSection x) = 0
    rw [TensorRSSpace.toModel_smul,
      show TensorRSSpace.toModel (S.toSection x) = S.toFun x from rfl, hS_zero,
      smul_zero]

/-- The underlying section of `pouSmul g r s α S` is the pointwise scalar
product of the partition-of-unity weight and the underlying section of `S`. -/
lemma pouSmul_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (x : M) :
    (pouSmul (I := I) (M := M) g r s α S).toSection x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toSection x := rfl

/-- The underlying map of `pouSmul g r s α S` is the pointwise scalar product of
the partition-of-unity weight and the underlying map of `S`. -/
lemma pouSmul_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (x : M) :
    (pouSmul (I := I) (M := M) g r s α S).toFun x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toFun x := by
  rw [SmoothCcTensor.toFun_apply, pouSmul_toSection_apply,
    TensorRSSpace.toModel_smul]
  rfl

/-- The trivialization-at-`α` projection of the partition-of-unity-weighted
section is the partition-of-unity weight times the trivialization projection of
`S`: the trivialization's fibrewise linear map is homogeneous. -/
private lemma tensorTrivProj_pouSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (x : M) :
    tensorTrivProj (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        tensorTrivProj (I := I) (M := M) g r s S α x := by
  unfold tensorTrivProj
  rw [pouSmul_toSection_apply]
  exact map_smul _ _ _

/-- **The raw chart component of the partition-of-unity-weighted section.** The
raw chart-frame scalar component of `pouSmul g r s α S` is the partition-of-
unity weight `chartAtlasPOU I M α` times the raw chart-frame scalar component of
`S`. This is the fibrewise linearity of the trivialization projection composed
with the chart-frame component projection. -/
theorem tensorChartComponentRaw_smul_pou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx =
      fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x := by
  funext x
  unfold tensorChartComponentRaw
  rw [tensorTrivProj_pouSmul (I := I) (M := M) g r s α S x, map_smul,
    smul_eq_mul]

/-- The raw chart-frame scalar component of `pouSmul g r s α S` is the weighted
chart-frame scalar component `tensorChartComponentPou` of `S`: both equal
`chartAtlasPOU I M α` times the raw chart-frame scalar component of `S`. -/
theorem tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx =
      tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx := by
  rw [tensorChartComponentRaw_smul_pou (I := I) (M := M) g r s α S Idx Jdx]
  rfl

/-- **The partition-of-unity-weighted section is chart-supported.** The
topological support of the underlying map of `pouSmul g r s α S` is contained
in the chart-`α` source: the underlying map vanishes wherever the partition-of-
unity weight does, and the chart-atlas partition of unity is subordinate to the
chart cover. -/
theorem pouSmul_tsupport_subset_chartSource
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    tsupport (pouSmul (I := I) (M := M) g r s α S).toFun ⊆
      (chartAt H α).source := by
  classical
  have hfun_eq : (pouSmul (I := I) (M := M) g r s α S).toFun =
      fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        S.toFun x := by
    funext x
    exact pouSmul_toFun_apply (I := I) (M := M) g r s α S x
  rw [hfun_eq]
  have h_supp_sub : Function.support
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        S.toFun x) ⊆
      Function.support
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hweight_zero
    exact hx (by rw [hweight_zero, zero_smul])
  refine (closure_mono h_supp_sub).trans ?_
  exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate
    I M) α

/-- **The weighted Euclidean chart component is a raw Euclidean chart component.**
The partition-of-unity-weighted Euclidean chart component of `S` at the
component multi-index `P₀` equals the raw Euclidean chart component of the
partition-of-unity-weighted section `pouSmul g r s α S` at `P₀`. -/
theorem tensorChartComponent_eq_tensorComponentEuclid_pouSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (P₀ : CompIdx E r s) :
    tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 =
      tensorComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀ := by
  rw [tensorComponentEuclid_def, tensorChartComponent_def,
    tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
      (I := I) (M := M) g r s α S P₀.1 P₀.2]

/-- **The partition-of-unity-weighted per-component scalar weak-solution
headline of the connection Laplacian.**

Let `g` be a smooth Riemannian metric on a closed (compact, boundaryless) smooth
manifold `M`, let `α : M` be a chart center, and let `S` (the solution) and `F`
(the source) be smooth compactly-supported `(r, s)`-tensor sections. Let
`K ⊆ chartTargetEuclid α` be compact with the partition-of-unity-weighted
Euclidean chart component `tensorChartComponent g r s S α P₀.1 P₀.2` supported
inside `K`, and `P₀ : CompIdx E r s` a component multi-index.

If `F` is supported inside the chart source and the global `H^1` weak equation
`∫_M ⟨∇(ζ_α • S), ∇v⟩ dμ_g = ⟨F, v⟩_{L²}` of the connection Laplacian — for the
partition-of-unity-weighted solution section `pouSmul g r s α S` — holds for
every smooth compactly-supported test section `v`, then the canonical
(partition-of-unity-weighted) Euclidean chart component
`tensorChartComponent g r s S α P₀.1 P₀.2` is a smooth weak solution of the
principal-part elliptic bilinear form `tensorPrincipalForm g α hK hK_target`
with right-hand side
`tensorComponentWeakRHS g r s (pouSmul g r s α S) F α hK hK_target P₀`. -/
theorem tensorChartComponent_isSmoothWeakSolution
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hS_K : tsupport
        (tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (pouSmul (I := I) (M := M) g r s α S) v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
      (tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2)
      (tensorComponentWeakRHS (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) F α hK hK_target P₀) := by
  classical
  have hcomp_eq :
      tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        tensorComponentEuclid (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α S) α P₀ :=
    tensorChartComponent_eq_tensorComponentEuclid_pouSmul
      (I := I) (M := M) g r s α S P₀
  have hpou_supp :
      tsupport (pouSmul (I := I) (M := M) g r s α S).toFun ⊆
        (chartAt H α).source :=
    pouSmul_tsupport_subset_chartSource (I := I) (M := M) g r s α S
  have hpou_K :
      tsupport (tensorComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀) ⊆ K := by
    rw [← hcomp_eq]; exact hS_K
  rw [hcomp_eq]
  exact tensorComponent_isSmoothWeakSolution (I := I) (M := M) g r s
    (pouSmul (I := I) (M := M) g r s α S) F α hK hK_target P₀
    hpou_supp hF_supp hpou_K hweak

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
