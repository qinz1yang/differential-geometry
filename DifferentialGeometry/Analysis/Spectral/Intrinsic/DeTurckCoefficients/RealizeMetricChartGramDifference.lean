import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent
import DifferentialGeometry.Geometry.Operator.Hessian

/-!
# The chart-Gram difference of two realized metrics as a symmetric raw tensor component

For two fibre-small smooth perturbations `T, T'`, the realized metrics
`g₁ = g_bg + h_sym T = tensorSectionRealizeMetric g_bg T` and `g₂ = g_bg + h_sym T'` differ, in the
chart-`α` Gram matrix, by the chart-`α` Gram entries of the *symmetrized* perturbation difference
`h_sym(T − T')`.  Since the background `g_bg` cancels and `h_sym` is the symmetrization of the raw
extracted bilinear form `ccTensorBilin`, the pointwise chart-Gram difference is the symmetric raw
chart-`α`-frame `(0,2)`-component of the difference tensor `T − T'`:
```
chartGramOnE g₁ α a b y − chartGramOnE g₂ α a b y
  = ½ · (rawComp_{a,b}(T − T')(p) + rawComp_{b,a}(T − T')(p)),
```
where `p = (extChartAt I α).symm y` and `rawComp` is `tensorChartComponentRaw`.

This is the foundational identity that lets the chart-jet Faà-di-Bruno Lipschitz tower (which is
stated in terms of `chartGramJetDiffSeminormSum`, i.e. the chart-jet magnitude of the Gram
difference) be controlled by the covariant fibre-norm jets of the perturbation difference `T − T'`.

## Main result

* `chartGramOnE_realize_sub_eq_symm_rawComponent` — the pointwise chart-Gram difference of the two
  realized metrics equals the symmetrized raw chart-`α`-frame `(0,2)`-component of `T − T'`.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedSectionVars false in
/-- **The chart-`α` Gram entry of a realized metric equals the background Gram entry plus the
symmetrized extracted bilinear form of the perturbation.**

For a fibre-small perturbation `T` and a base point `x`, the chart-`α` Gram matrix entry of the
realized metric `tensorSectionRealizeMetric g_bg T` is `chartGramMatrix g_bg α x a b` plus the
symmetrized extracted bilinear form `ccTensorBilinSymm g_bg T x (e^α_a x) (e^α_b x)`. -/
theorem chartGramMatrix_realize_apply
    (g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (α x : M) (a b : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α x a b =
      chartGramMatrix (I := I) g_bg α x a b +
        ccTensorBilinSymm (I := I) g_bg T x
          (chartBasisVecFiber (I := I) α a x)
          (chartBasisVecFiber (I := I) α b x) := by
  rw [chartGramMatrix_apply, chartGramMatrix_apply,
    tensorSectionRealizeMetric_inner (I := I) g_bg T hδ_lt hδ x]

/-- **The chart-Gram difference of two realized metrics is the symmetrized raw `(0,2)`-component of
the perturbation difference.**

For two fibre-small perturbations `T, T'`, the pointwise chart-`α` Gram-entry difference of the two
realized metrics at a chart-target point `y` (read at the chart preimage `p = (extChartAt I α).symm
y` when `p ∈ (chartAt H α).source`) equals the symmetrized raw chart-`α`-frame `(0,2)`-component of
the difference tensor `T − T'`. -/
theorem chartGramOnE_realize_sub_eq_symm_rawComponent
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ)
    (α : M) (a b : Fin (Module.finrank ℝ E)) (y : E)
    (hp : (extChartAt I α).symm y ∈ (chartAt H α).source) :
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α a b y -
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T' hδ_lt hδ') α a b y =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![a, b] ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![b, a] ((extChartAt I α).symm y)) := by
  classical
  set p : M := (extChartAt I α).symm y with hp_def
  rw [chartGramOnE_def, chartGramOnE_def]
  rw [chartGramMatrix_realize_apply (I := I) g_bg T hδ_lt hδ α p a b,
    chartGramMatrix_realize_apply (I := I) g_bg T' hδ_lt hδ' α p a b]

  rw [show (chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p)) -
      (chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T' p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p)) =
      ccTensorBilinSymm (I := I) g_bg T p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) -
        ccTensorBilinSymm (I := I) g_bg T' p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) by ring]

  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]

  have hrawAB := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![a, b] : Fin 2 → Fin (Module.finrank ℝ E))
  have hrawBA := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![b, a] : Fin 2 → Fin (Module.finrank ℝ E))

  have hframe : chartFrameBasisModel (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe] at hrawAB hrawBA

  have hbilin : ∀ (i j : Fin (Module.finrank ℝ E)),
      ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
          (fun k : Fin 2 =>
            chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ccTensorBilin (I := I) g_bg T p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) -
          ccTensorBilin (I := I) g_bg T' p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) := by
    intro i j
    have hvecAB : (fun k : Fin 2 =>
        chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] := by
      funext k; fin_cases k <;> rfl
    rw [hvecAB, ccTensorBilin_apply, ccTensorBilin_apply]

    show Tensor0SSpace.toModel
        ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)))
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] = _
    rw [SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
    rfl
  rw [hrawAB, hrawBA, hbilin a b, hbilin b a]

  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  ring

/-- **The chart-Gram difference of two realized metrics, with separate fibre-small witnesses.**

The same symmetrized-raw-component identity as `chartGramOnE_realize_sub_eq_symm_rawComponent`, but
allowing the two perturbations `T, T'` to carry *separate* fibre-small witnesses `(δ, hδ)`,
`(δ', hδ')`.  The realized chart-Gram entries depend only on `g_bg + h_sym`, not on the positivity
witness, so the identity is witness independent. -/
theorem chartGramOnE_realize_sub_eq_symm_rawComponent_two_witness
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ')
    (α : M) (a b : Fin (Module.finrank ℝ E)) (y : E)
    (hp : (extChartAt I α).symm y ∈ (chartAt H α).source) :
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α a b y -
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T' hδ'_lt hδ') α a b y =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![a, b] ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![b, a] ((extChartAt I α).symm y)) := by
  classical
  set p : M := (extChartAt I α).symm y with hp_def
  rw [chartGramOnE_def, chartGramOnE_def]
  rw [chartGramMatrix_realize_apply (I := I) g_bg T hδ_lt hδ α p a b,
    chartGramMatrix_realize_apply (I := I) g_bg T' hδ'_lt hδ' α p a b]
  rw [show (chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p)) -
      (chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T' p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p)) =
      ccTensorBilinSymm (I := I) g_bg T p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) -
        ccTensorBilinSymm (I := I) g_bg T' p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) by ring]
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
  have hrawAB := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![a, b] : Fin 2 → Fin (Module.finrank ℝ E))
  have hrawBA := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![b, a] : Fin 2 → Fin (Module.finrank ℝ E))
  have hframe : chartFrameBasisModel (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe] at hrawAB hrawBA
  have hbilin : ∀ (i j : Fin (Module.finrank ℝ E)),
      ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
          (fun k : Fin 2 =>
            chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ccTensorBilin (I := I) g_bg T p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) -
          ccTensorBilin (I := I) g_bg T' p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) := by
    intro i j
    have hvecAB : (fun k : Fin 2 =>
        chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] := by
      funext k; fin_cases k <;> rfl
    rw [hvecAB, ccTensorBilin_apply, ccTensorBilin_apply]
    show Tensor0SSpace.toModel
        ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)))
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] = _
    rw [SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
    rfl
  rw [hrawAB, hrawBA, hbilin a b, hbilin b a]
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  ring

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
