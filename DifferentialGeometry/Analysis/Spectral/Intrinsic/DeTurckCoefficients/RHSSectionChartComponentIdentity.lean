import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieMatrixChartBridge
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Geometry.Flow.LieDerivativeChartFrameIdentity
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent

/-!
# The section↔chart raw-component identity for the realized Ricci–DeTurck RHS

For a smooth Riemannian metric `g₁` the *genuine geometric Ricci–DeTurck right-hand side*
`deTurckRHSSection g_bg g₁` is a smooth `(0,2)`-tensor section.  This file proves that, on the
chart-`α` Levi–Civita good set, its raw chart-`α`-frame `(0,2)`-component (read through the
`g_bg`-retagged carrier `deTurckRHSSectionBg g_bg g₁`) equals the **textbook chart-coordinate
Ricci–DeTurck carrier**
`-2 · chartRicciTensor g₁ α (Jdx 0) (Jdx 1) (ϕ_α b) + chartLieDeTurckComp g₁ g_bg α (Jdx 0) (Jdx 1) (ϕ_α b)`.

This is the **section↔chart identity** that lets the all-order chart-jet Faà-di-Bruno Lipschitz
tower (`exists_chartRicciTensor_iteratedFDeriv_lipschitz_on_compact`,
`exists_chartLieDeTurckComp_iteratedFDeriv_lipschitz_on_compact`) control the Fréchet jets of the
raw chart components of the realized RHS section.

## Mathematical content

`deTurckRicciRHS g_bg g = -2 · Ric(g) + 𝓛_{W(g, g_bg)} g`.  Evaluated on the chart-`α` frame pair
`(e^α_i b, e^α_j b)`, the Ricci slot becomes `chartRicciTensor g α i j (ϕ_α b)` by the off-centre
Ricci basis identity (`ricciTensor_chartBasisVec_alpha_eq`), and the Lie slot becomes
`chartLieDeTurckComp g g_bg α i j (ϕ_α b)` by the Cartan-formula chart matrix
(`chartLieDerivMetricMatrix_eq_lieDerivMetric_chartBasis`) composed with the textbook carrier
identification (`chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp`).  The raw `(0,2)`
component is exactly that bilinear evaluation, via the trivialisation-projection↔chart-basis
identity (`section_compCLM_eval_eq_tensorChartComponentRaw` at `r = 0`) and the section value
identity (`deTurckRHSSection_toModel_apply`).

## Main result

* `tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie` — the raw chart-`α`-frame
  `(0,2)`-component of `deTurckRHSSectionBg g_bg g₁` equals
  `-2 · chartRicciTensor g₁ α (Jdx 0) (Jdx 1) (ϕ_α b) + chartLieDeTurckComp g₁ g_bg α (Jdx 0) (Jdx 1) (ϕ_α b)`,
  on the chart-`α` Levi–Civita good set.
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
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
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

/-- **The raw chart-`α`-frame `(0,2)`-component of the realized Ricci–DeTurck RHS section equals
its bilinear evaluation on the chart-`α` frame pair.**

For a base point `b` in the chart-`α` source and a covariant multi-index `Jdx : Fin 2 → Fin n`,
the raw chart-`α` `(0,2)`-component of `deTurckRHSSectionBg g_bg g₁` at `b` equals the
Ricci–DeTurck bilinear value `deTurckRicciRHS g_bg g₁ b (e^α_{Jdx 0} b) (e^α_{Jdx 1} b)` on the
chart-`α` frame vectors.  This composes the closed-form raw chart-component identity
`tensorChartComponentRaw_eq_chartFrame` (the raw `(0,2)` component is `S.toSection b` applied to the
chart-frame basis element at the empty input multi-index and evaluated on the chart-frame tuple)
with the realized RHS section value `deTurckRHSSection_toModel_apply`. -/
private theorem tensorChartComponentRaw_deTurckRHSSectionBg_eq_deTurckRicciRHS
    (g_bg g₁ : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ (chartAt H α).source)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
        (deTurckRHSSectionBg (I := I) g_bg g₁) α Idx Jdx b =
      deTurckRicciRHS (I := I) g_bg g₁ b
        (chartBasisVecFiber (I := I) α (Jdx 0) b)
        (chartBasisVecFiber (I := I) α (Jdx 1) b) := by
  classical

  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (deTurckRHSSectionBg (I := I) g_bg g₁) α hb Idx Jdx]

  have hframe : chartFrameBasisModel (I := I) (M := M) α b 0 Idx =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I b) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α b 0 Idx v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe]

  have hmodel := deTurckRHSSection_toModel_apply (I := I) g_bg g₁ b
    (fun k : Fin 2 => chartBasisVecFiber (I := I) α (Jdx k) b)

  rw [show (deTurckRHSSectionBg (I := I) g_bg g₁).toSection b =
      (deTurckRHSSection (I := I) g_bg g₁).toSection b from rfl]

  have hdirect :
      ((deTurckRHSSection (I := I) g_bg g₁).toSection b
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I b) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I b) ℝ)
        (fun k : Fin 2 => chartBasisVecFiber (I := I) α (Jdx k) b) =
      Tensor0SSpace.toModel
        ((deTurckRHSSection (I := I) g_bg g₁).toSection b
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I b) (1 : ℝ)))
        (fun k : Fin 2 => chartBasisVecFiber (I := I) α (Jdx k) b) := rfl
  rw [hdirect, hmodel]

/-- **The section↔chart raw-component identity for the realized Ricci–DeTurck RHS.**

For two smooth Riemannian metrics `g_bg, g₁`, a chart base point `α`, and a base point `b` in the
chart-`α` Levi–Civita good set, the raw chart-`α`-frame `(0,2)`-component of the realized RHS
section `deTurckRHSSectionBg g_bg g₁` at `b` equals the textbook chart-coordinate Ricci–DeTurck
carrier `-2 · chartRicciTensor g₁ α (Jdx 0) (Jdx 1) (ϕ_α b) + chartLieDeTurckComp g₁ g_bg α (Jdx 0) (Jdx 1) (ϕ_α b)`. -/
theorem tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
    (g_bg g₁ : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
        (deTurckRHSSectionBg (I := I) g_bg g₁) α Idx Jdx b =
      (-2 : ℝ) * chartRicciTensor (I := I) g₁ α (Jdx 0) (Jdx 1) (extChartAt I α b) +
        chartLieDeTurckComp (I := I) g₁ g_bg α (Jdx 0) (Jdx 1) (extChartAt I α b) := by
  classical
  have hb_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  set v₀ : TangentSpace I b := chartBasisVecFiber (I := I) α (Jdx 0) b with hv₀_def
  set v₁ : TangentSpace I b := chartBasisVecFiber (I := I) α (Jdx 1) b with hv₁_def

  rw [tensorChartComponentRaw_deTurckRHSSectionBg_eq_deTurckRicciRHS (I := I) (M := M) g_bg g₁ α
      hb_src Idx Jdx]
  rw [show chartBasisVecFiber (I := I) α (Jdx 0) b = v₀ from rfl,
    show chartBasisVecFiber (I := I) α (Jdx 1) b = v₁ from rfl]

  rw [deTurckRicciRHS, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

  have hRic :
      ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g₁) b v₀ v₁ =
        chartRicciTensor (I := I) g₁ α (Jdx 0) (Jdx 1) (extChartAt I α b) := by
    have h := ricciTensor_chartBasisVec_alpha_eq (I := I) g₁ α (Jdx 0) (Jdx 1) hb
    rw [hv₀_def, hv₁_def]
    exact h

  have hLie :
      lieDerivMetricClm (I := I) g₁
        (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
          (smoothRiemannianMetricToInfty (I := I) g_bg)) b v₀ v₁ =
        chartLieDeTurckComp (I := I) g₁ g_bg α (Jdx 0) (Jdx 1) (extChartAt I α b) := by
    rw [lieDerivMetricClm_apply]
    have hmat := chartLieDerivMetricMatrix_eq_lieDerivMetric_chartBasis (I := I)
      (smoothRiemannianMetricToInfty (I := I) g₁)
      (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
        (smoothRiemannianMetricToInfty (I := I) g_bg))
      α (Jdx 0) (Jdx 1) b hb
    rw [hv₀_def, hv₁_def, ← hmat]
    exact chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp (I := I) g₁ g_bg α
      (Jdx 0) (Jdx 1) hb
  rw [hRic, hLie]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
