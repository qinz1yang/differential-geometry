import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Symmetry of the Ricci–DeTurck right-hand side

`deTurckRicciRHS g_bg g = −2 · Ric(g) + 𝓛_{W(g, g_bg)} g` is a sum of two
*symmetric* `(0,2)`-tensors: the Ricci tensor is symmetric (`ricciTensor_symm`)
and the metric Lie derivative is symmetric (`lieDerivMetric_isPointwiseSymm`),
the latter being the genuine `(0,2)`-tensor symmetry of `𝓛_W g`. -/

/-- **The Ricci–DeTurck right-hand side is a symmetric bilinear form:**
`deTurckRicciRHS g_bg g x v w = deTurckRicciRHS g_bg g x w v`. -/
theorem deTurckRicciRHS_symm
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    deTurckRicciRHS (I := I) g_bg g x v w =
      deTurckRicciRHS (I := I) g_bg g x w v := by
  simp only [deTurckRicciRHS, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, lieDerivMetricClm_apply]
  rw [ricciTensor_symm (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w,
    DeTurck.lieDerivMetric_isPointwiseSymm (I := I)
      (smoothRiemannianMetricToInfty (I := I) g)
      (DeTurck.deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w]

/-- The Ricci–DeTurck section `deTurckRHSSection g_bg g`, re-tagged from the
type-level metric tag `g` to the background tag `g_bg`.  The metric tag is a pure
type-level parameter (it does not appear in the carrier data, see `SmoothCcTensor`
in `Integral/L2/SmoothSections/Defs.lean`), so the underlying smooth section is
unchanged. -/
noncomputable def deTurckRHSSectionBg (g_bg g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2 where
  toSection := (deTurckRHSSection (I := I) g_bg g).toSection
  hasCompactSupport := (deTurckRHSSection (I := I) g_bg g).hasCompactSupport

@[simp] theorem deTurckRHSSectionBg_toSection
    (g_bg g : SmoothRiemannianMetric I M) :
    (deTurckRHSSectionBg (I := I) g_bg g).toSection =
      (deTurckRHSSection (I := I) g_bg g).toSection := rfl

/-- The model value of the re-tagged Ricci–DeTurck section recovers
`deTurckRicciRHS g_bg g` (transported from `deTurckRHSSection_toModel_apply`
through the `rfl`-identical underlying section). -/
theorem deTurckRHSSectionBg_toModel_apply
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((deTurckRHSSectionBg (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) :=
  deTurckRHSSection_toModel_apply (I := I) g_bg g x v

/-- **The extracted symmetric bilinear form of the Ricci–DeTurck section is the
Ricci–DeTurck right-hand side.**  Evaluating `ccTensorBilinSymm` on the smooth
tensor section `deTurckRHSSection g_bg g` (re-tagged to `g_bg`) reproduces
`deTurckRicciRHS g_bg g` pointwise: the model value of the section recovers
`deTurckRicciRHS` (`deTurckRHSSection_toModel_apply`), and the symmetrization is a
no-op since `deTurckRicciRHS` is symmetric (`deTurckRicciRHS_symm`). -/
theorem deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g_bg (deTurckRHSSectionBg (I := I) g_bg g) x v w =
      deTurckRicciRHS (I := I) g_bg g x v w := by
  rw [ccTensorBilinSymm_apply]
  rw [ccTensorBilin_apply, ccTensorBilin_apply]
  unfold ccTensorModel
  rw [ccTensorMultilinear_apply]
  rw [deTurckRHSSectionBg_toModel_apply, deTurckRHSSectionBg_toModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [deTurckRicciRHS_symm (I := I) g_bg g x w v]
  ring

end DifferentialGeometry.PDE.RicciFlow
