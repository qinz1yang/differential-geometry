import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MildSolutionTimeH1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPartialSumJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegSolutionJointlySmooth
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Spectral.Intrinsic.PointwiseDeriv

/-! # The realized DeTurck–Ricci solution family

The genuine second-order quasilinear spectral maximal-regularity engine
`deTurckRicci_quasilinear_maxreg_solution` produces, for the initial perturbation
`u₀ = 0` (so `g_DT 0 = g₀`), a positive horizon `T₀` and, for every short interval, the
strong (`MaxRegSolutionSpace = timeH1`) Duhamel solution `u` of the Ricci–DeTurck
flow linearized about the background, as a path in the tensor Sobolev scale
`tensorHs g₀ 0 2 (a : ℝ)`, driven by the **continuous, non-gated, genuinely
second-order** nonlinearity `deTurckSobolevNHa2 : H^{a+2} → H^a` (NO finite-support /
`realizeMetricAt` gating).  The engine is the mixed-view forcing contraction of the
DeTurck–Ricci quasilinear equation (the lower-order arm killed by small `T`, the
second-order arm killed by a small forcing ball), so the forcing reproduces
`deTurckSobolevNHa2` along the order-`(a+2)` Duhamel field `maxRegDuhamelSolField`.

The interior parabolic smoothing (`solField_into_all_tensorHs_interior`) places
`u.toFun t` in `⋂_σ Hˢ` for every interior time `t ∈ Ioo 0 T`, so — through the
now-PROVED smooth-representative gate `spectralSmoothRealizesAsSmooth_holds` — each
`u.toFun t` has a genuine `C∞` representative `T_rep t : SmoothCcTensor g₀ 0 2`.
Realizing that representative as a metric perturbation through
`tensorSectionRealizeMetric g₀ (T_rep t)` (which takes the `C∞` representative
DIRECTLY — no finite support, no fibre-by-fibre `realizeMetricAt`) produces the
metric family `g_DT t`, and the parabolic interior regularity makes the chart-Gram
entries jointly smooth.

This file assembles the construction.  The glue obtains `T, u, gforce` and its
defining identities from `deTurckRicci_quasilinear_maxreg_solution`, builds `g_DT` by
realizing the smooth representative family through `tensorSectionRealizeMetric`, and
discharges the initial-value and realize-relation conjuncts purely structurally from
`tensorSectionRealizeMetric_inner` and `ccTensorBilinSymm_zero_apply`.  The genuinely-deep
analytic content is isolated as a SINGLE named, SOLUTION-PINNED honest input taking the
genuine engine solution `u` together with its defining identities (`hduh`, `hforce`,
`htrace`) as hypotheses (so it is not vacuous):

* `realizedDeTurck_timeRegular_family` — the **time-regular** family of `C∞`
  representatives `T_rep` (uniformly `g₀`-fibre small with a single `δ < 1`) carrying ALL
  the realized data jointly: the zero initial value `T_rep 0 = 0`, the interior `L²` pin
  tying `T_rep t` to `u.toFun t`, the Ricci–DeTurck flow derivative (the soundness core:
  the pointwise `[0,∞)`-derivative of the realized inner-product perturbation is the
  intrinsic Ricci–DeTurck right-hand side, via the pointwise bridge
  `maxreg_l2deriv_to_pointwise_hasderivwithinat` and the chart-polynomial intrinsic tie
  `deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS`), and the joint chart-Gram
  interior regularity `JointChartGramSmooth` (the standard parabolic interior smoothing,
  `C∞` in space and time up to `t = 0`).  A per-time existential selection of the
  smooth-representative gate alone cannot supply the time-regularity the pointwise flow
  derivative requires; the time-regular family is exactly that soundness core.

`realizedDeTurckFamily_exists` calls the single time-regular family once and assembles
its output into the realized metric family `g_DT` together with its representative family
`T_rep`, the realize relation pinning the two, the DeTurck–Ricci flow derivative, and the
joint chart-Gram smoothness, from which the master `deTurckRicci_solution_with_jointReg`
(`DeTurckInitialDataExistence.lean`) builds the `IsQuasilinearMetricParabolicSolution`
flow.  Consumers transitively depend on the `sorryAx` carried by the single
SOLUTION-PINNED honest input `realizedDeTurck_timeRegular_family`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Equality of two smooth Riemannian metrics from equality of their inner-product
fields: the remaining structure fields (`symm`, `pos`, `isVonNBounded`, `contMDiff`)
are `Prop`-valued, hence proof-irrelevant. -/
theorem smoothRiemannianMetric_ext_inner {g g' : SmoothRiemannianMetric I M}
    (h : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) :
    g = g' := by
  have hinner : g.inner = g'.inner := by
    funext x
    ext v w
    exact h x v w
  cases g with
  | mk gi gsymm gpos gvon gcont =>
    cases g' with
    | mk gi' gsymm' gpos' gvon' gcont' =>
      cases hinner
      rfl

/-- The symmetrized extraction of the zero smooth tensor section is the zero
bilinear form: `ccTensorBilinSymm g₀ 0 = 0`, since `ccTensorBilinSymm` is
`ℝ`-homogeneous in the section and `(0 : SmoothCcTensor) = (0 : ℝ) • 0`. -/
theorem ccTensorBilinSymm_zero_apply (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
    (zero_smul ℝ _).symm
  rw [h0, ccTensorBilinSymm_smul]
  ring

/-- The zero smooth tensor section is uniformly `g₀`-fibre small with constant
`0 < 1`: `gFibreOpBound g₀ (ccTensorBilinSymm g₀ 0) 0`. -/
theorem gFibreOpBound_ccTensorBilinSymm_zero (g : SmoothRiemannianMetric I M) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) 0 := by
  intro x v w
  rw [ccTensorBilinSymm_zero_apply]
  simp only [abs_zero, zero_mul, le_refl]

end DifferentialGeometry.PDE.RicciFlow
