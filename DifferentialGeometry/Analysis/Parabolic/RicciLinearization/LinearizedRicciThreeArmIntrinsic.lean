import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The intrinsic Lichnerowicz two-arm right-hand side
`appCc(linearizedRicciArm0Field)(∇⁰(T−T')) + appCc(linearizedRicciArm2FieldLichnerowicz)(∇²(T−T'))`,
as a `(0,2)`-tensor field. Defined once so that the deferred leaf and the headline share a
small elaborated conclusion term (avoids re-elaborating the large `appCc` / `iteratedCovGrad`
expression at each `sorry`). -/
noncomputable def linearizedRicciLichnerowiczTwoArmField
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 0 2 :=
  appCc (I := I) (M := M) g₀ 2 2
      (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
    + appCc (I := I) (M := M) g₀ 4 2
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))

set_option linter.unusedSectionVars false in

/-- The intrinsic two-arm Lichnerowicz right-hand side, evaluated by `unitModel`. -/
noncomputable def linearizedRicciLichnerowiczTwoArmValue
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (v : Fin 2 → TangentSpace I x) : ℝ :=
  unitModel (I := I) (M := M) g₀ 2
    (linearizedRicciLichnerowiczTwoArmField (I := I) g₀ T T' hδ hδ' s) x v

set_option linter.unusedSectionVars false in

/-- Intrinsic (chart-free) variation-of-Ricci-as-Lichnerowicz-operator.

Deferred leaf. This is the intrinsic characterization of the derivative of the Ricci tensor
of the realized metric path `s ↦ realizedFam g₀ T T' s` as the Lichnerowicz operator,
expressed entirely in `g₀`-inner / covariant-derivative language (no `chartSum`,
`chartSlope`, `extChartAt`, `chartRicciTrace` object).

Mathematically this is the standard identity `d/ds|_{s} Ric(g_s) = Ric'(g_s)(h_s)` with
`h_s = ∂_s g_s = (T − T')`, decomposed into its order-0 (curvature action) and order-2
(rough-Laplacian / trace-Hessian) arms via the intrinsic Palatini machinery
(`ricciTensor_sub_eq_connDiff_palatini`, `connDiffInner_g1_eq_half_covGradSymmS`,
`covDerivConnDiff_g1inner_eq_secondCovGrad_lowerArms`, the curvature-action lemmas). The
order-1 arm vanishes (Lichnerowicz collapse). Its intrinsic proof is the chart-free content
currently absent from the library; the chart representation of this same identity is
`chartSlopeContributions_eq_threeArm_component` (which carries the chart-route `sorry`).

The conclusion is stated through the abbreviation `linearizedRicciLichnerowiczTwoArmValue`
so the large `appCc` / `iteratedCovGrad` expression is elaborated once at its definition. -/
theorem linearizedRicciAt_eq_lichnerowicz_intrinsic_step
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v : Fin 2 → TangentSpace I x) :
    linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
      linearizedRicciLichnerowiczTwoArmValue (I := I) g₀ T T' hδ hδ' s x v := by
  sorry

set_option linter.unusedSectionVars false in

/-- Chart-free intrinsic two-arm identity for the linearized Ricci operator.

The linearized Ricci `linearizedRicciAt` — the derivative of the Ricci tensor of the
realized metric path `s ↦ realizedFam g₀ T T' s` — decomposes intrinsically (entirely in
`g₀`-inner / covariant-derivative language, with no chart, `extChartAt`, `chartSum` or
`chartSlope` object) into the Lichnerowicz two arms: the order-0 curvature arm
`appCc(linearizedRicciArm0Field)(∇⁰(T−T'))` and the order-2 principal / trace-Hessian arm
`appCc(linearizedRicciArm2FieldLichnerowicz)(∇²(T−T'))`. The order-1 arm vanishes
(Lichnerowicz collapse).

`#print axioms` transits only the `sorryAx` of the single deferred leaf
`linearizedRicciAt_eq_lichnerowicz_intrinsic_step` (the intrinsic
variation-of-Ricci-as-Lichnerowicz-operator, chart-free deep content not yet present in the
library); it does NOT transit the chart-route sorry
`chartSlopeContributions_eq_threeArm_component` nor any `chartSum` / `chartSlope` /
`extChartAt` declaration. -/
theorem linearizedRicciAt_eq_threeArm_intrinsic
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  change linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
    linearizedRicciLichnerowiczTwoArmValue (I := I) g₀ T T' hδ hδ' s x v
  exact linearizedRicciAt_eq_lichnerowicz_intrinsic_step (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    s hs x v

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
