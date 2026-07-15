import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartGramRealizeDiffJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.IteratedCovGradChartJetPeel

/-!
# The chart-component Euclidean coordinate bridge: `EuclN`-jets versus `E`-jets

The forward covariant Faà-di-Bruno peel (`IteratedCovGradChartJetPeel`) lives in the
`toEuclidean`-image `EuclN` (plain Fréchet jets of `rawPullR`), while the chart-Gram / Ricci–DeTurck
tower bounds (`ChartGramRealizeDiffJet`, `ChartDeTurckRicciRHSRealizeJet`) live in the raw chart
target `E` (`iteratedFDerivWithin` jets of `rawCompOnE` on the chart-target interior).  The two
families of chart components are related by the canonical continuous-linear equivalence
`toEuclidean : E ≃L[ℝ] EuclN`:

`rawPullR g 0 2 S α ![] Jdx = rawCompOnE g S α Jdx ∘ toEuclidean.symm` (as functions on `EuclN`).

This file proves the **chart-component Euclidean coordinate bridge**: on the partition-of-unity
kernel, the order-`m` plain `EuclN` Fréchet jet of `rawPullR` is bounded by `‖toEuclidean.symm‖^m`
times the order-`m` `iteratedFDerivWithin` jet of `rawCompOnE` (within the chart-target interior),
at the corresponding chart-preimage point.  Summed and supremised over the jet window, this yields a
single uniform bound of the `EuclN` bare chart-jet content by the `E` bare chart-jet content.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

open Manifold Set Filter Topology
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The plain `EuclN` raw chart component `rawPullR g 0 2 S α ![] Jdx` equals the `E`-coordinate raw
chart component `rawCompOnE g S α Jdx` precomposed with the continuous-linear equivalence
`toEuclidean.symm : EuclN → E`. -/
lemma rawPullR_eq_rawCompOnE_comp (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx =
      rawCompOnE (I := I) (M := M) g S α Jdx ∘ (toEuclidean (E := E)).symm := by
  funext y
  rw [rawPullR, Function.comp_apply, Function.comp_apply, Function.comp_apply, rawCompOnE]

/-- **The chart-component Euclidean coordinate bridge (pointwise order-`m` jet).**
For `S : SmoothCcTensor g 0 2`, chart `α`, target multi-index `Jdx`, order `m`, and a point `y`
of `EuclN` whose `toEuclidean.symm`-image lies in the chart-target interior, the order-`m` plain
Fréchet jet of `rawPullR` is bounded by `‖toEuclidean.symm‖^m` times the order-`m`
`iteratedFDerivWithin` jet of `rawCompOnE` at the corresponding `E`-point. -/
lemma norm_iteratedFDeriv_rawPullR_le_iteratedFDerivWithin_rawCompOnE
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) y‖ ≤
      ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ ^ m *
        ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g S α Jdx)
          (interior (extChartAt I α).target) ((toEuclidean (E := E)).symm y)‖ := by
  classical
  set e : EuclN ≃L[ℝ] E := (toEuclidean (E := E)).symm with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hUD : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn

  rw [rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx]

  have hpre_open : IsOpen (e ⁻¹' O) := hO_open.preimage e.continuous
  have hy_pre : y ∈ e ⁻¹' O := hy

  have hplain : iteratedFDeriv ℝ m (rawCompOnE (I := I) (M := M) g S α Jdx ∘ ⇑e) y =
      iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g S α Jdx ∘ ⇑e) (e ⁻¹' O) y :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := rawCompOnE (I := I) (M := M) g S α Jdx ∘ ⇑e) m hpre_open hy_pre).symm
  rw [hplain]

  have hcomp := e.iteratedFDerivWithin_comp_right (f := rawCompOnE (I := I) (M := M) g S α Jdx)
    hUD (x := y) hy m
  rw [hcomp]

  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

  have he_norm : ‖(e : EuclN →L[ℝ] E)‖ = ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ := rfl
  rw [he_norm, mul_comm]

end DifferentialGeometry.PDE.RicciFlow
