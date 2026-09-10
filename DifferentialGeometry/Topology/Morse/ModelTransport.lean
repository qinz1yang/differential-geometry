import DifferentialGeometry.Topology.Morse.InteriorRestriction
import DifferentialGeometry.Topology.Manifold.MFDeriv.ModelTransport
import DifferentialGeometry.Topology.Morse.HessianNaturality
import Mathlib.LinearAlgebra.QuadraticForm.Signature

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace Poincare.Morse
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  (e : E ≃L[ℝ] F)


theorem isCriticalPointAt_transContinuousLinearEquiv_iff {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x) :
    IsCriticalPointAt (I.transContinuousLinearEquiv e) f x ↔ IsCriticalPointAt I f x := by
  change (show F →L[ℝ] ℝ from mfderiv (I.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ) f x) = 0 ↔
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) = 0
  erw [Poincare.Manifold.mfderiv_transContinuousLinearEquiv I e hf hx]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := e.symm.surjective v
    exact DFunLike.congr_fun h w
  · intro h
    rw [h, ContinuousLinearMap.zero_comp]


theorem chartHessianAt_transContinuousLinearEquiv {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x)
    (hc : IsCriticalPointAt I f x) :
    chartHessianAt (fun y => f ((extChartAt (I.transContinuousLinearEquiv e) x).symm y))
      (extChartAt (I.transContinuousLinearEquiv e) x x) =
      (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)).comp
        e.symm.toLinearEquiv.toLinearMap := by
  let g : E → ℝ := fun y => f ((extChartAt I x).symm y)
  let z := extChartAt I x x
  have hg : ContDiffAt ℝ 2 g (e.symm (e z)) := by
    simpa only [e.symm_apply_apply] using
      (Poincare.Manifold.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint I hf hx).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hz : fderiv ℝ g (e.symm (e z)) = 0 := by
    rw [e.symm_apply_apply]
    have hd := Poincare.Manifold.mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint
      I (hf.mdifferentiableAt (by simp)) hx
    exact hd.symm.trans hc
  have hd := fderiv_fderiv_comp_at_critical hg e.symm.contDiff.contDiffAt hz
  ext v
  change (fderiv ℝ (fderiv ℝ (g ∘ e.symm)) (e z)) v v =
    (fderiv ℝ (fderiv ℝ g) z) (e.symm v) (e.symm v)
  rw [hd, e.symm.fderiv, e.symm_apply_apply]
  rfl


theorem chartHessianAt_equivalent_transContinuousLinearEquiv {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x)
    (hc : IsCriticalPointAt I f x) :
    (chartHessianAt (fun y => f ((extChartAt (I.transContinuousLinearEquiv e) x).symm y))
      (extChartAt (I.transContinuousLinearEquiv e) x x)).Equivalent
      (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)) := by
  rw [chartHessianAt_transContinuousLinearEquiv I e hf hx hc]
  exact ⟨(QuadraticMap.isometryEquivOfCompLinearEquiv _ e.symm.toLinearEquiv).symm⟩


theorem sigNeg_chartHessianAt_transContinuousLinearEquiv {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x)
    (hc : IsCriticalPointAt I f x) :
    sigNeg (chartHessianAt (fun y => f ((extChartAt (I.transContinuousLinearEquiv e) x).symm y))
      (extChartAt (I.transContinuousLinearEquiv e) x x)) =
      sigNeg (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)) :=
  (chartHessianAt_equivalent_transContinuousLinearEquiv I e hf hx hc).sigNeg_eq


theorem isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x) :
    IsNondegenerateCriticalPointAt (I.transContinuousLinearEquiv e) f x ↔
      IsNondegenerateCriticalPointAt I f x := by
  unfold IsNondegenerateCriticalPointAt
  rw [isCriticalPointAt_transContinuousLinearEquiv_iff I e hf hx]
  by_cases hc : IsCriticalPointAt I f x
  · simp only [hc, true_and]
    rw [chartHessianAt_transContinuousLinearEquiv I e hf hx hc, QuadraticMap.associated_comp]
    convert! LinearMap.separatingLeft_congr_iff
      (B := QuadraticMap.associated (R := ℝ)
        (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)))
      e.toLinearEquiv e.toLinearEquiv using 1
  · simp only [hc, false_and]
end Poincare.Morse
