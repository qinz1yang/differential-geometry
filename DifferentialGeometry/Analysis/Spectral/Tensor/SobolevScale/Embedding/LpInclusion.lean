import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion
import DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpMap
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section
open MeasureTheory Filter
open scoped Manifold ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem tensorHsPi_ae_eq_of_inclusion
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hca : c ≤ a) (hdb : d ≤ b)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure Ω}
    (Z : Lp (PiLp 2 (fun _ : ι => TensorHs g r s b)) p μ)
    (W : Ω → PiLp 2 (fun _ : ι => TensorHs g r s a)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hab)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hcd)
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hca)
    let U := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hdb)
    (fun t => P (Z t)) =ᵐ[μ] W →
    (fun t => Q ((U.compLpL p μ Z) t)) =ᵐ[μ] (fun t => L (W t)) := by
  intro P Q L U hZW
  filter_upwards [U.coeFn_compLpL Z, hZW] with t ht hpt
  rw [ht, ← hpt]
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
end
