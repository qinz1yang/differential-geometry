import DifferentialGeometry.Analysis.Sobolev.Intrinsic.SmoothEntropyNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.PositiveApproximation

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M] [I.Boundaryless]


theorem exists_pos_wform_of_weak
    {g : SmoothRiemannianMetric I M} (hdim : 2 ≤ Module.finrank ℝ E)
    {u : M → ℝ} {G : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G)
    (hu : MemLp u 2 (riemannianVolumeMeasure I M g))
    (hGn : MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 2
      (riemannianVolumeMeasure I M g))
    (hmass : (∫ x, u x ^ 2 ∂riemannianVolumeMeasure I M g) = 1)
    {R : M → ℝ} (hR : Continuous R) {tau δ : ℝ} (htau : 0 ≤ tau) (hδ : 0 < δ) :
    ∃ w : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ w ∧ (∀ x, 0 < w x) ∧
      (∫ x, w x ^ 2 ∂riemannianVolumeMeasure I M g) = 1 ∧
      (∫ x, 4 * tau * g.inner x (gradFun g w x) (gradFun g w x) +
        tau * R x * w x ^ 2 - w x ^ 2 * Real.log (w x ^ 2)
        ∂riemannianVolumeMeasure I M g) ≤
      (∫ x, 4 * tau * g.inner x (G x) (G x) +
        tau * R x * u x ^ 2 - u x ^ 2 * Real.log (u x ^ 2)
        ∂riemannianVolumeMeasure I M g) + δ := by
  rcases isEmpty_or_nonempty M with hM | hM
  · let : IsEmpty M := hM
    simp only [integral_of_isEmpty, zero_ne_one] at hmass
  · let : Nonempty M := hM
    obtain ⟨v, hv, hvmass, hvW⟩ := hG.exists_smooth_normalized_wform_le
      hdim hu hGn hmass hR tau (half_pos hδ)
    have hvenergy := integrable_metric_energy_of_memLp g
      (Equivalence.memLp_g_norm_gradFun_smooth g 2 hv)
    obtain ⟨w, hw, hwpos, hwmass, hwW⟩ := exists_pos_wform g hv hvmass
      hvenergy hR (C := 0) htau (half_pos hδ)
    simp only [zero_mul, add_zero, Geometry.Connection.gradient_eq_gradFun] at hwW
    refine ⟨w, hw, hwpos, hwmass, ?_⟩
    linarith

end DifferentialGeometry.PDE.RicciFlow.Entropy
