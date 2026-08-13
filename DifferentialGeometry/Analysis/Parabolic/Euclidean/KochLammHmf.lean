import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLinear
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammProduct

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {U G F H : Type*}
  [NormedAddCommGroup U]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem klHmf_split {T : ℝ} {A₀ A₂ Aₚ ε K : ℝ≥0}
    (A : ℝ × V → G →L[ℝ] H)
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (u : ℝ × V → U) (d : ℝ × V → G)
    (hA : ∀ z, ‖A z‖ ≤ (ε : ℝ))
    (hQ : ∀ z, ‖Q z‖ ≤ (K : ℝ))
    (hAmeas : AEStronglyMeasurable (fun z ↦ A z (d z))
      (klVolume : Measure (ℝ × V)))
    (hQmeas : AEStronglyMeasurable (fun z ↦ Q z (d z) (d z))
      (klVolume : Measure (ℝ × V)))
    (hd : KLPath T A₀ A₂ Aₚ u d) :
    KLSplit T (K * A₂ * A₂) (K * Aₚ * Aₚ) (ε * A₂) (ε * Aₚ)
      (fun z ↦ Q z (d z) (d z)) (fun z ↦ A z (d z)) := by
  refine ⟨?_, ?_⟩
  · apply klBilin_source Q d d hQ hQmeas
    · exact ⟨hd.grad_ae, hd.grad_l2, hd.grad_lp⟩
    · exact ⟨hd.grad_ae, hd.grad_l2, hd.grad_lp⟩
  · apply kl1_map_bound A d hA hAmeas
    exact ⟨hd.grad_ae, hd.grad_l2, hd.grad_lp⟩

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
