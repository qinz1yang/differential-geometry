import DifferentialGeometry.Analysis.Sobolev.MetricTarget.WeakCompactness
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation

section

set_option autoImplicit false
noncomputable section

open Filter Set MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_weakGrad_sq_le_liminf_comp_fderiv_on_subset
    {X : Type*} [TopologicalSpace X] {Ω Ω₀ : Set E}
    [IsFiniteMeasure (volume.restrict Ω)] (hΩ : IsOpen Ω) (hsub : Ω ⊆ Ω₀)
    {P : X → ℝ} (hP : Continuous P) {D : ℝ} (hD : ∀ p, ‖P p‖ ≤ D)
    (U : ℕ → E → X) (v : E → X)
    (hLip : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (P ∘ U n))
    (hae : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => U n x) atTop (𝓝 (v x)))
    {B : ℝ} (hB : ∀ n, (∫ x in Ω, ‖fderiv ℝ (P ∘ U n) x‖ ^ 2) ≤ B)
    (hw : DeGiorgi.MemW1pWitness 2 (P ∘ v) Ω₀) :
    (∫ x in Ω, ‖hw.weakGrad x‖ ^ 2) ≤
      liminf (fun n => ∫ x in Ω, ‖fderiv ℝ (P ∘ U n) x‖ ^ 2) atTop := by
  obtain ⟨_, _, hv, _, _, _, _, _, henergy⟩ :=
    exists_memW1pWitness_comp_of_ae_tendsto_of_lipschitz hP hD U v hLip hae hB
  have heq := (DeGiorgi.MemW1pWitness.restrict hΩ hsub hw).ae_eq hΩ hv
  have hint : (∫ x in Ω, ‖hw.weakGrad x‖ ^ 2) = ∫ x in Ω, ‖hv.weakGrad x‖ ^ 2 :=
    integral_congr_ae (heq.mono fun x hx => congrArg (fun z : E => ‖z‖ ^ 2) hx)
  exact hint.trans_le henergy

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
