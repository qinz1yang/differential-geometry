import DifferentialGeometry.Analysis.Integration.Lp.Lifting
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SliceWkp

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

theorem exists_lp_lift_of_weak_partials
    {Z E F : Type*} [MeasurableSpace Z]
    [NormedAddCommGroup E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure Z} {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {j : E → F} (hj : Continuous j) (hinj : Function.Injective j)
    (L : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] F) (A : ℝ)
    (hlift : ∀ f : Lp ℝ 2 (volume.restrict Ω), MemWkp 1 2 f Ω →
      ∃ e : E, j e = L f ∧ ‖e‖ ≤ A * (iteratedWeakSobolevNorm 1 2 f Ω).toReal)
    (P : Lp (Lp ℝ 2 (volume.restrict Ω)) 2 μ)
    (W : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => W i (t,z)) (P t : EuclideanSpace ℝ (Fin d) → ℝ) Ω) :
    ∃ v : Lp E 2 μ, (fun t => j (v t)) =ᵐ[μ] fun t => L (P t) := by
  obtain ⟨hP, hnorm⟩ := ae_memWkp_one_and_memLp_wkpNorm_of_lp_weak_partials hΩ P W hweak
  have hb : MemLp (fun t => A * (iteratedWeakSobolevNorm 1 2 (P t) Ω).toReal) 2 μ :=
    hnorm.const_mul A
  have hex : ∀ᵐ t ∂μ, ∃ e : E, j e = L (P t) ∧
      ‖e‖ ≤ A * (iteratedWeakSobolevNorm 1 2 (P t) Ω).toReal := by
    filter_upwards [hP] with t ht
    exact hlift (P t) ht
  obtain ⟨v, hv, _⟩ := MeasureTheory.exists_lp_lift_of_ae_exists_norm_le hj hinj
    (L.continuous.comp_aestronglyMeasurable (Lp.memLp P).1) hb hex
  exact ⟨v, hv⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean
