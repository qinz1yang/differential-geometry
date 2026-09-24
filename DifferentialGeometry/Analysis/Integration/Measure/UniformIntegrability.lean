import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Regular

open Metric Set

namespace MeasureTheory

private theorem integral_norm_small_sets {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} {f : X → F}
    (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, MeasurableSet s → μ s ≤ ENNReal.ofReal δ →
      (∫ x in s, ‖f x‖ ∂μ) < ε := by
  obtain ⟨δ, hδ, hbound⟩ := (memLp_one_iff_integrable.2 hf).eLpNorm_indicator_le
    (by norm_num) (by norm_num) (half_pos hε)
  refine ⟨δ, hδ, fun s hs hμs => ?_⟩
  have h := hbound s hs hμs
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hf.integrableOn] at h
  exact (ENNReal.ofReal_le_ofReal_iff (half_pos hε).le).mp h |>.trans_lt (half_lt_self hε)

theorem IntegrableOn.exists_pos_integral_norm_closedBall_lt {X F : Type*} [NormedAddCommGroup X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup F]
    {μ : Measure X} [μ.IsAddLeftInvariant] [μ.OuterRegular] [NullSingletonClass μ]
    {s : Set X} {f : X → F} (hf : IntegrableOn f s μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ a : X, (∫ z in closedBall a r ∩ s, ‖f z‖ ∂μ) < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := integral_norm_small_sets hf hε
  obtain ⟨U, hU0, hUopen, hUmeasure⟩ :=
    ({0} : Set X).exists_isOpen_lt_of_lt (μ := μ) (ENNReal.ofReal δ)
      (by simpa only [measure_singleton] using ENNReal.ofReal_pos.2 hδ)
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hUopen 0 (hU0 (mem_singleton 0))
  refine ⟨R / 2, half_pos hR, fun a => ?_⟩
  have hshift : μ (closedBall a (R / 2)) = μ (closedBall (0 : X) (R / 2)) := by
    have heq : closedBall (0 : X) (R / 2) = (a + ·) ⁻¹' closedBall a (R / 2) := by
      simp [preimage_add_closedBall]
    rw [heq, measure_preimage_add]
  have hbound : μ (closedBall a (R / 2)) ≤ ENNReal.ofReal δ := by
    rw [hshift]
    exact (measure_mono ((closedBall_subset_ball (half_lt_self hR)).trans hRU)).trans
      hUmeasure.le
  have h := hsmall (closedBall a (R / 2)) measurableSet_closedBall
    ((Measure.restrict_apply_le _ _).trans hbound)
  simpa only [Measure.restrict_restrict measurableSet_closedBall] using h

end MeasureTheory
