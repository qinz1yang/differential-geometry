import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {T a b : ℝ}

private theorem shift_preserving (a b : ℝ) :
    MeasurePreserving (fun t : ℝ => t + a) (timeMeasure (b - a))
      (volume.restrict (Icc a b)) := by
  have h := (measurePreserving_add_right volume a).restrict_image_emb
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (b - a))
  simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel] using h

namespace timeL2

def slice (f : timeL2 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    timeL2 X (b - a) := by
  have hset : Icc a b ⊆ Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨ha.trans ht.1, ht.2.trans hbT⟩
  have hle : volume.restrict (Icc a b) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hset le_rfl
  have hf : MemLp (fun t : ℝ => f t) 2 (volume.restrict (Icc a b)) :=
    (Lp.memLp f).mono_measure hle
  exact (hf.comp_measurePreserving (shift_preserving a b)).toLp (fun t => f (t + a))

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem slice_coe (f : timeL2 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    slice f a b ha hbT =ᵐ[timeMeasure (b - a)] fun t => f (t + a) := by
  unfold slice
  exact MemLp.coeFn_toLp _

end timeL2

namespace timeH1

def slice (u : timeH1 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    timeH1 X (b - a) :=
  mk (u.toFun a) (timeL2.slice u.deriv a b ha hbT)

omit [CompleteSpace X] in
theorem slice_deriv (u : timeH1 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    (slice u a b ha hbT).deriv =ᵐ[timeMeasure (b - a)] fun t => u.deriv (a + t) := by
  filter_upwards [timeL2.slice_coe u.deriv a b ha hbT] with t ht
  simpa only [slice, deriv_mk, add_comm] using ht

omit [CompleteSpace X] in
theorem slice_toFun (u : timeH1 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (b - a)) :
    (slice u a b ha hbT).toFun t = u.toFun (a + t) := by
  have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) (b - a) := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    exact ⟨le_of_lt hs.1, hs.2.trans ht.2⟩
  have hrestr :
      (fun s : ℝ => (timeL2.slice u.deriv a b ha hbT) s)
        =ᵐ[volume.restrict (uIoc (0 : ℝ) t)] fun s => u.deriv (s + a) :=
    (timeL2.slice_coe u.deriv a b ha hbT).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hint :
      (∫ s in (0 : ℝ)..t, (timeL2.slice u.deriv a b ha hbT) s)
        = ∫ s in (0 : ℝ)..t, u.deriv (s + a) :=
    intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict hrestr)
  have haT : a ≤ T := by linarith [ht.1, ht.2]
  have hat_mem : t + a ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2]
  have hdiff := u.toFun_sub_toFun (t₀ := a) (t₁ := t + a) ⟨ha, haT⟩ hat_mem
  change u.toFun a + ∫ s in (0 : ℝ)..t, (timeL2.slice u.deriv a b ha hbT) s = _
  rw [hint]
  rw [intervalIntegral.integral_comp_add_right]
  simp only [zero_add]
  rw [← hdiff]
  abel_nf

end timeH1

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
