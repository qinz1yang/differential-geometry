import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import DifferentialGeometry.Topology.UniformConvergence

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

open Filter Set MeasureTheory
open scoped Topology

theorem exists_tendstoUniformlyOn_left_endpoint_of_integrable_deriv_bound
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a < b) {U : Set X} (f d : ℝ → X → F) (B : ℝ → ℝ)
    (hderiv : ∀ t ∈ Ioo a b, ∀ x ∈ U, HasDerivAt (fun s => f s x) (d t x) t)
    (hbound : ∀ t ∈ Ioo a b, ∀ x ∈ U, ‖d t x‖ ≤ B t)
    (hint : IntervalIntegrable B volume a b) :
    ∃ g : X → F, TendstoUniformlyOn f g (𝓝[Ioo a b] a) U := by
  let m : ℝ → ℝ := fun t => ∫ r in a..t, B r
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have hmem : ∀ t ∈ Ioo a b, t ∈ uIcc a b := by
    intro t ht
    rw [uIcc_of_le hab.le]
    exact ⟨ht.1.le, ht.2.le⟩
  have hm : Tendsto m (𝓝[Ioo a b] a) (𝓝 0) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval' hint ha) a ha
    have hl := hc.mono (fun t ht => hmem t ht)
    simpa only [intervalIntegral.integral_same] using hl.tendsto
  apply exists_tendstoUniformlyOn_left_endpoint_of_time_modulus hab f m hm
  have hordered : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, s ≤ t → ∀ x ∈ U,
      dist (f t x) (f s x) ≤ |m t - m s| := by
    intro s hs t ht hst x hx
    have hsub : Icc s t ⊆ Ioo a b := by
      intro r hr
      exact ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
    have hd : ∀ r ∈ Icc s t, HasDerivAt (fun v => f v x) (d r x) r :=
      fun r hr => hderiv r (hsub hr) x hx
    have hc : ContinuousOn (fun r => f r x) (Icc s t) :=
      fun r hr => (hd r hr).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun r => f r x) (Ioo s t) :=
      fun r hr => (hd r ⟨hr.1.le, hr.2.le⟩).differentiableAt.differentiableWithinAt
    have hb : ∀ᵐ r, r ∈ Ioo s t → ‖deriv (fun v => f v x) r‖ ≤ B r := by
      exact Eventually.of_forall fun r hr => by
        rw [(hd r ⟨hr.1.le, hr.2.le⟩).deriv]
        exact hbound r (hsub ⟨hr.1.le, hr.2.le⟩) x hx
    have hist := hint.mono_set (uIcc_subset_uIcc (hmem s hs) (hmem t ht))
    have hib : ∀ r ∈ Ioo a b, IntervalIntegrable B volume a r :=
      fun r hr => hint.mono_set (uIcc_subset_uIcc ha (hmem r hr))
    have hi := norm_sub_le_integral_of_norm_deriv_le_of_le hst hc hdiff hb hist
    calc
      dist (f t x) (f s x) = ‖f t x - f s x‖ := dist_eq_norm _ _
      _ ≤ ∫ r in s..t, B r := hi
      _ = m t - m s := (intervalIntegral.integral_interval_sub_left (hib t ht) (hib s hs)).symm
      _ ≤ |m t - m s| := le_abs_self _
  intro s hs t ht x hx
  rcases le_total s t with hst | hts
  · simpa only [dist_comm, abs_sub_comm] using hordered s hs t ht hst x hx
  · exact hordered t ht s hs hts x hx

end DifferentialGeometry.Analysis
