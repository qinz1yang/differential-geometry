import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Solution
import Mathlib.Topology.Order.IntermediateValue

namespace DifferentialGeometry.Analysis.ODE

theorem zero_eq_iff_of_hasDerivAt_mul_Ioo
    {a b : ℝ} {u κ : ℝ → ℝ} (hκ : ContinuousOn κ (Set.Ioo a b))
    (hu : ∀ t ∈ Set.Ioo a b, HasDerivAt u (κ t * u t) t)
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    u s = 0 ↔ u t = 0 := by
  let A : ℝ → (ℝ →L[ℝ] ℝ) := fun t => κ t • ContinuousLinearMap.id ℝ ℝ
  have hA : ContinuousOn A (Set.Ioo a b) := hκ.smul continuousOn_const
  have huA : ∀ t ∈ Set.Ioo a b, HasDerivAt u (A t (u t)) t := by
    intro t ht
    simpa only [A, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul] using hu t ht
  have hzA : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun _ : ℝ => (0 : ℝ))
      (A t 0) t := by
    intro t _
    simpa only [map_zero] using hasDerivAt_const t (0 : ℝ)
  constructor
  · intro hz
    exact Flow.linearODE_unique_on_Ioo hs hA huA hzA hz ht
  · intro hz
    exact Flow.linearODE_unique_on_Ioo ht hA huA hzA hz hs

theorem neg_iff_neg_of_hasDerivAt_mul_Ioo
    {a b : ℝ} {u κ : ℝ → ℝ} (hκ : ContinuousOn κ (Set.Ioo a b))
    (hu : ∀ t ∈ Set.Ioo a b, HasDerivAt u (κ t * u t) t)
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    u s < 0 ↔ u t < 0 := by
  have hc : ContinuousOn u (Set.Ioo a b) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hneg : ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, u s < 0 → u t < 0 := by
    intro s hs t ht hsu
    by_contra htu
    obtain ⟨z, hz, huz⟩ := isPreconnected_Ioo.intermediate_value hs ht hc
      ⟨hsu.le, le_of_not_gt htu⟩
    exact hsu.ne ((zero_eq_iff_of_hasDerivAt_mul_Ioo hκ hu hz hs).mp huz)
  exact ⟨hneg s hs t ht, hneg t ht s hs⟩

theorem nonpos_iff_nonpos_of_hasDerivAt_mul_Ioo
    {a b : ℝ} {u κ : ℝ → ℝ} (hκ : ContinuousOn κ (Set.Ioo a b))
    (hu : ∀ t ∈ Set.Ioo a b, HasDerivAt u (κ t * u t) t)
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    u s ≤ 0 ↔ u t ≤ 0 := by
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt]
  exact or_congr (zero_eq_iff_of_hasDerivAt_mul_Ioo hκ hu hs ht)
    (neg_iff_neg_of_hasDerivAt_mul_Ioo hκ hu hs ht)

end DifferentialGeometry.Analysis.ODE
