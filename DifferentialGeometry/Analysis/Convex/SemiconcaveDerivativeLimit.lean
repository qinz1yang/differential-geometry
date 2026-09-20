import DifferentialGeometry.Analysis.Convex.DerivativeLimit

noncomputable section

namespace DifferentialGeometry.Analysis

open Filter Set
open scoped _root_.Topology

theorem tendsto_deriv_of_concaveOn_sub
    {ι : Type*} {L : Filter ι} {D : Set ℝ}
    {F : ι → ℝ → ℝ} {f q : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ interior D)
    (hconcave : ∀ᶠ i in L, ConcaveOn ℝ D (fun r ↦ F i r - q r))
    (hF : ∀ᶠ i in L, DifferentiableAt ℝ (F i) x)
    (hlim : ∀ y ∈ D, Tendsto (fun i ↦ F i y) L (𝓝 (f y)))
    (hf : DifferentiableAt ℝ f x) (hq : DifferentiableAt ℝ q x) :
    Tendsto (fun i ↦ deriv (F i) x) L (𝓝 (deriv f x)) := by
  have hFq : ∀ᶠ i in L, DifferentiableAt ℝ (fun r ↦ F i r - q r) x := by
    filter_upwards [hF] with i hi
    exact hi.sub hq
  have hlimq : ∀ y ∈ D,
      Tendsto (fun i ↦ F i y - q y) L (𝓝 (f y - q y)) :=
    fun y hy ↦ (hlim y hy).sub_const (q y)
  have h := tendsto_deriv_of_concaveOn hx hconcave hFq hlimq (hf.sub hq)
  have heq : (fun i ↦ deriv (fun r ↦ F i r - q r) x + deriv q x) =ᶠ[L]
      (fun i ↦ deriv (F i) x) := by
    filter_upwards [hF] with i hi
    change deriv (F i - q) x + deriv q x = deriv (F i) x
    rw [deriv_sub hi hq, sub_add_cancel]
  have hsum := (h.add_const (deriv q x)).congr' heq
  change Tendsto (fun i ↦ deriv (F i) x) L (𝓝 (deriv (f - q) x + deriv q x)) at hsum
  simpa only [deriv_sub hf hq, sub_add_cancel] using hsum

end DifferentialGeometry.Analysis
