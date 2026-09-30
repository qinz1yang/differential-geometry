import DifferentialGeometry.Geometry.Comparison.MultipleEndsSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.ProductBlowdownRecognition
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottCriterion

set_option autoImplicit false

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

variable {X C : Type*} [mX : MetricSpace X] [ProperSpace X] [MetricSpace C] [ProperSpace C]

theorem PointedGHConverges.exists_isometryEquiv_real_of_unbounded_components
    {p : X} {q : C} {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hlim : Tendsto c atTop (𝓝 0))
    (h : @PointedGHConverges (fun _ : ℕ => X)
      (fun n => mX.rescale (c n) (hc n)) C _ (fun _ => p) q)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {K : Set X} (hK : IsCompact K) {a b : X}
    (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b))
    (hab : connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) :
    ∃ e : C ≃ᵢ ℝ, e q = 0 := by
  obtain ⟨Y, mY, _, e, hcompact, _⟩ :=
    exists_isometryEquiv_real_prod_compact_of_unbounded_components hcomp hsegments hK ha hb hab
  let := mY
  let := hcompact
  exact h.exists_isometryEquiv_of_rescaled_normed_product hc hlim e isCompact_univ.isBounded

theorem exists_isometryEquiv_real_of_rescaled_approximations
    (p : X) (q : C)
    (happrox : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
      R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox X C
        (mX.rescale R⁻¹ (inv_pos.mpr hR)) _ p q δ))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {K : Set X} (hK : IsCompact K) {a b : X}
    (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b))
    (hab : connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) :
    ∃ e : C ≃ᵢ ℝ, e q = 0 := by
  let c (n : ℕ) := ((n : ℝ) + 1)⁻¹
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  have hc0 : Tendsto c atTop (𝓝 0) := by
    simpa [c, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h : @PointedGHConverges (fun _ : ℕ => X)
      (fun n => mX.rescale (c n) (hc n)) C _ (fun _ => p) q := by
    apply @PointedGHConverges.of_eventually_kleinerLott_approx
      (fun _ : ℕ => X) C (fun n => mX.rescale (c n) (hc n)) _ _ (fun _ => p) q
    intro δ hδ hδone
    obtain ⟨R₀, hR₀⟩ := happrox δ hδ hδone
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R₀)] with n hn
    exact hR₀ (n + 1) (by linarith) (by positivity)
  exact h.exists_isometryEquiv_real_of_unbounded_components hc hc0 hcomp hsegments hK ha hb hab

end GC.MetricGeometry
