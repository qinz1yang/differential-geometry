import DifferentialGeometry.Analysis.InnerProductSpace.RegularSimplexDirections
import DifferentialGeometry.Geometry.Comparison.ModelAngle

set_option autoImplicit false

noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace
namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_common_shortening_strut_of_dense_directions
    {X : Type*} {D : Type*} [MetricSpace X] {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (q : X) (ξ : D → {v : EuclideanSpace ℝ (Fin m) // ‖v‖ = 1})
    (γ : D → ℝ → X) (r : D → ℝ)
    (hr : ∀ d, 0 < r d)
    (hradial : ∀ d, ∀ s ∈ Ioc (0 : ℝ) (r d), dist q (γ d s) = s)
    (hdense : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ d, InnerProductGeometry.angle v (ξ d).val < ε)
    (hangle : ∀ d e, Tendsto
      (fun s : ℝ => comparisonAngleNegCurvature 1 s s (dist (γ d s) (γ e s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (InnerProductGeometry.angle (ξ d).val (ξ e).val)))
    {S : ℝ} (hS : 0 < S) :
    ∃ (d : Fin (m+1) → D) (s : ℝ), 0 < s ∧ s < S ∧
      (∀ i, s ≤ r (d i)) ∧
      (∀ i, dist q (γ (d i) s) = s) ∧
      (∀ i j, i ≠ j →
        Real.pi / 2 + 6 * (8 * (n : ℝ))⁻¹ <
          InnerProductGeometry.angle (ξ (d i)).val (ξ (d j)).val) ∧
      (∀ i j, i ≠ j →
        Real.pi / 2 + 5 * (8 * (n : ℝ))⁻¹ <
          comparisonAngleNegCurvature 1
            (dist q (γ (d i) s)) (dist q (γ (d j) s))
            (dist (γ (d i) s) (γ (d j) s))) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le hm hmn
  have hθ : 0 < (8 * (n : ℝ))⁻¹ := by positivity
  obtain ⟨v, hv, hi, hangle_v⟩ := EuclideanSpace.exists_regularSimplex hm
  choose d hd using fun i => hdense (v i) (hv i) _ hθ
  have hmargin (i j : Fin (m+1)) (hij : i ≠ j) :
      Real.pi / 2 + 6 * (8 * (n : ℝ))⁻¹ <
        InnerProductGeometry.angle (ξ (d i)).val (ξ (d j)).val := by
    have hsep := EuclideanSpace.regularSimplex_angle_margin hm hmn hij
    rw [EuclideanSpace.angle_regularSimplexVector hm hij, ← hangle_v i j hij] at hsep
    have h₁ := InnerProductGeometry.angle_le_angle_add_angle (v i) (ξ (d i)).val (v j)
    have h₂ := InnerProductGeometry.angle_le_angle_add_angle (ξ (d i)).val (ξ (d j)).val (v j)
    rw [InnerProductGeometry.angle_comm (ξ (d j)).val (v j)] at h₂
    linarith [hd i, hd j]
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i : Fin (m+1), s ≤ r (d i) := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [Ioc_mem_nhdsGT (hr (d i))] with s hs using hs.2
  have hcomp : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i j : Fin (m+1), i ≠ j →
      Real.pi / 2 + 5 * (8 * (n : ℝ))⁻¹ <
        comparisonAngleNegCurvature 1 s s (dist (γ (d i) s) (γ (d j) s)) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hij)
    · have hlt : Real.pi / 2 + 5 * (8 * (n : ℝ))⁻¹ <
          InnerProductGeometry.angle (ξ (d i)).val (ξ (d j)).val := by
        linarith [hmargin i j hij]
      filter_upwards [(hangle (d i) (d j)).eventually (eventually_gt_nhds hlt)] with s hs _ using hs
  have hall : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      0 < s ∧ s < S ∧ (∀ i : Fin (m+1), s ≤ r (d i)) ∧
      (∀ i j : Fin (m+1), i ≠ j → Real.pi / 2 + 5 * (8 * (n : ℝ))⁻¹ <
        comparisonAngleNegCurvature 1 s s (dist (γ (d i) s) (γ (d j) s))) := by
    filter_upwards [Ioo_mem_nhdsGT hS, hsmall, hcomp] with s hs hradius hang
    exact ⟨hs.1, hs.2, hradius, hang⟩
  obtain ⟨s, hs, hsS, hsr, hsa⟩ := hall.exists
  refine ⟨d, s, hs, hsS, hsr, ?_, hmargin, ?_⟩
  · intro i
    exact hradial (d i) s ⟨hs, hsr i⟩
  · intro i j hij
    rw [hradial (d i) s ⟨hs, hsr i⟩, hradial (d j) s ⟨hs, hsr j⟩]
    exact hsa i j hij

end DifferentialGeometry.Geometry.Comparison.Toponogov
