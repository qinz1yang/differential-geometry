import DifferentialGeometry.Geometry.Metric.RetainedMarkerRadii
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false
noncomputable section
open Set Metric
namespace GC.MetricGeometry

theorem original_packet_marker_scale_binding
    {M H I : Type*} [MetricSpace M]
    (f : M → H) (ρ : M → ℝ) {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    (center : I → M) (D : I → ℝ) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (hD : ∀ i, D i = 200 ∨ D i = 100 * Δ ∨ D i = 1000000 * Δ)
    (hsmall : (Λ : ℝ) * (1000000 * Δ) ≤ 1 / 4)
    (hpos : ∀ i, 0 < ρ (center i))
    (ζ : ∀ i, ball (center i) (D i * ρ (center i)) → ℝ)
    (marker : I → H → ℝ)
    (hmarker : ∀ i p, marker i (f p) = ρ (center i) *
      (Subtype.val : ball (center i) (D i * ρ (center i)) → M).extend (ζ i) 0 p)
    (core : I → Set M)
    (hcore : ∀ i, core i ⊆ ball (center i) (D i * ρ (center i)))
    (hplateau : ∀ i p (hp : p ∈ core i), ζ i ⟨p, hcore i hp⟩ = 1)
    (cloud : Set M) (hcover : ∀ p ∈ cloud, ∃ i, p ∈ core i) :
    (∀ i p, 0 < marker i (f p) →
      3 * ρ (center i) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (center i) / 4) ∧
    (∀ p ∈ cloud, ∃ i, marker i (f p) = ρ (center i)) ∧
    (∀ p ∈ cloud, ∀ q, f p = f q →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p) := by
  classical
  have hbound (i : I) : D i ≤ 1000000 * Δ := by
    rcases hD i with hi | hi | hi <;> rw [hi] <;> linarith
  have hs : ∀ i p, 0 < marker i (f p) →
      3 * ρ (center i) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (center i) / 4 := by
    intro i p hp
    have hn : (Subtype.val : ball (center i) (D i * ρ (center i)) → M).extend (ζ i) 0 p ≠ 0 := by
      intro hz
      rw [hmarker i p, hz, mul_zero] at hp
      exact (lt_irrefl 0) hp
    obtain ⟨u, _, hu⟩ := Function.support_extend_zero_subset hn
    have hpball : p ∈ ball (center i) (D i * ρ (center i)) := by
      rw [← hu]
      exact u.property
    apply scale_bounds_on_closedBall hρ (hpos i) hsmall
    exact hpball.le.trans (mul_le_mul_of_nonneg_right (hbound i) (hpos i).le)
  have hf : ∀ p ∈ cloud, ∃ i, marker i (f p) = ρ (center i) := by
    intro p hp
    obtain ⟨i, hi⟩ := hcover p hp
    refine ⟨i, ?_⟩
    rw [hmarker i p]
    have he := Function.Injective.extend_apply (Subtype.val_injective)
      (ζ i) (0 : M → ℝ) (⟨p, hcore i hi⟩ : ball (center i) (D i * ρ (center i)))
    change (Subtype.val : ball (center i) (D i * ρ (center i)) → M).extend (ζ i) 0 p = ζ i ⟨p, hcore i hi⟩ at he
    rw [he, hplateau i p hi, mul_one]
  refine ⟨hs, hf, ?_⟩
  intro p hp q heq
  obtain ⟨i, hi⟩ := hf p hp
  exact (scale_comparison_of_retained_marker f ρ marker (fun i => ρ (center i))
    hpos hs heq i hi).2

theorem original_packet_closed_support_scale_bounds
    {M : Type*} [MetricSpace M] (ρ : M → ℝ) {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (center : M) {D : ℝ}
    (hpos : 0 < ρ center) (hsmall : (Λ : ℝ) * D ≤ 1 / 4)
    (ζ : ball center (D * ρ center) → ℝ) :
    ∀ p ∈ tsupport ((Subtype.val : ball center (D * ρ center) → M).extend ζ 0),
      3 * ρ center / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ center / 4 := by
  have hs : tsupport ((Subtype.val : ball center (D * ρ center) → M).extend ζ 0) ⊆
      closedBall center (D * ρ center) := by
    apply closure_minimal _ isClosed_closedBall
    intro p hp
    obtain ⟨u, _, hu⟩ := Function.support_extend_zero_subset hp
    rw [← hu]
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp u.property).le
  intro p hp
  exact scale_bounds_on_closedBall hρ hpos hsmall (hs hp)

theorem original_small_packet_block_zero
    {M V : Type*} [MetricSpace M] [AddCommGroup V] [Module ℝ V]
    (ρ : M → ℝ) {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    (a i p : M) {Da Di : ℝ} (ha : 0 < ρ a) (hi : 0 < ρ i)
    (hDa : (Λ : ℝ) * Da ≤ 1 / 4) (hDi : (Λ : ℝ) * Di ≤ 1 / 4)
    (hp : p ∈ ball a (Da * ρ a)) (hprune : ρ i ≤ ρ a / 2)
    (ζ : ball i (Di * ρ i) → ℝ) (v : V) :
    let cutoff := (Subtype.val : ball i (Di * ρ i) → M).extend ζ 0 p
    cutoff = 0 ∧ cutoff • v = 0 := by
  have hscalea := scale_bounds_on_closedBall hρ ha hDa (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp).le)
  have hz : (Subtype.val : ball i (Di * ρ i) → M).extend ζ 0 p = 0 := by
    by_contra hn
    obtain ⟨u, _, hu⟩ := Function.support_extend_zero_subset hn
    have hpball : p ∈ ball i (Di * ρ i) := by rw [← hu]; exact u.property
    have hscalei := scale_bounds_on_closedBall hρ hi hDi (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hpball).le)
    linarith
  exact ⟨hz, by rw [hz, zero_smul]⟩

end GC.MetricGeometry
