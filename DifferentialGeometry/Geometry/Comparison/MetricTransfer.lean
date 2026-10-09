import DifferentialGeometry.Geometry.Comparison.CanonicalGermAngle
import Mathlib.Topology.Maps.Basic

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem fourPointComparison_image_iff_of_dist_eq
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {κ : ℝ}
    {f : Y → X} {s : Set Y}
    (hdist : ∀ a ∈ s, ∀ b ∈ s, dist (f a) (f b) = dist a b) :
    fourPointComparison κ (f '' s) ↔ fourPointComparison κ s := by
  constructor
  · intro h x hx a ha b hb c hc hax hbx hcx
    have hne (y : Y) (hy : y ∈ s) (hyx : y ≠ x) : f y ≠ f x := by
      intro heq
      have hd := hdist y hy x hx
      rw [heq, dist_self] at hd
      exact hyx (dist_eq_zero.mp hd.symm)
    have ht := h (f x) ⟨x, hx, rfl⟩ (f a) ⟨a, ha, rfl⟩ (f b) ⟨b, hb, rfl⟩
      (f c) ⟨c, hc, rfl⟩ (hne a ha hax) (hne b hb hbx) (hne c hc hcx)
    simpa only [hdist x hx a ha, hdist x hx b hb, hdist x hx c hc,
      hdist a ha b hb, hdist b hb c hc, hdist c hc a ha] using ht
  · intro h x hx a ha b hb c hc hax hbx hcx
    rcases hx with ⟨x, hx, rfl⟩
    rcases ha with ⟨a, ha, rfl⟩
    rcases hb with ⟨b, hb, rfl⟩
    rcases hc with ⟨c, hc, rfl⟩
    have ht := h x hx a ha b hb c hc (fun heq => hax (congrArg f heq))
      (fun heq => hbx (congrArg f heq)) (fun heq => hcx (congrArg f heq))
    simpa only [hdist x hx a ha, hdist x hx b hb, hdist x hx c hc,
      hdist a ha b hb, hdist b hb c hc, hdist c hc a ha] using ht

theorem exists_local_fourPointComparison_image
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {κ : ℝ}
    {f : Y → X} (hf : IsOpenEmbedding f) {p : Y}
    (hlocal : ∃ Ω : Set Y, IsOpen Ω ∧ fourPointComparison κ Ω ∧ p ∈ Ω)
    (hmetric : ∃ r : ℝ, 0 < r ∧ ∀ a ∈ ball p r, ∀ b ∈ ball p r,
      dist (f a) (f b) = dist a b) :
    ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ f p ∈ Ω := by
  obtain ⟨Ω, hΩ, hcomp, hp⟩ := hlocal
  obtain ⟨r, hr, hdist⟩ := hmetric
  refine ⟨f '' (Ω ∩ ball p r), hf.isOpenMap _ (hΩ.inter isOpen_ball), ?_,
    ⟨p, ⟨hp, by simpa only [mem_ball, dist_self] using hr⟩, rfl⟩⟩
  apply (fourPointComparison_image_iff_of_dist_eq
    (fun a ha b hb => hdist a ha.2 b hb.2)).mpr
  exact hcomp.mono inter_subset_left

theorem germComparisonAngle_comp_of_eventually_dist_eq
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {κ : ℝ}
    {f : Y → X} {γ β : ℝ → Y}
    (hdist : ∀ᶠ z : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ),
      dist (f (γ z.1)) (f (β z.2)) = dist (γ z.1) (β z.2)) :
    germComparisonAngle κ (f ∘ γ) (f ∘ β) = germComparisonAngle κ γ β := by
  apply limsup_congr
  filter_upwards [hdist] with z hz
  simp only [Function.comp_def, hz]

theorem germComparisonAngle_comp_of_dist_eq_on
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {κ R S : ℝ}
    (hR : 0 < R) (hS : 0 < S) {f : Y → X} {γ β : ℝ → Y}
    (hdist : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (f (γ s)) (f (β t)) = dist (γ s) (β t)) :
    germComparisonAngle κ (f ∘ γ) (f ∘ β) = germComparisonAngle κ γ β := by
  apply germComparisonAngle_comp_of_eventually_dist_eq
  have heR : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioc (0 : ℝ) R := Ioc_mem_nhdsGT hR
  have heS : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc (0 : ℝ) S := Ioc_mem_nhdsGT hS
  filter_upwards [heR.prod_inl _, heS.prod_inr _] with z hs ht using hdist z.1 hs z.2 ht

end DifferentialGeometry.Geometry.Comparison.Toponogov
