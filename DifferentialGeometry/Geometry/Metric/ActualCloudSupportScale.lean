import DifferentialGeometry.Geometry.Metric.OriginalPacketScaleBindings
import DifferentialGeometry.Geometry.Metric.RetainedMarkerLocality

/-! CFS26 (master207B, B:3582): the support-scale bounds (AS) hold for EVERY preimage of an image point with a
positive marker, and every point of the original cores has a full constant marker. Consequently CFS07 applies to
ALL preimage choices in the actual cloud, and every selection of preimages gives the large-scale control (MCb)
`r x / (5/3) ≤ r y ≤ (5/3) r x` that the CFS14 kernel requires at its own buffer `L` (e.g. `L = 128 ε⁻¹`). -/

set_option autoImplicit false
noncomputable section
open Set Metric

namespace GC.MetricGeometry

/-- CFS26 + CFS07 on the actual packets: comparison for every pair of cloud preimages and the (MCb) form for every
selection of preimages over the image of the cloud. -/
theorem actualCloud_support_scale_all_preimages
    {M H I : Type*} [MetricSpace M] [PseudoMetricSpace H]
    (f : M → H) (ρ : M → ℝ) {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    (center : I → M) (D : I → ℝ) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (hD : ∀ i, D i = 200 ∨ D i = 100 * Δ ∨ D i = 1000000 * Δ)
    (hsmall : (Λ : ℝ) * (1000000 * Δ) ≤ 1 / 4)
    (hpos : ∀ i, 0 < ρ (center i))
    (ζ : ∀ i, ball (center i) (D i * ρ (center i)) → ℝ)
    (marker : I → H → ℝ) (hmarkerLip : ∀ i, LipschitzWith 1 (marker i))
    (hmarker : ∀ i p, marker i (f p) = ρ (center i) *
      (Subtype.val : ball (center i) (D i * ρ (center i)) → M).extend (ζ i) 0 p)
    (core : I → Set M)
    (hcore : ∀ i, core i ⊆ ball (center i) (D i * ρ (center i)))
    (hplateau : ∀ i p (hp : p ∈ core i), ζ i ⟨p, hcore i hp⟩ = 1)
    (cloud : Set M) (hcover : ∀ p ∈ cloud, ∃ i, p ∈ core i)
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) (hLσ : L * σ ≤ 1 / 5) :
    (∀ p ∈ cloud, ∀ q ∈ cloud, dist (f p) (f q) ≤ L * max (σ * ρ p) (σ * ρ q) →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p) ∧
    ∀ select : H → M, (∀ x ∈ f '' cloud, select x ∈ cloud ∧ f (select x) = x) →
      ∀ x ∈ f '' cloud, ∀ y ∈ f '' cloud,
        dist y x ≤ L * max (σ * ρ (select y)) (σ * ρ (select x)) →
        σ * ρ (select x) / (5 / 3) ≤ σ * ρ (select y) ∧
          σ * ρ (select y) ≤ (5 / 3) * (σ * ρ (select x)) := by
  obtain ⟨hs, hf, -⟩ := original_packet_marker_scale_binding f ρ hρ center D Δ hΔ hD hsmall hpos ζ
    marker hmarker core hcore hplateau cloud hcover
  have hpair : ∀ p ∈ cloud, ∀ q ∈ cloud, dist (f p) (f q) ≤ L * max (σ * ρ p) (σ * ρ q) →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
    intro p hp q hq hd
    exact nearby_scale_comparison_of_retained_markers (P := cloud)
      (fun z => f (z : M)) (fun z => ρ (z : M)) marker (fun i => ρ (center i)) hpos hmarkerLip
      (fun z => hf z z.property) (fun i z hz => hs i z hz) hσ hL hLσ ⟨p, hp⟩ ⟨q, hq⟩ hd
  refine ⟨hpair, ?_⟩
  intro select hselect x hx y hy hd
  obtain ⟨hxc, hxf⟩ := hselect x hx
  obtain ⟨hyc, hyf⟩ := hselect y hy
  have hc := hpair (select x) hxc (select y) hyc (by
    rw [hxf, hyf, dist_comm, max_comm]
    exact hd)
  have hlo := mul_le_mul_of_nonneg_left hc.1 hσ
  have hup := mul_le_mul_of_nonneg_left hc.2 hσ
  constructor <;> nlinarith

end GC.MetricGeometry
