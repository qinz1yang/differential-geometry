import DifferentialGeometry.Analysis.ODE.Flow.Planar.NonvanishingPlanarFlow
import DifferentialGeometry.Topology.Flow.FirstReturn
import DifferentialGeometry.Topology.PlanarJordan.ReturnDisk

open Set

namespace Poincare.Analysis

theorem not_mem_transverse_segment_of_pos
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : Continuous v)
    (hnz : ∀ z, v z ≠ 0)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ s z) (v (φ t z)) t)
    (σ : ℝ →ᵃ[ℝ] ℂ) {ε a t : ℝ} (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ)
    (hsource : e.source = Ioo (-ε) ε ×ˢ Ioo (-ε) ε)
    (he : ∀ p, e p = φ p.2 (σ p.1)) (ha : a ∈ Ioo (-ε) ε) (ht : 0 < t) :
    φ t (σ a) ∉ σ '' Ioo (-ε) ε := by
  rintro ⟨b, hb, hbe⟩
  let r := max |a| |b|
  have hr : r < ε := max_lt (abs_lt.mpr ha) (abs_lt.mpr hb)
  have haK : a ∈ Icc (-r) r := abs_le.mp (le_max_left |a| |b|)
  have hbK : b ∈ Icc (-r) r := abs_le.mp (le_max_right |a| |b|)
  obtain ⟨T, hT, ⟨c, hc, hce⟩, havoid⟩ :=
    Poincare.Topology.Flow.exists_first_return_to_transverse_segment φ e hsource he hr haK
      ⟨t, ht, b, hbK, hbe⟩
  have hcε : c ∈ Ioo (-ε) ε := by constructor <;> linarith [hc.1, hc.2]
  have havoid' (s : ℝ) (hs : s ∈ Ioo 0 T) : φ s (σ a) ∉ σ '' uIcc a c := by
    intro hm
    apply havoid s hs
    apply image_mono (t := Icc (-r) r) ?_ hm
    intro u hu
    exact ⟨(le_min haK.1 hc.1).trans hu.1, hu.2.trans (max_le haK.2 hc.2)⟩
  obtain ⟨U, _, _, _, ⟨d⟩, hforward | hbackward⟩ :=
    Poincare.Topology.PlanarJordan.exists_trapped_disk_of_transverse_return
      φ σ e hsource he ha hcε hT hce.symm
      (injective_orbit_of_nonvanishing φ hv hnz hderiv (σ a)).injOn havoid'
  · obtain ⟨z, _, hz⟩ := exists_zero_of_forward_invariant_disk d φ hv.continuousOn
      hforward (fun z _ s _ ↦ (hderiv z s).hasDerivWithinAt)
    exact hnz z hz
  · have hrev (z : ℂ) (s : ℝ) :
        HasDerivAt (fun t ↦ φ.reverse t z) (-v (φ.reverse s z)) s := by
      simpa only [Function.comp_def, neg_one_smul, φ.reverse_apply] using
        (hderiv z (-s)).scomp s (hasDerivAt_neg s)
    obtain ⟨z, _, hz⟩ := exists_zero_of_forward_invariant_disk d φ.reverse
      (v := fun z ↦ -v z) hv.neg.continuousOn hbackward
      (fun z _ s _ ↦ (hrev z s).hasDerivWithinAt)
    exact hnz z (neg_eq_zero.mp hz)

end Poincare.Analysis
