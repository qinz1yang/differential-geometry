import DifferentialGeometry.Analysis.ODE.Flow.Planar.InvariantDiskFlow
import DifferentialGeometry.Topology.PlanarJordan.InvariantDisk

open Set

namespace Poincare.Analysis

theorem injective_orbit_of_nonvanishing
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : Continuous v)
    (hnz : ∀ x, v x ≠ 0)
    (hderiv : ∀ x t, HasDerivAt (fun s ↦ φ s x) (v (φ t x)) t)
    (x : ℂ) : Function.Injective (fun t ↦ φ t x) := by
  have hnon : ∃ s : ℝ, φ s x ≠ x := by
    by_contra h
    push Not at h
    have hd : HasDerivAt (fun s ↦ φ s x) (v x) 0 := by
      simpa only [φ.map_zero_apply] using hderiv x 0
    rw [show (fun s ↦ φ s x) = (fun _ ↦ x) from funext h] at hd
    exact hnz x (hd.unique (hasDerivAt_const 0 x))
  have hno (t : ℝ) (ht : 0 < t) (hret : φ t x = x) : False := by
    obtain ⟨U, _, _, _, ⟨e⟩, hinv⟩ :=
      Poincare.Topology.PlanarJordan.exists_invariant_disk_of_periodic_orbit
        φ hnon ⟨t, ht, hret⟩
    obtain ⟨y, _, hy⟩ := exists_zero_of_forward_invariant_disk e φ hv.continuousOn
      (fun {s} _ ↦ hinv s) (fun y _ s _ ↦ (hderiv y s).hasDerivWithinAt)
    exact hnz y hy
  have horder (s t : ℝ) (hst : s < t) (he : φ s x = φ t x) : False := by
    apply hno (t - s) (sub_pos.mpr hst)
    calc
      φ (t - s) x = φ (-s) (φ t x) := by rw [← φ.map_add]; congr 1; ring
      _ = φ (-s) (φ s x) := congrArg (φ (-s)) he.symm
      _ = x := by rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply]
  intro s t he
  rcases lt_trichotomy s t with h | h | h
  · exact (horder s t h he).elim
  · exact h
  · exact (horder t s h he.symm).elim

end Poincare.Analysis
