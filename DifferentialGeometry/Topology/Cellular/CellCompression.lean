import DifferentialGeometry.Topology.Cellular.Cellular
import DifferentialGeometry.Topology.ClosedBall.RadialCompression
import DifferentialGeometry.Topology.Homeomorph.ExtensionByIdentity

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

namespace EmbeddedClosedCell

variable {n : ℕ} {X : Type*} [MetricSpace X]

theorem exists_compression (c : EmbeddedClosedCell n X) {K : Set X}
    (hK : IsCompact K) (hKC : K ⊆ c.interiorSet) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : X ≃ₜ X, (∀ x ∉ c.interiorSet, H x = x) ∧ diam (H '' K) ≤ ε := by
  obtain ⟨R, hR, hR1, hKR⟩ := c.exists_radius_of_isCompact hK hKC
  let z : Disk n := ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨η, hη, hηmap⟩ := Metric.continuousAt_iff.mp
    (c.isClosedEmbedding.continuous.continuousAt (x := z)) (ε / 2) (by positivity)
  let r := min (R / 2) (η / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrη : r < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨h, -, hsmall, hfix⟩ := exists_radial_compression_supported
    (E := EuclideanSpace ℝ (Fin n)) (δ := r / 2) (ε := r) (R := R) (S := (R + 1) / 2)
    (by positivity) (by linarith) hrR (by linarith)
  have hball (x : EuclideanSpace ℝ (Fin n)) :
      x ∈ closedBall 0 1 ↔ h x ∈ closedBall 0 1 := by
    constructor
    · intro hx
      by_contra hh
      have hn : 1 < ‖h x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hh
      have heq : h x = x := h.injective (hfix (h x) (by linarith))
      exact hh (heq.symm ▸ hx)
    · intro hx
      by_contra hh
      have hn : 1 < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hh
      rw [hfix x (by linarith)] at hx
      exact hh hx
  let d : Disk n ≃ₜ Disk n := h.subtype hball
  have hds (x : Disk n) (hx : x ∈ diskSphere n) : d x = x := by
    apply Subtype.ext
    change h (x : EuclideanSpace ℝ (Fin n)) = x
    apply hfix
    rw [mem_diskSphere.mp hx]
    linarith
  obtain ⟨H, hH, hHfix, -⟩ := exists_homeomorph_extension_disk
    c.isClosedEmbedding c.isOpen_interior d hds
  refine ⟨H, ?_, ?_⟩
  · intro x hx
    by_cases hxc : x ∈ c.carrier
    · have hs : x ∈ c.map '' diskSphere n := by
        rw [← c.carrier_sdiff_interiorSet]
        exact ⟨hxc, hx⟩
      obtain ⟨v, hv, rfl⟩ := hs
      rw [hH, hds v hv]
    · exact hHfix x (fun hi => hxc (interior_subset hi))
  · have hsub : H '' K ⊆ ball (c.map z) (ε / 2) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨v, -, rfl⟩ := hKC hx
      rw [hH]
      have hv : ‖(d v : EuclideanSpace ℝ (Fin n))‖ < r :=
        mem_ball_zero_iff.mp (hsmall (mem_closedBall_zero_iff.mpr (hKR v hx)))
      apply hηmap
      have hd : dist (d v) z = ‖(d v : EuclideanSpace ℝ (Fin n))‖ := by
        change dist (d v : EuclideanSpace ℝ (Fin n)) 0 = _
        exact dist_zero_right _
      rw [hd]
      exact hv.trans hrη
    have := diam_le_of_subset_closedBall (by positivity : 0 ≤ ε / 2)
      (hsub.trans ball_subset_closedBall)
    linarith

end EmbeddedClosedCell

end DifferentialGeometry.Topology
