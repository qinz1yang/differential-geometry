import DifferentialGeometry.Topology.Manifold.ChartDisk.Construction

namespace DifferentialGeometry.Topology

open scoped ContDiff

noncomputable def sublevelProfile (δ s : ℝ) : ℝ :=
  1 / 2 - diskProfile δ (s + δ)

theorem sublevelProfile_contDiff (δ : ℝ) : ContDiff ℝ ∞ (sublevelProfile δ) :=
  contDiff_const.sub ((diskProfile_contDiff δ).comp (contDiff_id.add contDiff_const))

theorem sublevelProfile_bounds (δ s : ℝ) :
    -(1 / 2 : ℝ) ≤ sublevelProfile δ s ∧ sublevelProfile δ s ≤ 1 / 2 := by
  have := diskProfile_nonneg δ (s + δ)
  have := diskProfile_le_one δ (s + δ)
  dsimp [sublevelProfile]
  constructor <;> linarith

theorem sublevelProfile_eq_neg_half {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ -δ / 2) :
    sublevelProfile δ s = -1 / 2 := by
  rw [sublevelProfile, diskProfile_eq_one hδ (by linarith)]
  ring

theorem sublevelProfile_le_zero_iff {δ s : ℝ} (hδ : 0 < δ) :
    sublevelProfile δ s ≤ 0 ↔ s ≤ 0 := by
  have h := half_le_diskProfile_iff (R := δ) (t := s + δ) hδ
  dsimp [sublevelProfile]
  constructor
  · intro hs
    have := h.mp (by linarith)
    linarith
  · intro hs
    have := h.mpr (by linarith)
    linarith

theorem sublevelProfile_eq_zero_iff {δ s : ℝ} (hδ : 0 < δ) :
    sublevelProfile δ s = 0 ↔ s = 0 := by
  have h := diskProfile_eq_half_iff (R := δ) (t := s + δ) hδ
  dsimp [sublevelProfile]
  constructor
  · intro hs
    have := h.mp (by linarith)
    linarith
  · intro hs
    have := h.mpr (by linarith)
    linarith

theorem sublevelProfile_hasDerivAt_pos {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (sublevelProfile δ) d 0 := by
  obtain ⟨d, hd, hder⟩ := diskProfile_hasDerivAt_neg hδ
  have hshift : HasDerivAt (fun s : ℝ => s + δ) 1 0 := (hasDerivAt_id 0).add_const δ
  have hd' : HasDerivAt (diskProfile δ) d ((fun s : ℝ => s + δ) 0) := by
    simpa only [zero_add] using hder
  refine ⟨-d, neg_pos.mpr hd, ?_⟩
  convert! (hd'.comp 0 hshift).const_sub (1 / 2) using 1
  simp only [mul_one]

end DifferentialGeometry.Topology
