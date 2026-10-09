import DifferentialGeometry.Geometry.Comparison.CompactRadialTarget
import DifferentialGeometry.Geometry.Comparison.PairedCompactPatch

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem exists_compact_closedBall_at_of_fourPointComparison [Nontrivial X]
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω : Set X} (hΩ : IsOpen Ω) (hcomp : fourPointComparison 1 Ω)
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH Ω ≤ n) {p : X} (hp : p ∈ Ω) :
    ∃ s : ℝ, 0 < s ∧ closedBall p s ⊆ Ω ∧ IsCompact (closedBall p s) := by
  obtain ⟨q, hq, ρ, hρ, hBΩ, hBc⟩ := exists_compact_closedBall_in_open_set
    hcurves hcomp (Subset.refl Ω) hΩ ⟨p, hp⟩ hcomplete hn hdim
  by_cases hpq : p = q
  · subst p
    exact ⟨ρ, hρ, hBΩ, hBc⟩
  have hd : 0 < dist q p := dist_pos.mpr (Ne.symm hpq)
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
  let h := min (R / 2) (dist q p / 4)
  have hh : 0 < h := lt_min (half_pos hR) (by positivity)
  have hhR : h < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hhd : h ≤ dist q p / 4 := min_le_right _ _
  let a := dist q p - h
  let D := dist q p + h
  have ha : 0 < a := by dsimp [a]; linarith
  have haD : a ≤ D := by dsimp [a, D]; linarith
  have hD : 0 < D := ha.trans_le haD
  let t := min (1 / 2) (ρ / (2 * D))
  have ht : t ∈ Ioo 0 1 := ⟨lt_min (by norm_num) (by positivity),
    (min_le_left _ _).trans_lt (by norm_num)⟩
  have htD : t * D < ρ := by
    have hb := mul_le_mul_of_nonneg_right (min_le_right (1 / 2) (ρ / (2 * D))) hD.le
    have he : ρ / (2 * D) * D = ρ / 2 := by field_simp
    rw [he] at hb
    exact hb.trans_lt (half_lt_self hρ)
  have hWΩ : ball p h ⊆ Ω := (ball_subset_ball hhR.le).trans hRΩ
  have hrad (x : X) (hx : x ∈ ball p h) : dist q x ∈ Icc a D := by
    have hpx : dist p x < h := by simpa only [mem_ball, dist_comm] using hx
    have htri := dist_triangle q p x
    have hrev := dist_triangle q x p
    rw [dist_comm x p] at hrev
    constructor <;> dsimp [a, D] <;> linarith
  have htb := totallyBounded_annulus_of_compact_radial_target hcurves hcomp hq ha haD
    ht htD (ball_subset_closedBall.trans hBΩ) hWΩ hrad hBc
  obtain ⟨Rc, hRc, hc⟩ := hcomplete p hp
  let s := min (h / 2) Rc
  have hs : 0 < s := lt_min (half_pos hh) hRc
  have hsh : s < h := (min_le_left _ _).trans_lt (half_lt_self hh)
  have hsRc : s ≤ Rc := min_le_right _ _
  have hsc : IsComplete (closedBall p s) := by
    intro f hf hfs
    obtain ⟨x, _, hfx⟩ := hc f hf
      (hfs.trans (Filter.principal_mono.mpr (closedBall_subset_closedBall hsRc)))
    exact ⟨x, isClosed_iff_clusterPt.mp isClosed_closedBall x
      (hf.1.mono (le_inf hfx hfs)), hfx⟩
  exact ⟨s, hs, (closedBall_subset_ball hsh).trans hWΩ,
    (htb.subset (closedBall_subset_ball hsh)).isCompact_of_isComplete hsc⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
