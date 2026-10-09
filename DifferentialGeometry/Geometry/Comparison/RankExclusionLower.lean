import DifferentialGeometry.Geometry.Comparison.PairedRankIncrease
import DifferentialGeometry.Topology.MetricSpace.DistanceCoordinates

set_option autoImplicit false

open Set Real Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X] [Fintype ι]

theorem PairedComparisonPacket.distanceCoordinates_lower_of_rank_exclusion
    {δ β : ℝ} {V Ω : Set X} {a b : ι → X}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω)
    (hanchors : range a ∪ range b ⊆ Ω) {a₀ A : ℝ} (ha₀ : 0 < a₀)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hδ : 0 ≤ δ) (hδβ : δ ≤ β / 100)
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A)
    (hno : ∀ z ∈ V, ∀ c d : Option ι → X, range c ∪ range d ⊆ Ω →
      ¬ PairedComparisonPacket β {z} c d)
    {q : X} {r : ℝ} (hbuf : ball q (3 * r) ⊆ V)
    (hr1 : 2 * r ≤ 1) (hra : 2 * r ≤ a₀ / 2)
    (hrK : 2 * r ≤ (β / (100 * Real.pi)) ^ 2 / (4 * cosh (A + 1) / sinh a₀))
    {x y : X} (hx : x ∈ ball q r) (hy : y ∈ ball q r) :
    (β / (100 * Real.pi)) ^ 2 * dist x y ≤ dist (distanceCoordinates 2 a x) (distanceCoordinates 2 a y) := by
  by_cases hxy : x = y
  · subst y
    simp
  have hL : 0 < dist x y := dist_pos.mpr hxy
  have hxd : dist x q < r := hx
  have hyd : dist y q < r := hy
  have hLr : dist x y < 2 * r := by
    have h := dist_triangle x q y
    rw [dist_comm q y] at h
    exact lt_of_le_of_lt h (by linarith)
  have hball : closedBall x (dist x y) ⊆ V := by
    intro z hz
    apply hbuf
    change dist z q < 3 * r
    have hh := dist_triangle z x q
    have hz' : dist z x ≤ dist x y := hz
    linarith
  have hex : ∃ i, (β / (100 * Real.pi)) ^ 2 * dist x y < |dist x (a i) - dist y (a i)| := by
    by_contra h
    have hcoords : ∀ i, |dist x (a i) - dist y (a i)| ≤ (β / (100 * Real.pi)) ^ 2 * dist x y := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    obtain ⟨z, hz, _, _, _, hp, hanchors'⟩ := hpacket.exists_extension_of_near_coordinates
      hcurves hcomp hV hanchors ha₀ hβ hβ1 hδ hδβ hbounds
      hL (hLr.le.trans hr1) (hLr.le.trans hra) (hLr.le.trans hrK) hball hcoords
    exact hno z hz _ _ hanchors' hp
  obtain ⟨i, hi⟩ := hex
  have h := PiLp.dist_apply_le (distanceCoordinates 2 a x) (distanceCoordinates 2 a y) i
  rw [distanceCoordinates_apply, distanceCoordinates_apply, Real.dist_eq] at h
  exact hi.le.trans h

end DifferentialGeometry.Geometry.Comparison.Toponogov
