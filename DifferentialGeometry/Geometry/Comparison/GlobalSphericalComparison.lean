import DifferentialGeometry.Geometry.Comparison.ConeSphericalComparison
import DifferentialGeometry.Geometry.Comparison.SphericalAngleShortening

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem fourPointSphericalComparison_univ_of_cone_comparison
    {Y : Type*} [MetricSpace Y]
    (hdiam : ∀ v w : Y, dist v w ≤ Real.pi)
    (hcone : fourPointComparison 0 (univ : Set (EuclideanCone Y)))
    (hsegments : ∀ v w : Y, dist v w < Real.pi →
      ∃ f : Icc (0 : ℝ) 1 → Y,
        Continuous f ∧ f ⟨0, by norm_num⟩ = v ∧ f ⟨1, by norm_num⟩ = w ∧
        ∀ s t, dist (f s) (f t) = dist v w * dist s t) :
    fourPointSphericalComparison (univ : Set Y) := by
  have hshort := @sphericalComparisonAngle_le_of_shortening_left Y _ hdiam hcone
  intro p _ a _ b _ c _ hap hbp hcp hab hbc hca
  have hpa : 0 < dist p a := dist_pos.mpr hap.symm
  have hpb : 0 < dist p b := dist_pos.mpr hbp.symm
  have hpc : 0 < dist p c := dist_pos.mpr hcp.symm
  have haπ : dist p a < Real.pi := by linarith [dist_triangle p b a, dist_comm b a]
  have hbπ : dist p b < Real.pi := by linarith [dist_triangle p a b]
  have hcπ : dist p c < Real.pi := by linarith [dist_triangle p b c]
  have hex (x : Y) (hx : 0 < dist p x) (hxπ : dist p x < Real.pi) :
      ∃ u : Y, 0 < dist p u ∧ dist p u < Real.pi / 4 ∧
        dist p x = dist p u + dist u x := by
    obtain ⟨f, _, hf0, hf1, hd⟩ := hsegments p x hxπ
    let t : Icc (0 : ℝ) 1 := ⟨1 / 8, by norm_num⟩
    have hleft := hd ⟨0, by norm_num⟩ t
    have hright := hd t ⟨1, by norm_num⟩
    rw [hf0] at hleft
    rw [hf1] at hright
    norm_num [t, Subtype.dist_eq, Real.dist_eq] at hleft hright
    refine ⟨f t, ?_, ?_, ?_⟩
    · rw [hleft]; positivity
    · rw [hleft]; linarith [Real.pi_pos]
    · rw [hleft, hright]; ring
  obtain ⟨u, hu, huπ, hua⟩ := hex a hpa haπ
  obtain ⟨v, hv, hvπ, hvb⟩ := hex b hpb hbπ
  obtain ⟨w, hw, hwπ, hwc⟩ := hex c hpc hcπ
  have hpair (x y x' y' : Y) (hx' : 0 < dist p x') (hy' : 0 < dist p y')
      (hy : y ≠ p) (hxx' : dist p x = dist p x' + dist x' x)
      (hyy' : dist p y = dist p y' + dist y' y)
      (hper : dist p x + dist p y + dist x y < 2 * Real.pi) :
      sphericalComparisonAngle (dist p x) (dist p y) (dist x y) ≤
        sphericalComparisonAngle (dist p x') (dist p y') (dist x' y') := by
    have h1 := hshort hx' hy hxx' hper
    have hper' : dist p y + dist p x' + dist y x' < 2 * Real.pi := by
      have htri := dist_triangle y x x'
      rw [dist_comm y x, dist_comm x x'] at htri
      linarith
    have h2 := hshort hy' (dist_pos.mp hx').symm hyy' hper'
    rw [sphericalComparisonAngle_comm (dist p y),
      sphericalComparisonAngle_comm (dist p y'), dist_comm y x', dist_comm y' x'] at h2
    exact h1.trans h2
  have huv := hpair a b u v hu hv hbp hua hvb hab
  have hvw := hpair b c v w hv hw hcp hvb hwc hbc
  have hwu := hpair c a w u hw hu hap hwc hua hca
  have hsmall := sphericalComparisonAngle_sum_le_of_cone_comparison hcone hu hv hw
    (by linarith : dist p u < Real.pi / 2)
    (by linarith : dist p v < Real.pi / 2)
    (by linarith : dist p w < Real.pi / 2)
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
