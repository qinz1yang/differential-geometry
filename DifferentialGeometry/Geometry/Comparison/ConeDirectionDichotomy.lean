import DifferentialGeometry.Geometry.Comparison.ConeAntipodalGeodesic
import DifferentialGeometry.Geometry.Metric.ConeAntipodalLine

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

theorem exists_pointed_line_isometry_of_two_directions {a b : Y}
    (hab : Real.pi ≤ dist a b) (hcover : ∀ c : Y, c = a ∨ c = b) :
    ∃ e : EuclideanCone Y ≃ᵢ ℝ, e tip = 0 ∧
      ∀ t : ℝ, e (twoRayPath a b t) = t := by
  have hi := isometry_twoRayPath_iff.mpr hab
  have hsurj : Function.Surjective (twoRayPath a b) := by
    intro x
    rcases eq_tip_or_eq_mk x with hx | ⟨r, u, _, hx⟩
    · exact ⟨0, (twoRayPath_zero a b).trans hx.symm⟩
    · rcases hcover u with hu | hu
      · exact ⟨r, (twoRayPath_coe a b r).trans (by simpa only [hu] using hx.symm)⟩
      · exact ⟨-(r : ℝ), (twoRayPath_neg_coe a b r).trans (by simpa only [hu] using hx.symm)⟩
  let e : ℝ ≃ᵢ EuclideanCone Y :=
    { toEquiv := Equiv.ofBijective (twoRayPath a b) ⟨hi.injective, hsurj⟩
      isometry_toFun := hi }
  refine ⟨e.symm, ?_, fun t => e.symm_apply_apply t⟩
  have hz : e 0 = tip := twoRayPath_zero a b
  rw [← hz, e.symm_apply_apply]

theorem geodesic_or_pointed_line_of_cone_comparison
    (hdiam : ∀ a b : Y, dist a b ≤ Real.pi)
    (hcomp : fourPointComparison 0 (univ : Set (EuclideanCone Y)))
    (hstrict : ∀ a b : Y, dist a b < Real.pi →
      ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) :
    (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∨
    ∃ a b : Y, dist a b = Real.pi ∧ (∀ c : Y, c = a ∨ c = b) ∧
      ∃ e : EuclideanCone Y ≃ᵢ ℝ, e tip = 0 ∧
        ∀ t : ℝ, e (twoRayPath a b t) = t := by
  classical
  by_cases hgeo : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t
  · exact Or.inl hgeo
  · apply Or.inr
    obtain ⟨a, ha⟩ := not_forall.mp hgeo
    obtain ⟨b, habseg⟩ := not_forall.mp ha
    have hab : dist a b = Real.pi :=
      le_antisymm (hdiam a b) (le_of_not_gt (fun h => habseg (hstrict a b h)))
    have hcover : ∀ c : Y, c = a ∨ c = b := by
      intro c
      by_cases hca : c = a
      · exact Or.inl hca
      · by_cases hcb : c = b
        · exact Or.inr hcb
        · obtain ⟨f, hf, hf0, hf1, hfd, _⟩ :=
            exists_antipodal_segment_through_of_cone_comparison hdiam hcomp hstrict hab hca hcb
          exact (habseg ⟨f, hf, hf0, hf1, by simpa only [hab] using hfd⟩).elim
    exact ⟨a, b, hab, hcover, exists_pointed_line_isometry_of_two_directions hab.ge hcover⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
