import DifferentialGeometry.Geometry.Comparison.UniformRadialDefect
import DifferentialGeometry.Topology.MetricSpace.AlmostRadialPoint

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem exists_radial_map_of_arbitrarily_short_curves
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω W : Set X} (hcomp : fourPointComparison 1 Ω) {q : X} (hq : q ∈ Ω)
    {a D t ρ ε : ℝ} (ha : 0 < a) (haD : a ≤ D) (ht : t ∈ Ioo 0 1)
    (htD : t * D < ρ) (hε : 0 < ε) (hB : ball q ρ ⊆ Ω) (hW : W ⊆ Ω)
    (hrad : ∀ x ∈ W, dist q x ∈ Icc a D) :
    ∃ f : W → ball q ρ,
      (∀ x, dist q (f x : X) = t * dist q (x : X)) ∧
      ∀ x y, ε ≤ dist x y → ((t * D / sinh D) / 2) * dist x y ≤ dist (f x) (f y) := by
  classical
  obtain ⟨η, hη, hstab⟩ := exists_uniform_radial_defect ha haD ht hε
  have hpoint (x : W) : ∃ u : X, u ∈ ball q ρ ∧ dist q u = t * dist q (x : X) ∧
      (1 - t) * dist q (x : X) ≤ dist u (x : X) ∧
      dist u (x : X) ≤ (1 - t) * dist q (x : X) + η := by
    obtain ⟨c, _, _, _, _, s, hs, hlo, hhi, _⟩ :=
      exists_almost_radial_point_of_arbitrarily_short_curves hcurves q (x : X)
        (mul_nonneg ht.1.le dist_nonneg) (mul_le_of_le_one_left dist_nonneg ht.2.le) hη
    refine ⟨c s, ?_, hs, ?_, ?_⟩
    · rw [mem_ball, dist_comm, hs]
      exact (mul_le_mul_of_nonneg_left (hrad x x.property).2 ht.1.le).trans_lt htD
    · nlinarith
    · nlinarith
  choose u hu hqu hlo hhi using hpoint
  let f : W → ball q ρ := fun x => ⟨u x, hu x⟩
  refine ⟨f, hqu, ?_⟩
  intro x y hxy
  exact hstab hcomp hq (hW x.property) (hW y.property) (hB (hu x)) (hB (hu y))
    (hrad x x.property) (hrad y y.property) hxy (hqu x) (hlo x) (hhi x)
    (hqu y) (hlo y) (hhi y)

end DifferentialGeometry.Geometry.Comparison.Toponogov
