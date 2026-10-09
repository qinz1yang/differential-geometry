import DifferentialGeometry.Geometry.Comparison.FiniteRadialComparison
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem radial_lower_of_distance_matrix {ι : Type*} (d : ι → ι → ℝ)
    (hself : ∀ i, d i i = 0) (hsymm : ∀ i j, d i j = d j i)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hcomp : ∀ q x y z, 0 < d q x → 0 < d q y → 0 < d q z →
      comparisonAngleNegCurvature 1 (d q x) (d q y) (d x y) +
        comparisonAngleNegCurvature 1 (d q y) (d q z) (d y z) +
        comparisonAngleNegCurvature 1 (d q z) (d q x) (d z x) ≤ 2 * Real.pi)
    {q x y u v : ι} {D t : ℝ} (hr : 0 < d q x) (hs : 0 < d q y)
    (hrD : d q x ≤ D) (hsD : d q y ≤ D) (ht : t ∈ Ioo 0 1)
    (hqu : d q u = t * d q x) (hux : d u x = (1 - t) * d q x)
    (hqv : d q v = t * d q y) (hvy : d v y = (1 - t) * d q y) :
    (t * D / sinh D) * d x y ≤ d u v := by
  let : PseudoMetricSpace (ι) := {
    dist := d
    dist_self := hself
    dist_comm := hsymm
    dist_triangle := htri }
  let p : ι → SeparationQuotient (ι) := SeparationQuotient.mk
  have hcomparison : fourPointComparison 1 (univ : Set (SeparationQuotient (ι))) := by
    intro q _ x _ y _ z _ hx hy hz
    obtain ⟨i, rfl⟩ := SeparationQuotient.surjective_mk q
    obtain ⟨j, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨k, rfl⟩ := SeparationQuotient.surjective_mk y
    obtain ⟨l, rfl⟩ := SeparationQuotient.surjective_mk z
    exact hcomp i j k l (dist_pos.mpr hx.symm) (dist_pos.mpr hy.symm) (dist_pos.mpr hz.symm)
  exact dist_radial_points_lower_of_fourPointComparison hcomparison
    (q := p q) (x := p x) (y := p y) (u := p u) (v := p v)
    (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _)
    hr hs hrD hsD ht hqu hux hqv hvy

end DifferentialGeometry.Geometry.Comparison.Toponogov
