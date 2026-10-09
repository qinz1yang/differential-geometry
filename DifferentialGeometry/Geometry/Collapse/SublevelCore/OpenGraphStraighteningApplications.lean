import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenGraphStraightening
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Consumer of LC59 (open graph straightening)

A concrete instance of `exists_openGraph_straightening` on the circle: the open region of the
cylinder `Circle × ℝ` between the level `0` and the graph of the continuous height
`z ↦ 2 + Re z` is diffeomorphic, fibrewise and increasingly, to the straight band
`Circle × (0, 1)`, by a map that fixes the lower part `u ≤ 1/2`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

/-- **Consumer of LC59.** Straightening of the region under the graph of `2 + Re z` over the
circle. -/
theorem exists_circle_openGraph_straightening :
    ∃ P : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) (Circle × ℝ)
        (Circle × ℝ) ∞,
      P.source = {z | 0 < z.2 ∧ z.2 < 1} ∧
      P.target = {z | 0 < z.2 ∧ z.2 < 2 + ((z.1 : ℂ)).re} ∧
      (∀ z ∈ P.source, (P z).1 = z.1) ∧ (∀ z ∈ P.source, z.2 ≤ 1 / 2 → P z = z) ∧
      ∀ x, StrictMonoOn (fun u => (P (x, u)).2) (Ioo 0 1) := by
  have hcont : Continuous fun z : Circle => 2 + ((z : ℂ)).re :=
    continuous_const.add (Complex.continuous_re.comp continuous_subtype_val)
  have hlow : ∀ z : Circle, (1 / 2 : ℝ) < 2 + ((z : ℂ)).re := by
    intro z
    have h1 : |((z : ℂ)).re| ≤ 1 := by
      have := Complex.abs_re_le_norm (z : ℂ)
      rwa [Circle.norm_coe] at this
    have h2 := neg_abs_le ((z : ℂ)).re
    linarith
  exact exists_openGraph_straightening (J := 𝓡 1) (a := 0) (c := 1 / 2) (r := 1)
    (by norm_num) (by norm_num) _ hcont hlow

end DifferentialGeometry.Geometry.Collapse
