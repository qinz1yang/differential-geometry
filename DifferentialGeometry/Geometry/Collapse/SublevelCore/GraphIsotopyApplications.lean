import DifferentialGeometry.Geometry.Collapse.SublevelCore.GraphIsotopy
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Consumer of the graph-to-level isotopy

On the unit circle `Q = 𝕊¹ ⊆ ℂ` (a compact manifold modelled on `EuclideanSpace ℝ (Fin 1)`), the
tilted height `h z = 1 + Re z / 2` takes values in `[1/2, 3/2] ⊆ (0, 3)`. The shared kernel
`exists_graphIsotopy_compactSupport` moves its closed subgraph in `𝕊¹ × ℝ` onto the slab
`{u ≤ 1}` by smooth diffeomorphisms supported in one compact subset of `𝕊¹ × (0, 3)`.
-/

set_option autoImplicit false

noncomputable section

open Set Complex
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] finrank_real_complex_fact'

theorem contMDiff_circle_tilt :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun z : Circle => 1 + (z : ℂ).re / 2) := by
  have hre : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun z : Circle => (z : ℂ).re) :=
    reCLM.contDiff.contMDiff.comp contMDiff_coe_sphere
  have haff : ContDiff ℝ ∞ (fun r : ℝ => 1 + r / 2) := by fun_prop
  exact haff.contMDiff.comp hre

theorem circle_tilt_mem (z : Circle) : 1 + (z : ℂ).re / 2 ∈ Ioo (0 : ℝ) 3 := by
  have h := abs_re_le_norm (z : ℂ)
  rw [Circle.norm_coe] at h
  have h' := abs_le.mp h
  constructor <;> linarith [h'.1, h'.2]

/-- **Consumer.** The closed subgraph of the tilted height on the circle is carried onto
`{u ≤ 1}` by a smooth compactly supported isotopy of `𝕊¹ × ℝ`, its graph onto `{u = 1}`. -/
theorem circle_tilted_subgraph_isotopic :
    ∃ Φ : ℝ → Diffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) (Circle × ℝ) (Circle × ℝ) ∞,
      Φ 0 = Diffeomorph.refl ((𝓡 1).prod 𝓘(ℝ, ℝ)) (Circle × ℝ) ∞ ∧
      (∃ S : Set (Circle × ℝ), IsCompact S ∧ S ⊆ univ ×ˢ Ioo 0 3 ∧
        ∀ t, ∀ z ∉ S, Φ t z = z ∧ (Φ t).symm z = z) ∧
      Φ 1 '' {z | z.2 ≤ 1 + (z.1 : ℂ).re / 2} = {z | z.2 ≤ 1} ∧
      Φ 1 '' {z | z.2 = 1 + (z.1 : ℂ).re / 2} = {z | z.2 = 1} := by
  obtain ⟨Φ, h0, -, -, -, -, -, hS, hle, heq, -⟩ :=
    exists_graphIsotopy_compactSupport (n := ⊤) (a := 0) (b := 3) (ρ := 1)
      (fun z : Circle => 1 + (z : ℂ).re / 2) contMDiff_circle_tilt
      (fun z => (circle_tilt_mem z).1) (fun z => (circle_tilt_mem z).2) ⟨by norm_num, by norm_num⟩
  exact ⟨Φ, h0, hS, hle, heq⟩

end DifferentialGeometry.Geometry.Collapse
