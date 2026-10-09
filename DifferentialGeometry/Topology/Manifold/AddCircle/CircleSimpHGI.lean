import DifferentialGeometry.Topology.Manifold.AddCircle.Circle

/-!
# Two `simp` lemmas for `AddCircle.diffeomorphCircle` (S-HG-INTAKE, suffix `_HGI`)

Verbatim: the declarations `diffeomorphCircle_apply_coe` and `diffeomorphCircle_symm_apply_exp`
that the donor branch `codex/della-mostow-smooth-adapter-20261004` (467465bc6c) adds to
`Topology/Manifold/AddCircle/Circle.lean`; the tracked file does not have them.
-/

set_option autoImplicit false

open scoped ContDiff Manifold

namespace AddCircle

@[simp] theorem diffeomorphCircle_apply_coe (t : ℝ) :
    diffeomorphCircle (t : AddCircle (1 : ℝ)) = Circle.exp (2 * Real.pi * t) := by
  change homeomorphCircle one_ne_zero (t : AddCircle (1 : ℝ)) = _
  rw [homeomorphCircle_apply, toCircle_apply_mk]
  congr 1
  ring

@[simp] theorem diffeomorphCircle_symm_apply_exp (t : ℝ) :
    diffeomorphCircle.symm (Circle.exp (2 * Real.pi * t)) = (t : AddCircle (1 : ℝ)) := by
  rw [← diffeomorphCircle_apply_coe]
  exact diffeomorphCircle.symm_apply_apply _

end AddCircle
