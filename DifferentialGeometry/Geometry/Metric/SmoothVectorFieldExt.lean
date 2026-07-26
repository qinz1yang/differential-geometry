import DifferentialGeometry.Geometry.Metric.ChartGram

/-!
# Chart-constant smooth tangent sections

The chart-constant tangent field at `x₀` with fibre value `c`, obtained by transporting
`c` through the inverse trivialization centred at `x₀`, is a smooth bundle section on the
trivialization base set (`chartConstVec_contMDiffOn`) and recovers a prescribed vector at
the centre (`chartConstVecFiber_self`).  These are the local building blocks of a global
smooth vector field with a prescribed value at a point (the launch field of the
first-variation / center-of-mass gradient construction).

NOTE: this file deliberately imports ONLY `ChartGram`.  Adding the section-globalization
imports (`Mathlib.Geometry.Manifold.VectorBundle.SmoothSection`,
`Mathlib.Geometry.Manifold.PartitionOfUnity`) here induces an instance-resolution `whnf`
timeout on `chartConstVec_contMDiffOn`.  The global producer must therefore live in a
SEPARATE downstream file that imports this one (using the compiled lemma, not re-elaborating
the trivialization internals) together with the globalization machinery.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart-constant tangent field at `x₀` with fibre value `c`. -/
def chartConstVecFiber (x₀ : M) (c : E) (x : M) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symm x c

/-- The chart-constant field with the right fibre value recovers `v` at the centre. -/
lemma chartConstVecFiber_self (q : M) (v : TangentSpace I q) :
    chartConstVecFiber (I := I) q
      ((trivializationAt E (TangentSpace I) q ⟨q, v⟩).2) q = v := by
  have hq : q ∈ (trivializationAt E (TangentSpace I) q).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) q
  simp only [chartConstVecFiber]
  exact (trivializationAt E (TangentSpace I) q).symm_apply_apply_mk hq v

/-- The chart-constant field is a smooth bundle section on the trivialization base set. -/
lemma chartConstVec_contMDiffOn (x₀ : M) (c : E) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
        (chartConstVecFiber (I := I) x₀ c x))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun x => chartConstVecFiber (I := I) x₀ c x)
  refine hiff.mpr ?_
  refine (contMDiffOn_const (c := c)).congr ?_
  intro x hx
  have h := (trivializationAt E (TangentSpace I) x₀).apply_mk_symm hx c
  simpa [chartConstVecFiber] using congrArg Prod.snd h

end Riemannian
end Geometry
end DifferentialGeometry

end
