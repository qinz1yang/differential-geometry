import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F H Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace Q] [ChartedSpace H Q]

theorem mfderiv_eq_comp_fderiv_of_open_transition
    (U : TopologicalSpace.Opens E) (f g : U → Q) (J : E → E)
    (hJ : DifferentiableOn ℝ J U)
    (hg : MDifferentiable (modelWithCornersSelf ℝ E) I g)
    (hcompat : ∀ u v : U, J u = v → f u = g v)
    (z w : U) (hzw : J z = w) :
    mfderiv (modelWithCornersSelf ℝ E) I f z =
      (mfderiv (modelWithCornersSelf ℝ E) I g w).comp (fderiv ℝ J z) := by
  let W : TopologicalSpace.Opens U :=
    ⟨(fun u : U => J u) ⁻¹' U,
      U.isOpen.preimage (hJ.continuousOn.comp_continuous continuous_subtype_val
        (fun u => u.property))⟩
  let zW : W := ⟨z, by change J z ∈ U; rw [hzw]; exact w.property⟩
  let tau : W → U := fun u => ⟨J u.val, u.property⟩
  have hJsub : MDifferentiable (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
      (fun u : U => J u) := by
    intro u
    apply DifferentialGeometry.mdifferentiableAt_subtype_iff.mpr
    exact ((hJ u u.property).differentiableAt (U.isOpen.mem_nhds u.property)).mdifferentiableAt
  have htau : MDifferentiable (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) tau := by
    intro u
    apply (MDifferentiableAt.subtypeVal_comp_iff tau u).mp
    exact (hJsub u.val).comp u (DifferentialGeometry.hasMFDerivAt_subtype_val W u).mdifferentiableAt
  have htauDeriv : mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) tau zW =
      fderiv ℝ J z := by
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp tau zW]
    change mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
      (fun u : W => J u.val) zW = _
    rw [DifferentialGeometry.mfderiv_restrict_open (fun u : U => J u) W zW,
      DifferentialGeometry.mfderiv_restrict_open J U z, mfderiv_eq_fderiv]
  have htauw : tau zW = w := Subtype.ext hzw
  have hcomp : g ∘ tau = fun u : W => f u.val := by
    funext u
    exact (hcompat u.val (tau u) rfl).symm
  have hd := mfderiv_comp zW
    (hg (tau zW)) (htau zW)
  rw [hcomp, DifferentialGeometry.mfderiv_restrict_open f W zW,
    htauw, htauDeriv] at hd
  exact hd

end DifferentialGeometry.Topology.Manifold

end
