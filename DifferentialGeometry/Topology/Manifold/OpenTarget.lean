import DifferentialGeometry.Topology.Manifold.OpenSubtype



open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace G N]



theorem contMDiffWithinAt_subtypeVal_comp_iff {n : ℕ∞ω}
    (U : TopologicalSpace.Opens N) (f : M → U) (s : Set M) (x : M) :
    ContMDiffWithinAt I J n (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt I J n f s x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..


theorem contMDiff_subtypeVal_comp_iff {n : ℕ∞ω}
    (U : TopologicalSpace.Opens N) (f : M → U) :
    ContMDiff I J n (Subtype.val ∘ f) ↔ ContMDiff I J n f := by
  simp only [ContMDiff, ContMDiffAt, contMDiffWithinAt_subtypeVal_comp_iff]



theorem mdifferentiableWithinAt_subtypeVal_comp_iff
    (U : TopologicalSpace.Opens N) (f : M → U) (s : Set M) (x : M) :
    MDifferentiableWithinAt I J (Subtype.val ∘ f) s x ↔ MDifferentiableWithinAt I J f s x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..


theorem mdifferentiableAt_subtypeVal_comp_iff
    (U : TopologicalSpace.Opens N) (f : M → U) (x : M) :
    MDifferentiableAt I J (Subtype.val ∘ f) x ↔ MDifferentiableAt I J f x := by
  simpa only [mdifferentiableWithinAt_univ] using
    mdifferentiableWithinAt_subtypeVal_comp_iff (I := I) (J := J) U f Set.univ x




theorem mfderiv_subtypeVal_comp
    (U : TopologicalSpace.Opens N) (f : M → U) (x : M) :
    mfderiv I J (Subtype.val ∘ f) x = mfderiv I J f x := by
  by_cases hf : MDifferentiableAt I J f x
  · have h := mfderiv_comp x
      (DifferentialGeometry.hasMFDerivAt_subtype_val (I := J) U (f x)).mdifferentiableAt hf
    rw [DifferentialGeometry.mfderiv_subtype_val] at h
    exact h.trans (by ext v; rfl)
  · rw [mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt
        (fun h => hf ((mdifferentiableAt_subtypeVal_comp_iff U f x).mp h))]
    rfl

end DifferentialGeometry.Topology
