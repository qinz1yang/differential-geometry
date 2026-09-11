import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F H H' M N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]

theorem mfderiv_comp_open_val (U : Opens N) (f : M → U)
    (hf : ContMDiff I J ∞ f) (x : M) :
    mfderiv I J (Subtype.val ∘ f) x = mfderiv I J f x := by
  have h := mfderiv_comp x
    ((contMDiff_subtype_val (I := J) (U := U) (n := ∞)).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [DifferentialGeometry.mfderiv_subtype_val] at h
  exact h

theorem mfderiv_restrict_open (U : Opens M) (f : M → N)
    (hf : ContMDiff I J ∞ f) (x : U) :
    mfderiv I J (f ∘ (Subtype.val : U → M)) x = mfderiv I J f x.val := by
  have h := mfderiv_comp x (hf.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiableAt (by simp))
  rw [DifferentialGeometry.mfderiv_subtype_val] at h
  exact h
end DifferentialGeometry.Topology.Manifold
