import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Topology.PartitionOfUnity.CompactSupport
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
open Bundle Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
theorem gradientFun_eq_sum_fintsupportOn
    {ι : Type*} {s K : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    (hK : IsCompact K) (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hfK : Function.support f ⊆ K) (hfs : Function.support f ⊆ s)
    {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    gradientFun g f x =
      ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
        gradientFun g (fun y => ρ i y * f y) x := by
  classical
  have heq : f = ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      (fun y => ρ i y * f y) := by
    funext y
    simp only [Finset.sum_apply]
    change f y = ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      ρ.toPartitionOfUnity i y • f y
    exact (ρ.toPartitionOfUnity.sum_fintsupportOn_smul hK hfK hfs y).symm
  calc
    gradientFun g f x = gradientFun g
        (∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK, (fun y => ρ i y * f y)) x := by
      rw [← heq]
    _ = _ := gradientFun_sum g _ fun i _ =>
      ((ρ i).contMDiff.mdifferentiableAt (by simp)).mul hf
end DifferentialGeometry.Geometry.Operator
