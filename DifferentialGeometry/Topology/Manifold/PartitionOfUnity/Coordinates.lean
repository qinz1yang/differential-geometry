import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

section

noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace SmoothPartitionOfUnity

variable {ι E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ F H} {K : Set M}
  (mu : SmoothPartitionOfUnity ι I M K)
  (U : TopologicalSpace.Opens E) (e : U → M)

def coordinateWeights : E → ι → ℝ :=
  Function.extend Subtype.val (fun z : U => fun i => mu i (e z)) (fun _ => 0)

omit [NormedSpace ℝ E] in
@[simp] theorem coordinateWeights_apply (z : U) (i : ι) :
    mu.coordinateWeights U e z i = mu i (e z) := by
  unfold coordinateWeights
  rw [Subtype.val_injective.extend_apply]

theorem contDiffOn_coordinateWeights [Fintype ι] (he : ContMDiff 𝓘(ℝ, E) I ∞ e) :
    ContDiffOn ℝ ∞ (mu.coordinateWeights U e) U := by
  apply contDiffOn_pi.mpr
  intro i z hz
  have hsub : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun z : U => mu.coordinateWeights U e z i) ⟨z, hz⟩ := by
    simpa only [coordinateWeights_apply, Function.comp_def] using ((mu i).contMDiff.comp he).contMDiffAt
  have hamb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun z => mu.coordinateWeights U e z i) z :=
    (contMDiffAt_subtype_iff (U := U) (x := ⟨z, hz⟩)
      (f := fun z => mu.coordinateWeights U e z i)).mp hsub
  exact (contMDiffAt_iff_contDiffAt.mp hamb).contDiffWithinAt

omit [NormedSpace ℝ E] in
theorem coordinateWeights_nonneg (z : U) (i : ι) :
    0 ≤ mu.coordinateWeights U e z i := by
  rw [coordinateWeights_apply]
  exact mu.nonneg i (e z)

omit [NormedSpace ℝ E] in
theorem sum_coordinateWeights_eq_one [Fintype ι] (z : U) (hz : e z ∈ K) :
    ∑ i, mu.coordinateWeights U e z i = 1 := by
  simpa only [coordinateWeights_apply, finsum_eq_sum_of_fintype] using mu.sum_eq_one hz

end SmoothPartitionOfUnity

end

end
