import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_contMDiff_extension_near_compact
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧
      ∀ x ∈ K, F =ᶠ[𝓝 x] f := by
  have hdisjoint : Disjoint Uᶜ K := disjoint_left.mpr fun x hx hxK => hx (hKU hxK)
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    I hU.isClosed_compl hK.isClosed hdisjoint (n := ⊤)
  have hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ := χ.contMDiff.of_le (by simp)
  refine ⟨fun x => χ x * f x, fun x => ?_, fun x hx => ?_⟩
  · by_cases hx : x ∈ U
    · exact hχ.contMDiffAt.mul ((hf x hx).contMDiffAt (hU.mem_nhds hx))
    · have hz : ∀ᶠ y in 𝓝 x, χ y = 0 := hzero.filter_mono (nhds_le_nhdsSet hx)
      have hconst : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) x :=
        contMDiffAt_const
      apply hconst.congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      rw [hy, zero_mul]
  · have h1 : ∀ᶠ y in 𝓝 x, χ y = 1 := hone.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [h1] with y hy
    rw [hy, one_mul]

end DifferentialGeometry.Geometry.Topology

end
