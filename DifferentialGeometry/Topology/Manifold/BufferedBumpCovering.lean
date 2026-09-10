import DifferentialGeometry.Topology.Manifold.BufferedFunctionCutoff
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

theorem exists_uniform_controlled_bumpCovering_of_buffered_functions
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) [Finite ι], ∀ (U : ι → Set M), (∀ i, IsOpen (U i)) →
      ∀ (u : ι → M → ℝ), (∀ i, ContMDiffOn I 𝓘(ℝ) ∞ (u i) (U i)) →
      ∀ (a b η : ι → ℝ), (∀ i, 0 < η i) →
      (∀ i, closure (U i ∩ u i ⁻¹' Icc (a i) (b i)) ⊆ U i) →
      (∀ x : M, ∃ i, x ∈ U i ∧ u i x ∈ Ioo (a i + η i) (b i - η i)) →
      ∃ f : BumpCovering ι M, (∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)) ∧
        (∀ i, tsupport (f i) ⊆ closure (U i ∩ u i ⁻¹' Icc (a i) (b i))) ∧
        (∀ i, ∀ x ∈ U i, u i x ∈ Icc (a i + η i) (b i - η i) → f i x = 1) ∧
        ∀ i, ∀ x ∈ U i, ∀ v : TangentSpace I x,
          |mvfderiv I (f i) x v| ≤ (C / η i) * |mvfderiv I (u i) x v| := by
  classical
  obtain ⟨C, hC, hcutoff⟩ := exists_uniform_cutoff_of_buffered_function (I := I) (M := M)
  refine ⟨C, hC, ?_⟩
  intro ι _ U hU u hu a b η hη hbuffer hcover
  choose β hβ hbound hsupp hone hderiv using
    (fun i ↦ hcutoff (U i) (hU i) (u i) (hu i) (a i) (b i) (η i) (hη i) (hbuffer i))
  have hevent (x : M) : ∃ i, β i =ᶠ[𝓝 x] fun _ ↦ 1 := by
    obtain ⟨i, hxu, hxcore⟩ := hcover x
    refine ⟨i, ?_⟩
    have hopen := (hu i).continuousOn.isOpen_inter_preimage (hU i)
      (isOpen_Ioo : IsOpen (Ioo (a i + η i) (b i - η i)))
    filter_upwards [hopen.mem_nhds (show x ∈ U i ∩ u i ⁻¹' Ioo (a i + η i) (b i - η i)
      from ⟨hxu, hxcore⟩)] with y hy
    exact hone i y hy.1 ⟨hy.2.1.le, hy.2.2.le⟩
  let f : BumpCovering ι M := {
    toFun := fun i ↦ ⟨β i, (hβ i).continuous⟩
    locallyFinite' := locallyFinite_of_finite _
    nonneg' := fun i x ↦ (hbound i x).1
    le_one' := fun i x ↦ (hbound i x).2
    eventuallyEq_one' := fun x _ ↦ hevent x }
  exact ⟨f, hβ, hsupp, hone, hderiv⟩

theorem exists_controlled_bumpCovering_of_buffered_functions
    {ι E H M : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ι → Set M), (∀ i, IsOpen (U i)) →
      ∀ (u : ι → M → ℝ), (∀ i, ContMDiffOn I 𝓘(ℝ) ∞ (u i) (U i)) →
      ∀ (a b η : ι → ℝ), (∀ i, 0 < η i) →
      (∀ i, closure (U i ∩ u i ⁻¹' Icc (a i) (b i)) ⊆ U i) →
      (∀ x : M, ∃ i, x ∈ U i ∧ u i x ∈ Ioo (a i + η i) (b i - η i)) →
      ∃ f : BumpCovering ι M, (∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)) ∧
        (∀ i, tsupport (f i) ⊆ closure (U i ∩ u i ⁻¹' Icc (a i) (b i))) ∧
        (∀ i, ∀ x ∈ U i, u i x ∈ Icc (a i + η i) (b i - η i) → f i x = 1) ∧
        ∀ i, ∀ x ∈ U i, ∀ v : TangentSpace I x,
          |mvfderiv I (f i) x v| ≤ (C / η i) * |mvfderiv I (u i) x v| := by
  obtain ⟨C, hC, h⟩ := exists_uniform_controlled_bumpCovering_of_buffered_functions (I := I) (M := M)
  exact ⟨C, hC, h ι⟩

end Poincare.Topology.Manifold
