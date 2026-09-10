import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold
variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [T2Space M] [Finite ι]


theorem exists_finite_point_bumps {e : ι → M} (he : Injective e) {U : Set M}
    (hU : IsOpen U) (heU : ∀ i, e i ∈ U) :
    ∃ φ : ι → M → ℝ,
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      ∀ i, (φ i =ᶠ[𝓝 (e i)] (fun _ => (1 : ℝ))) ∧
        ∀ j, j ≠ i → φ j =ᶠ[𝓝 (e i)] (fun _ => (0 : ℝ)) := by
  classical
  let C : ι → Set M := fun i => range e \ {e i}
  have hC : ∀ i, (C i).Finite := fun i => (finite_range e).subset sdiff_subset
  have hlocal : ∀ i, ∃ b : SmoothBumpFunction I (e i), tsupport b ⊆ U \ C i := by
    intro i
    have hopen : IsOpen (U \ C i) := hU.sdiff (hC i).isClosed
    have hi : e i ∈ U \ C i := ⟨heU i,by simp [C]⟩
    obtain ⟨b,_,hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) (e i)).mem_iff.mp
      (hopen.mem_nhds hi)
    exact ⟨b,hb⟩
  choose b hb using hlocal
  refine ⟨fun i => b i,(fun i => ⟨(b i).contMDiff,(b i).hasCompactSupport,(hb i).trans sdiff_subset⟩),?_⟩
  intro i
  refine ⟨?_,?_⟩
  · filter_upwards [(b i).eventuallyEq_one] with x hx
    exact hx
  · intro j hji
    have hother : e i ∈ C j := ⟨mem_range_self i,fun h => hji (he (mem_singleton_iff.mp h)).symm⟩
    have hout : e i ∉ tsupport (b j) := fun h => (hb j h).2 hother
    filter_upwards [(isClosed_tsupport (b j)).isOpen_compl.mem_nhds hout] with x hx
    exact image_eq_zero_of_notMem_tsupport hx

end Poincare.Manifold
