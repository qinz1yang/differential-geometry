import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

section

open Function Set
open scoped Manifold ContDiff Topology BigOperators

noncomputable section

namespace SmoothPartitionOfUnity

universe uI uE uH uM

variable {ι : Type uI} [Finite ι] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] {s : Set M}

def concentrate (f : SmoothPartitionOfUnity ι I M s) (i₀ : ι)
    (β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (hβ : ∀ x, β x ∈ Icc (0 : ℝ) 1) :
    SmoothPartitionOfUnity ι I M s := by
  classical
  letI := Fintype.ofFinite ι
  refine {
    toFun := fun i => ⟨fun x => (1 - β x) * f i x + if i = i₀ then β x else 0, ?_⟩
    locallyFinite' := locallyFinite_of_finite _
    nonneg' := ?_
    sum_eq_one' := ?_
    sum_le_one' := ?_ }
  · apply ContMDiff.add
    · exact (contMDiff_const.sub β.contMDiff).mul (f i).contMDiff
    · split_ifs
      · exact β.contMDiff
      · exact contMDiff_const
  · intro i x
    apply add_nonneg (mul_nonneg (sub_nonneg.mpr (hβ x).2) (f.nonneg i x))
    split_ifs
    · exact (hβ x).1
    · exact le_rfl
  · intro x hx
    rw [finsum_eq_sum_of_fintype]
    change ∑ i, ((1 - β x) * f i x + if i = i₀ then β x else 0) = 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true,
      show ∑ i, f i x = 1 by simpa only [finsum_eq_sum_of_fintype] using f.sum_eq_one hx,
      mul_one, sub_add_cancel]
  · intro x
    rw [finsum_eq_sum_of_fintype]
    change ∑ i, ((1 - β x) * f i x + if i = i₀ then β x else 0) ≤ 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hf : ∑ i, f i x ≤ 1 := by simpa only [finsum_eq_sum_of_fintype] using f.sum_le_one x
    nlinarith [mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr (hβ x).2)]

theorem concentrate_apply (f : SmoothPartitionOfUnity ι I M s) (i₀ : ι)
    (β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (hβ : ∀ x, β x ∈ Icc (0 : ℝ) 1) (i : ι) (x : M) :
    letI := Classical.decEq ι
    f.concentrate i₀ β hβ i x = (1 - β x) * f i x + if i = i₀ then β x else 0 := rfl

theorem concentrate_apply_of_eq_one (f : SmoothPartitionOfUnity ι I M s) (i₀ : ι)
    (β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (hβ : ∀ x, β x ∈ Icc (0 : ℝ) 1)
    {x : M} (hx : β x = 1) (i : ι) :
    letI := Classical.decEq ι
    f.concentrate i₀ β hβ i x = if i = i₀ then 1 else 0 := by
  classical
  simp only [concentrate_apply, hx, sub_self, zero_mul, zero_add]

theorem isSubordinate_concentrate (f : SmoothPartitionOfUnity ι I M s) (i₀ : ι)
    (β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (hβ : ∀ x, β x ∈ Icc (0 : ℝ) 1)
    {U : ι → Set M} (hf : f.IsSubordinate U) (hs : tsupport β ⊆ U i₀) :
    (f.concentrate i₀ β hβ).IsSubordinate U := by
  classical
  intro i
  change tsupport (fun x => (1 - β x) * f i x + if i = i₀ then β x else 0) ⊆ U i
  apply Set.Subset.trans (tsupport_add _ _)
  apply Set.union_subset
  · exact (tsupport_mul_subset_right).trans (hf i)
  · by_cases hi : i = i₀
    · simpa only [hi, if_true] using hs
    · simp only [hi, ↓reduceIte]
      change tsupport (0 : M → ℝ) ⊆ U i
      rw [tsupport_zero]
      exact empty_subset _

end SmoothPartitionOfUnity

end

end

section

set_option autoImplicit false

open Set Filter Topology
open scoped ContDiff Manifold

namespace SmoothPartitionOfUnity

variable {ι E H M : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_isSubordinate_eq_single_near
    {K : Set M} (hK : IsClosed K) (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) (i₀ : ι) {x₀ : M} (hx₀ : x₀ ∈ U i₀) :
    letI := Classical.decEq ι
    ∃ ρ : SmoothPartitionOfUnity ι I M K, ρ.IsSubordinate U ∧
      ∃ W : Set M, IsOpen W ∧ x₀ ∈ W ∧
        ∀ x ∈ W, ∀ i, ρ i x = if i = i₀ then 1 else 0 := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_isSubordinate I hK U hU hcover
  obtain ⟨f, _, hf⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp
    ((hU i₀).mem_nhds hx₀)
  let β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ := ⟨f, f.contMDiff⟩
  have hβ : ∀ x, β x ∈ Icc (0 : ℝ) 1 := fun _ => f.mem_Icc
  have hβsupp : tsupport β ⊆ U i₀ := hf
  have hβone : ∀ᶠ x in 𝓝 x₀, β x = 1 := f.eventuallyEq_one
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp hβone
  refine ⟨ρ.concentrate i₀ β hβ, ρ.isSubordinate_concentrate i₀ β hβ hρ hβsupp,
    W, hWopen, hxW, ?_⟩
  intro x hx i
  exact ρ.concentrate_apply_of_eq_one i₀ β hβ (hWsub hx) i

end SmoothPartitionOfUnity

end
