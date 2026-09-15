import Mathlib.Geometry.Manifold.ContMDiff.Basic

section

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {H₁ H₂ H₃ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂]
  [TopologicalSpace H₃]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {I₃ : ModelWithCorners 𝕜 E₃ H₃}
  {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
  {n : WithTop ℕ∞}

theorem IsCompact.eventually_contMDiffOn_of_locally_eventually_contMDiffOn
    {A : Type*} {l : Filter A} {M : A → Type*}
    [∀ a, TopologicalSpace (M a)] [∀ a, ChartedSpace H₂ (M a)]
    {f : ∀ a, M₁ → M a} {K : Set M₁} (hK : IsCompact K)
    (hloc : ∀ x ∈ K, ∃ U : Set M₁, U ∈ 𝓝 x ∧
      ∀ᶠ a in l, ContMDiffOn I₁ I₂ n (f a) U) :
    ∀ᶠ a in l, ContMDiffOn I₁ I₂ n (f a) K := by
  classical
  choose U hUx hU using hloc
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => interior (U x hx))
    (fun x hx => interior_mem_nhds.mpr (hUx x hx))
  have htail : ∀ᶠ a in l, ∀ x ∈ t,
      ContMDiffOn I₁ I₂ n (f a) (U x x.property) := by
    exact (eventually_all_finite t.finite_toSet).mpr (fun x _ => hU x x.property)
  filter_upwards [htail] with a ha x hx
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (ht hx)
  exact ((ha y hyt x (interior_subset hy)).contMDiffAt
    (mem_interior_iff_mem_nhds.mp hy)).contMDiffWithinAt

end

end
