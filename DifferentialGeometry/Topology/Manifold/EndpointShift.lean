import DifferentialGeometry.Topology.Manifold.BoundaryOrder
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Topology.Order.ProjIcc

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

theorem not_exists_regular_patch_of_endpoint_shift
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace N] [ChartedSpace H N] [BoundarylessManifold I N]
    [CompactSpace N] [Nonempty N]
    (ℓ δ : ℝ) [Fact (0 < ℓ)] (hδ : ℓ ≤ δ) :
    ¬ ∃ u : N × Icc 0 ℓ → ℝ,
      (∀ w, mvfderiv (I.prod (𝓡∂ 1)) u w ≠ 0) ∧
      (∀ᶠ w in 𝓝ˢ ((univ : Set N) ×ˢ {t : Icc 0 ℓ | (t : ℝ) = 0}), u w = (w.2 : ℝ)) ∧
      ∀ᶠ w in 𝓝ˢ ((univ : Set N) ×ˢ {t : Icc 0 ℓ | (t : ℝ) = ℓ}), u w = (w.2 : ℝ) - δ := by
  let : Fact (0 ≤ ℓ) := ⟨(Fact.out : 0 < ℓ).le⟩
  rintro ⟨u, hreg, hlocal₀, hlocal₁⟩
  have hbdy (w : N × Icc 0 ℓ) (hw : (I.prod (𝓡∂ 1)).IsBoundaryPoint w) :
      u w = 0 ∨ u w = ℓ - δ := by
    change w ∈ (I.prod (𝓡∂ 1)).boundary (N × Icc 0 ℓ) at hw
    rw [ModelWithCorners.boundary_of_boundaryless_left, boundary_Icc] at hw
    rcases hw.2 with hw | hw
    · left
      have hzero : (w.2 : ℝ) = 0 := congrArg Subtype.val hw
      have h : u w = (w.2 : ℝ) := subset_of_mem_nhdsSet hlocal₀ ⟨mem_univ _, hzero⟩
      exact h.trans hzero
    · right
      have hone : (w.2 : ℝ) = ℓ := congrArg Subtype.val (show w.2 = ⊤ from hw)
      have h : u w = (w.2 : ℝ) - δ := subset_of_mem_nhdsSet hlocal₁ ⟨mem_univ _, hone⟩
      exact h.trans (congrArg (fun x ↦ x - δ) hone)
  let p : N := Classical.choice inferInstance
  let γ : ℝ → N × Icc 0 ℓ := fun t ↦ (p, projIcc 0 ℓ (Fact.out : 0 ≤ ℓ) t)
  have hγ : Continuous γ := continuous_const.prodMk continuous_projIcc
  have hγ₀ : γ 0 ∈ (univ : Set N) ×ˢ {t : Icc 0 ℓ | (t : ℝ) = 0} := by
    refine ⟨mem_univ _, ?_⟩
    change (projIcc 0 ℓ (Fact.out : 0 ≤ ℓ) 0 : ℝ) = 0
    rw [projIcc_of_mem (Fact.out : 0 ≤ ℓ) ⟨le_rfl, Fact.out⟩]
  have hcoordinate : ∀ᶠ t in 𝓝[≥] (0 : ℝ), ((γ t).2 : ℝ) = 0 + 1 * t := by
    filter_upwards [Icc_mem_nhdsGE (Fact.out : 0 < ℓ)] with t ht
    change (projIcc 0 ℓ (Fact.out : 0 ≤ ℓ) t : ℝ) = 0 + 1 * t
    rw [projIcc_of_mem (Fact.out : 0 ≤ ℓ) ht]
    simp only [one_mul, zero_add]
  have hlt : (0 : ℝ) < ℓ - δ := boundary_value_lt_of_inward_coordinate hreg hbdy γ
    hγ.continuousWithinAt (mem_nhdsSet_iff_forall.mp hlocal₀ _ hγ₀) zero_lt_one hcoordinate
  linarith only [hlt, hδ]

end Poincare.Topology.Manifold
