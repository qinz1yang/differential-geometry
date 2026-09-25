import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.Connected.FinitePartition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.eq_of_preconnected_of_mem_endpoints
    {T A : Set E} {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) T)
    (hA : IsPreconnected A) (hAT : A ⊆ T) (h₀ : γ 0 ∈ A) (h₁ : γ 1 ∈ A) : A = T := by
  let δ := Function.invFunOn γ (Icc (0 : ℝ) 1)
  have hδ := hγ.symm
  have hpre : IsPreconnected (δ '' A) :=
    hA.image δ (hδ.isPiecewiseAffineOn.continuousOn.mono hAT)
  have hzero : δ (γ 0) = 0 := hγ.bijOn.invOn_invFunOn.1 ⟨le_rfl, zero_le_one⟩
  have hone : δ (γ 1) = 1 := hγ.bijOn.invOn_invFunOn.1 ⟨zero_le_one, le_rfl⟩
  have hI : Icc (0 : ℝ) 1 ⊆ δ '' A :=
    hpre.Icc_subset ⟨γ 0, h₀, hzero⟩ ⟨γ 1, h₁, hone⟩
  apply Subset.antisymm hAT
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hI (hδ.bijOn.mapsTo hx)
  exact hδ.bijOn.injOn (hAT hy) hx hyx ▸ hy

theorem exists_member_eq_of_arc_between_partition_boundary_marks
    {C : Set (Set E)} (hC : C.Finite)
    (hdis : C.PairwiseDisjoint id) {W : Set E}
    (hcharts : ∀ T ∈ C, ∃ δ : ℝ → E, IsPLHomeomorphOn δ (Icc 0 1) T ∧
      T ∩ W = {δ 0, δ 1}) {A : Set E} {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) (hAC : A ⊆ ⋃₀ C)
    (h₀ : γ 0 ∈ W) (h₁ : γ 1 ∈ W) : A ∈ C := by
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
  have hclosed (T : Set E) (hTC : T ∈ C) : IsClosed T := by
    obtain ⟨δ, hδ, _⟩ := hcharts T hTC
    exact ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hδ).isPolyhedron.isClosed
  obtain ⟨T, ⟨hTC, hAT⟩, _⟩ :=
    Topology.existsUnique_subset_of_isConnected_of_finite_closed_partition
      hA.isConnected hC hclosed hdis hAC
  obtain ⟨δ, hδ, hTW⟩ := hcharts T hTC
  have hγ₀ : γ 0 ∈ A := hγ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hγ₁ : γ 1 ∈ A := hγ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hne : γ 0 ≠ γ 1 := fun h =>
    zero_ne_one (hγ.bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ h)
  have hp := hTW.subset ⟨hAT hγ₀, h₀⟩
  have hq := hTW.subset ⟨hAT hγ₁, h₁⟩
  have hends : δ 0 ∈ A ∧ δ 1 ∈ A := by
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact (hne (hp.trans hq.symm)).elim
    · exact ⟨hp ▸ hγ₀, hq ▸ hγ₁⟩
    · exact ⟨hq ▸ hγ₁, hp ▸ hγ₀⟩
    · exact (hne (hp.trans hq.symm)).elim
  have heq := hδ.eq_of_preconnected_of_mem_endpoints hA.isConnected.isPreconnected hAT
    hends.1 hends.2
  exact heq.symm ▸ hTC

end DifferentialGeometry.Topology.PiecewiseLinear
