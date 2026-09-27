import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.SphereSeparation.ComponentCount
import DifferentialGeometry.Topology.SphereSeparation.Defs

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open Set
open Metric

abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)

private theorem unitSphere_connected :
    IsConnected (sphere (0 : EuclideanThree) 1) := by
  apply isConnected_sphere
  · rw [← Module.finrank_eq_rank']
    norm_num [EuclideanThree, Module.finrank_fin_fun]
  · positivity

theorem isConnected_sphereTwo : IsConnected (Set.univ : Set SphereTwo) := by
  let _ : ConnectedSpace SphereTwo := Subtype.connectedSpace unitSphere_connected
  exact isConnected_univ

private theorem exterior_connected :
    IsConnected ((closedBall (0 : EuclideanThree) 1)ᶜ) := by
  let f : EuclideanThree × ℝ → EuclideanThree := fun p => p.2 • p.1
  have hsource :
      IsConnected (sphere (0 : EuclideanThree) 1 ×ˢ Ioi (1 : ℝ)) :=
    unitSphere_connected.prod isConnected_Ioi
  have himage :
      f '' (sphere (0 : EuclideanThree) 1 ×ˢ Ioi (1 : ℝ)) =
        (closedBall (0 : EuclideanThree) 1)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
      rw [mem_compl_iff, mem_closedBall_zero_iff, not_le]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hr)]
      rw [mem_sphere_zero_iff_norm] at hu
      rw [hu, mul_one]
      exact hr
    · intro hx
      have hxnorm : 1 < ‖x‖ := by
        simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using hx
      have hxne : ‖x‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hxnorm)
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ?_, ?_⟩
      · constructor
        · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
          exact inv_mul_cancel₀ hxne
        · exact hxnorm
      · dsimp [f]
        rw [smul_smul, mul_inv_cancel₀ hxne, one_smul]
  rw [← himage]
  exact hsource.image f (by fun_prop)

private theorem exterior_noncompact :
    ¬ IsCompact (closure ((closedBall (0 : EuclideanThree) 1)ᶜ)) := by
  intro hcompact
  have hbounded := hcompact.isBounded
  rw [Metric.isBounded_iff_subset_closedBall 0] at hbounded
  obtain ⟨r, hr⟩ := hbounded
  let e : EuclideanThree := EuclideanSpace.single 0 (max 2 (r + 1))
  have heNorm : ‖e‖ = max 2 (r + 1) := by
    simp [e, Real.norm_eq_abs, abs_of_nonneg (le_trans (by positivity) (le_max_left _ _))]
  have heExterior : e ∈ (closedBall (0 : EuclideanThree) 1)ᶜ := by
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le, heNorm]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have heClosure : e ∈ closure ((closedBall (0 : EuclideanThree) 1)ᶜ) :=
    subset_closure heExterior
  have heBounded : e ∈ closedBall (0 : EuclideanThree) r := hr heClosure
  rw [mem_closedBall_zero_iff, heNorm] at heBounded
  have : r < max 2 (r + 1) := lt_of_lt_of_le (lt_add_one r) (le_max_right _ _)
  exact (not_lt_of_ge heBounded) this

noncomputable def standardUnitSphereSides :
    SphereSides (sphere (0 : EuclideanThree) 1) where
  compactSide := ball 0 1
  endSide := (closedBall 0 1)ᶜ
  isOpen_compactSide := isOpen_ball
  isOpen_endSide := isClosed_closedBall.isOpen_compl
  isConnected_compactSide := isConnected_ball (by positivity)
  isConnected_endSide := exterior_connected
  disjoint := by
    rw [Set.disjoint_left]
    intro x hxBall hxExterior
    exact hxExterior (ball_subset_closedBall hxBall)
  union_eq_compl := by
    ext x
    simp only [mem_union, mem_ball_zero_iff, mem_compl_iff,
      mem_closedBall_zero_iff, mem_sphere_zero_iff_norm]
    rw [not_le]
    constructor
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
    · exact lt_or_gt_of_ne
  isCompact_closure_compactSide := by
    rw [closure_ball 0 one_ne_zero]
    exact isCompact_closedBall 0 1
  not_isCompact_closure_endSide := exterior_noncompact
  frontier_compactSide := frontier_ball 0 one_ne_zero
  frontier_endSide := by
    rw [frontier_compl, frontier_closedBall 0 one_ne_zero]
  closure_compactSide := by
    rw [closure_ball 0 one_ne_zero]
    ext x
    simp only [mem_closedBall_zero_iff, mem_union, mem_ball_zero_iff,
      mem_sphere_zero_iff_norm]
    exact le_iff_lt_or_eq
  closure_endSide := by
    rw [closure_compl, interior_closedBall 0 one_ne_zero]
    ext x
    simp only [mem_compl_iff, mem_ball_zero_iff, mem_closedBall_zero_iff,
      mem_union, mem_sphere_zero_iff_norm]
    rw [not_lt, not_le]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact h.le
      · exact h.symm.le
  interior_closure_compactSide := by
    rw [closure_ball 0 one_ne_zero, interior_closedBall 0 one_ne_zero]

noncomputable def standardUnitSphereComplementComponents :
    ConnectedComponents
      ((Metric.sphere (0 : EuclideanThree) 1)ᶜ : Set EuclideanThree) ≃ Fin 2 :=
  connectedComponentsComplEquivFinTwo standardUnitSphereSides

end DifferentialGeometry.Topology.SphereSeparation
