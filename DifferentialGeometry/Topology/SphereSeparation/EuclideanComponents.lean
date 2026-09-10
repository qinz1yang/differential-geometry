import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.MetricSpace.ProperSpace
import DifferentialGeometry.Topology.SphereSeparation.ComplementPair
import DifferentialGeometry.Topology.SphereSeparation.StandardSphere

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open Set
open Metric

private theorem outside_closedBall_connected (R : ℝ) (hR : 0 < R) :
    IsConnected ((closedBall (0 : EuclideanThree) R)ᶜ) := by
  let f : EuclideanThree × ℝ → EuclideanThree := fun p => p.2 • p.1
  have hSphere : IsConnected (sphere (0 : EuclideanThree) 1) := by
    apply isConnected_sphere
    · rw [← Module.finrank_eq_rank']
      norm_num [EuclideanThree, Module.finrank_fin_fun]
    · positivity
  have hSource :
      IsConnected (sphere (0 : EuclideanThree) 1 ×ˢ Ioi R) :=
    hSphere.prod isConnected_Ioi
  have hImage :
      f '' (sphere (0 : EuclideanThree) 1 ×ˢ Ioi R) =
        (closedBall (0 : EuclideanThree) R)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
      rw [mem_compl_iff, mem_closedBall_zero_iff, not_le]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_trans hR hr)]
      rw [mem_sphere_zero_iff_norm] at hu
      change R < r at hr
      simpa only [hu, mul_one] using hr
    · intro hx
      have hxNorm : R < ‖x‖ := by
        simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using hx
      have hxne : ‖x‖ ≠ 0 := ne_of_gt (lt_trans hR hxNorm)
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ?_, ?_⟩
      · constructor
        · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
          exact inv_mul_cancel₀ hxne
        · exact hxNorm
      · dsimp [f]
        rw [smul_smul, mul_inv_cancel₀ hxne, one_smul]
  rw [← hImage]
  exact hSource.image f (by fun_prop)

private theorem closure_compact_of_subset_closedBall {C : Set EuclideanThree} {R : ℝ}
    (hC : C ⊆ closedBall 0 R) : IsCompact (closure C) := by
  exact (isCompact_closedBall (0 : EuclideanThree) R).of_isClosed_subset
    isClosed_closure (closure_minimal hC isClosed_closedBall)

private theorem closure_noncompact_of_outside_subset {C : Set EuclideanThree} {R : ℝ}
    (hR : 0 < R) (hOutside : (closedBall 0 R)ᶜ ⊆ C) :
    ¬ IsCompact (closure C) := by
  intro hCompact
  have hBounded := hCompact.isBounded
  rw [Metric.isBounded_iff_subset_closedBall 0] at hBounded
  obtain ⟨r, hr⟩ := hBounded
  let q : ℝ := max (R + 1) (r + 1)
  let x : EuclideanThree := EuclideanSpace.single 0 q
  have hqNonneg : 0 ≤ q := by
    have hRone : 0 < R + 1 := by linarith
    exact hRone.le.trans (le_max_left _ _)
  have hxNorm : ‖x‖ = q := by
    simp [x, q, Real.norm_eq_abs, abs_of_nonneg hqNonneg]
  have hxOutside : x ∈ (closedBall (0 : EuclideanThree) R)ᶜ := by
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le, hxNorm]
    exact lt_of_lt_of_le (lt_add_one R) (le_max_left _ _)
  have hxClosure : x ∈ closure C := subset_closure (hOutside hxOutside)
  have hxBound := hr hxClosure
  rw [mem_closedBall_zero_iff, hxNorm] at hxBound
  exact (not_lt_of_ge hxBound)
    (lt_of_lt_of_le (lt_add_one r) (le_max_right _ _))

private theorem subset_closedBall_of_outside_subset_other
    {L Rgt : Set EuclideanThree} {R : ℝ}
    (hDisjoint : Disjoint L Rgt) (hOutside : (closedBall 0 R)ᶜ ⊆ L) :
    Rgt ⊆ closedBall 0 R := by
  intro x hxRight
  by_contra hxBall
  exact Set.disjoint_left.1 hDisjoint (hOutside hxBall) hxRight

private theorem sphereSidesOfComplementPair_nonempty {S : Set EuclideanThree}
    (hSCompact : IsCompact S) (p : ComplementPair S)
    (hSleft : S ⊆ closure p.left) (hSright : S ⊆ closure p.right) :
    Nonempty (SphereSides S) := by
  have hSBounded := hSCompact.isBounded
  rw [Metric.isBounded_iff_subset_closedBall 0] at hSBounded
  let r : ℝ := Classical.choose hSBounded
  have hr : S ⊆ closedBall (0 : EuclideanThree) r := Classical.choose_spec hSBounded
  let R : ℝ := max 1 r
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hSBall : S ⊆ closedBall (0 : EuclideanThree) R := by
    intro x hxS
    have hx := hr hxS
    rw [mem_closedBall_zero_iff] at hx ⊢
    exact hx.trans (le_max_right _ _)
  have hOutsideS : (closedBall (0 : EuclideanThree) R)ᶜ ⊆ Sᶜ := by
    intro x hxOutside hxS
    exact hxOutside (hSBall hxS)
  rcases p.subset_left_or_subset_right
      (outside_closedBall_connected R hR).isPreconnected hOutsideS with
    hOutsideLeft | hOutsideRight
  · have hRightBall : p.right ⊆ closedBall (0 : EuclideanThree) R :=
      subset_closedBall_of_outside_subset_other p.disjoint hOutsideLeft
    exact ⟨p.swap.toSphereSides
      (closure_compact_of_subset_closedBall hRightBall)
      (closure_noncompact_of_outside_subset hR hOutsideLeft)
      hSright hSleft⟩
  · have hLeftBall : p.left ⊆ closedBall (0 : EuclideanThree) R :=
      subset_closedBall_of_outside_subset_other p.disjoint.symm hOutsideRight
    exact ⟨p.toSphereSides
      (closure_compact_of_subset_closedBall hLeftBall)
      (closure_noncompact_of_outside_subset hR hOutsideRight)
      hSleft hSright⟩

noncomputable def sphereSidesOfComplementPair {S : Set EuclideanThree}
    (hSCompact : IsCompact S) (p : ComplementPair S)
    (hSleft : S ⊆ closure p.left) (hSright : S ⊆ closure p.right) :
    SphereSides S :=
  Classical.choice (sphereSidesOfComplementPair_nonempty hSCompact p hSleft hSright)

end DifferentialGeometry.Topology.SphereSeparation
