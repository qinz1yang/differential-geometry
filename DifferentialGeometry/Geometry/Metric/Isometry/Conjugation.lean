import DifferentialGeometry.Geometry.Metric.Isometry.Compactness
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Group

namespace IsometryEquiv

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_pos_pow_commute_of_bounded_displacement
    (Γ : Subgroup (X ≃ᵢ X)) [DiscreteTopology Γ] (f g : Γ) (x : X) (R : ℝ)
    (hR : ∀ n : ℕ, dist ((g : X ≃ᵢ X) (((f ^ n : Γ) : X ≃ᵢ X) x))
      (((f ^ n : Γ) : X ≃ᵢ X) x) ≤ R) :
    ∃ n : ℕ, 0 < n ∧ Commute (f ^ n) g := by
  have hΓ : IsClosed (Γ : Set (X ≃ᵢ X)) := Subgroup.isClosed_of_discreteTopology
  have hfin : Set.Finite {h : Γ | dist ((h : X ≃ᵢ X) x) x ≤ R} :=
    (hΓ.isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_setOf_dist_apply_le x R)).finite_of_discrete
  let c (n : ℕ) : Γ := (f ^ n)⁻¹ * g * f ^ n
  have hc (n : ℕ) : c n ∈ {h : Γ | dist ((h : X ≃ᵢ X) x) x ≤ R} := by
    change dist (((((f ^ n : Γ) : X ≃ᵢ X)).symm)
      ((g : X ≃ᵢ X) (((f ^ n : Γ) : X ≃ᵢ X) x))) x ≤ R
    calc
      _ = dist (((f ^ n : Γ) : X ≃ᵢ X).symm
          ((g : X ≃ᵢ X) (((f ^ n : Γ) : X ≃ᵢ X) x)))
          (((f ^ n : Γ) : X ≃ᵢ X).symm (((f ^ n : Γ) : X ≃ᵢ X) x)) := by
        rw [IsometryEquiv.symm_apply_apply]
      _ = dist ((g : X ≃ᵢ X) (((f ^ n : Γ) : X ≃ᵢ X) x))
          (((f ^ n : Γ) : X ≃ᵢ X) x) := ((f ^ n : Γ) : X ≃ᵢ X).symm.dist_eq _ _
      _ ≤ R := hR n
  obtain ⟨m, n, hmn, heq⟩ := hfin.exists_lt_map_eq_of_forall_mem hc
  refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  have h : f ^ n * (f ^ m)⁻¹ * g = g * (f ^ n * (f ^ m)⁻¹) := by
    have h := congrArg (fun z : Γ => f ^ n * z * (f ^ m)⁻¹) heq
    dsimp only [c] at h
    group at h ⊢
    exact h
  simpa only [Commute, SemiconjBy, pow_sub f hmn.le] using h

end IsometryEquiv
