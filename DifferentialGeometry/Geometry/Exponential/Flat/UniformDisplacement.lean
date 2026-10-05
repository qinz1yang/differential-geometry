import DifferentialGeometry.Geometry.Exponential.Flat.AffineTranslations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Uniform displacement in an actual free cocompact affine group

Recentering an arbitrary point by an actual group element puts it in a bounded ball. A small
movement then belongs to a finite set of conjugates. Freeness and compactness give a positive
minimum for their movements on that ball, hence a uniform lower bound at every ambient point.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instSpace : NormedSpace ℝ V] [instFD : FiniteDimensional ℝ V]

theorem exists_uniform_affine_displacement (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {g : G | ‖(g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ B})
    (hcov : ∀ x : V, ∃ k : G, ‖x - (k : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R)
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : V, (g : V ≃ᵃⁱ[ℝ] V) x ≠ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : G, g ≠ 1 → ∀ x : V, c ≤ ‖(g : V ≃ᵃⁱ[ℝ] V) x - x‖ := by
  classical
  let S : Set G := {g | ‖(g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ 2 * R + 1 ∧ g ≠ 1}
  have hS : S.Finite := (hdisc (2 * R + 1)).subset fun g hg => hg.1
  let K : Set ℝ := ⋃ g ∈ S,
    (fun y : V => ‖(g : V ≃ᵃⁱ[ℝ] V) y - y‖) '' Metric.closedBall 0 R
  have hK : IsCompact K := hS.isCompact_biUnion fun g hg =>
    (isCompact_closedBall (0 : V) R).image
      ((g : V ≃ᵃⁱ[ℝ] V).continuous.sub continuous_id).norm
  have hKpos : ∀ b ∈ K, 0 < b := by
    intro b hb
    rcases Set.mem_iUnion.mp hb with ⟨g, hg⟩
    rcases Set.mem_iUnion.mp hg with ⟨hgs, hy⟩
    rcases hy with ⟨y, hy, rfl⟩
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hfree g hgs.2 y))
  obtain ⟨c₀, hc₀, hmin⟩ := hK.exists_forall_le' continuous_id.continuousOn hKpos
  refine ⟨min c₀ 1, lt_min hc₀ zero_lt_one, ?_⟩
  intro g hgne x
  by_cases hsmall : ‖(g : V ≃ᵃⁱ[ℝ] V) x - x‖ < 1
  · obtain ⟨k, hk⟩ := hcov x
    let y := (k : V ≃ᵃⁱ[ℝ] V).symm x
    let a : G := k⁻¹ * g * k
    have hy : ‖y‖ ≤ R := by
      have heq := (k : V ≃ᵃⁱ[ℝ] V).isometry.dist_eq y 0
      change dist ((k : V ≃ᵃⁱ[ℝ] V) ((k : V ≃ᵃⁱ[ℝ] V).symm x))
        ((k : V ≃ᵃⁱ[ℝ] V) 0) = dist y 0 at heq
      rw [AffineIsometryEquiv.apply_symm_apply, dist_zero_right, dist_eq_norm] at heq
      exact heq ▸ hk
    have hmovement : ‖(a : V ≃ᵃⁱ[ℝ] V) y - y‖ =
        ‖(g : V ≃ᵃⁱ[ℝ] V) x - x‖ := by
      change ‖(k : V ≃ᵃⁱ[ℝ] V).symm
        ((g : V ≃ᵃⁱ[ℝ] V) ((k : V ≃ᵃⁱ[ℝ] V) ((k : V ≃ᵃⁱ[ℝ] V).symm x))) -
          (k : V ≃ᵃⁱ[ℝ] V).symm x‖ = ‖(g : V ≃ᵃⁱ[ℝ] V) x - x‖
      rw [AffineIsometryEquiv.apply_symm_apply, ← dist_eq_norm, ← dist_eq_norm]
      exact (k : V ≃ᵃⁱ[ℝ] V).symm.isometry.dist_eq _ _
    have ha0 : ‖(a : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ 2 * R + 1 := by
      have htri := dist_triangle ((a : V ≃ᵃⁱ[ℝ] V) 0) ((a : V ≃ᵃⁱ[ℝ] V) y) 0
      have htri' := dist_triangle ((a : V ≃ᵃⁱ[ℝ] V) y) y 0
      rw [(a : V ≃ᵃⁱ[ℝ] V).isometry.dist_eq, dist_zero_left, dist_zero_right,
        dist_zero_right] at htri
      simp only [dist_eq_norm, sub_zero] at htri'
      rw [hmovement] at htri'
      linarith
    have hane : a ≠ 1 := by
      intro ha
      apply hgne
      have hh := congrArg (fun z : G => k * z * k⁻¹) ha
      simpa [a, mul_assoc] using hh
    have hmem : ‖(a : V ≃ᵃⁱ[ℝ] V) y - y‖ ∈ K := by
      refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨⟨ha0, hane⟩, ?_⟩⟩
      exact ⟨y, mem_closedBall_zero_iff.mpr hy, rfl⟩
    exact (min_le_left c₀ 1).trans (hmovement ▸ hmin _ hmem)
  · exact (min_le_right c₀ 1).trans (le_of_not_gt hsmall)

end DifferentialGeometry.Geometry.FlatSurface
