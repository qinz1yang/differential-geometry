import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionIntertwiner

/-!
# Consumers of the near-one square root and of the projection intertwiner

Lane CMS-BUN (S-BUNDLE, consumers of G1–G2).
* In `ℝ`, `sqrtNearOne` is the usual square root near `1`.
* Kato's theorem in uniform form: there is `ε > 0` (depending only on the space) such that any two
  orthogonal projections at distance `< ε` are conjugate by a linear isometric equivalence.
-/

set_option autoImplicit false

noncomputable section

open Metric

namespace DifferentialGeometry.Analysis.ProjectionIntertwiner

open DifferentialGeometry.Analysis.NearOneSqrt

theorem sqrtNearOne_real_eq_sqrt {x : ℝ} (hx : x ∈ ball (1 : ℝ) (sqrtRadius ℝ)) (h0 : 0 < x)
    (h4 : x < 4) : sqrtNearOne ℝ x = Real.sqrt x := by
  symm
  apply eq_sqrtNearOne hx
  · rw [Real.norm_eq_abs, abs_lt]
    constructor
    · have := Real.sqrt_pos.mpr h0
      linarith
    · have h2 : Real.sqrt x < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num; exact h4)
      linarith
  · exact Real.mul_self_sqrt h0.le

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Uniform Kato theorem: orthogonal projections at distance `< ε` are conjugate by a linear
isometric equivalence of the whole space. -/
theorem exists_linearIsometryEquiv_intertwining :
    ∃ ε > 0, ∀ P Q : F →L[ℝ] F, P ∘L P = P → P.adjoint = P → Q ∘L Q = Q → Q.adjoint = Q →
      ‖Q - P‖ < ε → ∃ B : F ≃ₗᵢ[ℝ] F, ∀ v, B (P v) = Q (B v) := by
  refine ⟨min 1 (Real.sqrt (sqrtRadius (F →L[ℝ] F))),
    lt_min one_pos (Real.sqrt_pos.mpr sqrtRadius_pos), ?_⟩
  intro P Q hP hPs hQ hQs hε
  have h1 : ‖Q - P‖ < 1 := lt_of_lt_of_le hε (min_le_left _ _)
  have hη : ‖Q - P‖ ^ 2 < sqrtRadius (F →L[ℝ] F) := by
    have h2 : ‖Q - P‖ < Real.sqrt (sqrtRadius (F →L[ℝ] F)) := lt_of_lt_of_le hε (min_le_right _ _)
    exact (Real.lt_sqrt (norm_nonneg _)).mp h2
  obtain ⟨hint, hBB, hBB', -, -⟩ := projIntertwiner_spec hP hPs hQ hQs h1 hη
  have hmem : projIntertwiner P Q ∈ unitary (F →L[ℝ] F) := by
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint]
    exact ⟨hBB, hBB'⟩
  refine ⟨Unitary.linearIsometryEquiv ⟨_, hmem⟩, fun v => ?_⟩
  exact congrArg (fun L : F →L[ℝ] F => L v) hint

end DifferentialGeometry.Analysis.ProjectionIntertwiner
