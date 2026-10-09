import DifferentialGeometry.Analysis.InnerProductSpace.AnchorAlignment

/-!
# Consumers of FC20 and FC21

With zero distortion, FC20 says that a distance-preserving map of the ball of radius `2a` fixing
the origin agrees with one linear isometry on the ball of radius `a`; FC21 then turns an exact
raw factor identity `Ψ = f(Pu - c) + d` into an exact affine coisometry identity.
-/

set_option autoImplicit false

open Module

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_linearIsometryEquiv_eqOn_of_isometry_ball {a : ℝ} (ha : 0 < a) (f : E → E)
    (h0 : f 0 = 0) (hiso : ∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → ‖f v - f w‖ = ‖v - w‖) :
    ∃ Q : E ≃ₗᵢ[ℝ] E, ∀ v, ‖v‖ ≤ a → f v = Q v := by
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_anchor_alignment ha le_rfl (by simpa using ha.le)
    f h0 (fun v w hv hw => by rw [hiso v w hv hw, sub_self, abs_zero])
  exact ⟨Q, fun v hv => sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hQ v hv))⟩

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

theorem exists_coisometry_eq_of_exact_raw_factor {X : Type*} (u : X → F) (Ψ : X → G)
    (P : F →L[ℝ] G) (hP : P.comp (ContinuousLinearMap.adjoint P) = ContinuousLinearMap.id ℝ G)
    (c d : G) {a : ℝ} (ha : 0 < a) (f : G → G) (h0 : f 0 = 0)
    (hiso : ∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → ‖f v - f w‖ = ‖v - w‖)
    (hraw : ∀ x, Ψ x = f (P (u x) - c) + d) (hball : ∀ x, ‖P (u x) - c‖ ≤ a) :
    ∃ A : F →L[ℝ] G, ∃ b₀ : G,
      A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ G ∧
        ∀ x, Ψ x = A (u x) + b₀ := by
  obtain ⟨A, b₀, hA, hval⟩ := exists_coisometry_raw_factor_alignment u Ψ P hP c d (ec := 0) ha
    le_rfl (by simpa using ha.le) f h0
    (fun v w hv hw => by rw [hiso v w hv hw, sub_self, abs_zero])
    (fun x => by rw [hraw x]; simp) hball
  refine ⟨A, b₀, hA, fun x => ?_⟩
  have := hval x
  rw [mul_zero, zero_add] at this
  have h := norm_le_zero_iff.mp this
  rw [sub_sub, sub_eq_zero] at h
  exact h

/-- FC20 for `n = 1` in W4-EGP's real form (`RealAnchorAlignment.exists_sign_of_real_anchor_alignment`
has the same conclusion without the bound `20δ ≤ a`). -/
theorem exists_sign_of_anchor_alignment_real {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ)
    (hδa : 20 * δ ≤ a) (f : ℝ → ℝ) (h0 : f 0 = 0)
    (hdist : ∀ v w, |v| < 2 * a → |w| < 2 * a → |(|f v - f w| - |v - w|)| ≤ δ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ v, |v| ≤ a → |f v - σ * v| ≤ 24 * δ := by
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_anchor_alignment (E := ℝ) ha hδ
    (by simpa using hδa) f h0 (fun v w hv hw => by simpa using hdist v w hv hw)
  have hQv : ∀ v : ℝ, Q v = Q 1 * v := fun v => by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have hσ : |Q 1| = 1 := by
    have := Q.norm_map 1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_one] at this
  refine ⟨Q 1, ?_, fun v hv => ?_⟩
  · rcases (abs_eq zero_le_one).mp hσ with h | h
    · exact Or.inl h
    · exact Or.inr h
  · have := hQ v (by simpa using hv)
    simpa [hQv v] using this

end InnerProductSpace
