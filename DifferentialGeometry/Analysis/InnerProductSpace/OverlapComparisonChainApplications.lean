import DifferentialGeometry.Analysis.InnerProductSpace.OverlapComparisonChain

/-!
# Consumer of the FC23 chain: exact data give an exact affine comparison

With an exactly isometric factor map (`δ_f = 0`), exact raw identities (`e_c = 0`) and exact
long/short tests (`α_F = α_G = β = δ = 0`), the chain returns one coisometry `A` with
`Ψ = A u + b₀` on the short buffer and `dF = A ∘ dG` at every tested point.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace InnerProductSpace

variable {k m : ℕ}

theorem exists_coisometry_eq_of_exact_overlap_data {X : Type*} {T : X → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)] [∀ x, CompleteSpace (T x)]
    (u : X → EuclideanSpace ℝ (Fin m)) (Ψ : X → EuclideanSpace ℝ (Fin k)) (S D : Set X)
    (P : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hP : P.comp (ContinuousLinearMap.adjoint P) = ContinuousLinearMap.id ℝ _)
    (c d : EuclideanSpace ℝ (Fin k)) {a : ℝ} (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) (h0 : f 0 = 0)
    (hiso : ∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → ‖f v - f w‖ = ‖v - w‖)
    (hraw : ∀ x ∈ S, Ψ x = f (P (u x) - c) + d) (hball : ∀ x ∈ S, ‖P (u x) - c‖ ≤ a)
    (dF : ∀ x, T x →L[ℝ] EuclideanSpace ℝ (Fin k)) (dG : ∀ x, T x →L[ℝ] EuclideanSpace ℝ (Fin m))
    {ℓ₀ t : ℝ} (hℓ₀ : 0 < ℓ₀) (ht : 0 < t)
    (hF : ∀ x ∈ D, ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x)‖ ≤ 1)
    (hG : ∀ x ∈ D, ‖dG x‖ ≤ 1) (hDS : D ⊆ S)
    (htests : ∀ x ∈ D, ∀ i : Fin k, ∃ w : T x, ‖w‖ = 1 ∧ ∃ y z : X, ∃ ℓ : ℝ, ℓ₀ ≤ ℓ ∧ z ∈ S ∧
      ℓ ≤ Ψ y i - Ψ x i ∧ Ψ y i - Ψ z i ≤ ℓ - t ∧
      dF x w i = (Ψ y i - Ψ x i) / ℓ ∧ dG x w = t⁻¹ • (u z - u x)) :
    ∃ A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k), ∃ b₀,
      A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
      (∀ x ∈ S, Ψ x = A (u x) + b₀) ∧ ∀ x ∈ D, dF x = A.comp (dG x) := by
  obtain ⟨A, b₀, hA, hval, hder⟩ := exists_coisometry_overlap_comparison u Ψ S D P hP c d ha
    le_rfl (by simpa using ha.le) le_rfl f h0
    (fun v w hv hw => by rw [hiso v w hv hw, sub_self, abs_zero])
    (fun x hx => by rw [hraw x hx]; simp) hball dF dG (αF := 0) (αG := 0) (β := 0) (δ := 0)
    le_rfl hℓ₀ ht le_rfl le_rfl (fun x hx i => by simpa using hF x hx i)
    (fun x hx => by simpa using hG x hx) hDS (fun x hx i => by
      obtain ⟨w, hw, y, z, ℓ, hℓ, hz, h1, h2, h3, h4⟩ := htests x hx i
      exact ⟨w, hw, y, z, ℓ, hℓ, hz, by linarith, by linarith, by rw [h3]; simp,
        by rw [h4]; simp⟩)
  refine ⟨A, b₀, hA, fun x hx => ?_, fun x hx => ?_⟩
  · have h := hval x hx
    simp only [mul_zero, add_zero] at h
    rw [← sub_eq_zero, ← sub_sub]
    exact norm_le_zero_iff.mp h
  · have h := hder x hx
    simp only [mul_zero, add_zero, zero_div, max_self, zero_add, mul_zero] at h
    norm_num at h
    exact sub_eq_zero.mp h

end InnerProductSpace
