import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

noncomputable section

theorem DifferentialGeometry.Analysis.surjective_coprod_graphs_of_ne
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : V →L[ℝ] E) (N : E) (ℓ₁ ℓ₂ : V →L[ℝ] ℝ)
    (hspan : ∀ v : E, ∃ (w : V) (t : ℝ), v = L w + t • N)
    (hne : ℓ₁ ≠ ℓ₂) :
    Function.Surjective
      ((L + ℓ₁.smulRight N).coprod (-(L + ℓ₂.smulRight N))) := by
  have hnonzero : (ℓ₁ - ℓ₂).toLinearMap ≠ 0 := by
    intro hzero
    apply hne
    apply ContinuousLinearMap.ext
    intro w
    have hw := LinearMap.congr_fun hzero w
    change ℓ₁ w - ℓ₂ w = 0 at hw
    exact sub_eq_zero.mp hw
  have hsurj : Function.Surjective (ℓ₁ - ℓ₂) :=
    surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (A := ℝ)
      (f := (ℓ₁ - ℓ₂).toLinearMap) (by simp) hnonzero
  intro v
  obtain ⟨w, t, hv⟩ := hspan v
  obtain ⟨z, hz⟩ := hsurj (t - ℓ₁ w)
  change ℓ₁ z - ℓ₂ z = t - ℓ₁ w at hz
  have hscalar : ℓ₁ (w + z) = t + ℓ₂ z := by
    rw [map_add, (sub_eq_iff_eq_add).mp hz, ← add_assoc, add_sub_cancel]
  have hsum : L (w + z) + ℓ₁ (w + z) • N = v + (L z + ℓ₂ z • N) := by
    rw [map_add, hscalar, add_smul, hv]
    exact add_add_add_comm _ _ _ _
  refine ⟨(w + z, z), ?_⟩
  change (L (w + z) + ℓ₁ (w + z) • N) + -(L z + ℓ₂ z • N) = v
  rw [hsum, add_neg_cancel_right]
