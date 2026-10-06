import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighMinimizer_EG

/-!
# Consumer of `exists_rayleigh_minimizer_EG` (S-W-EIG, G1)

The special case `ρ = 1`, `W = 0`: for every nonempty bounded open `Ω ⊂ ℝᵈ` the Dirichlet
Poincaré inequality `μ ∫ v² ≤ ∫ |∇v|²` on `H¹₀(Ω)` holds with an attained constant `μ ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The best Dirichlet-Poincaré constant on a bounded open set is attained by a unit vector
of `H¹₀(Ω)`. -/
theorem exists_attained_dirichlet_gap_EG (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ∃ μ : ℝ, 0 ≤ μ ∧ ∃ u : EuclideanSpace ℝ (Fin d) → ℝ, DeGiorgi.MemW01p 2 u Ω ∧
      (∫ x in Ω, u x ^ 2) = 1 ∧
      ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, DeGiorgi.MemW01p 2 v Ω →
        ∀ hv : DeGiorgi.MemW1pWitness 2 v Ω,
          μ * (∫ x in Ω, v x ^ 2) ≤ ∫ x in Ω, ‖hv.weakGrad x‖ ^ 2 := by
  obtain ⟨u, hu, hw, hN, hmin⟩ := exists_rayleigh_minimizer_EG hΩ hΩb hne
    (ρ := fun _ => 1) (W := fun _ => 0) measurable_const measurable_const (c₀ := 1) (B := 1)
    one_pos (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => by norm_num)
  refine ⟨∫ x in Ω, ‖hw.weakGrad x‖ ^ 2, integral_nonneg fun x => sq_nonneg _, u, hu, ?_, ?_⟩
  · simpa using hN
  · intro v hv0 hv
    simpa using hmin v hv0 hv

end DifferentialGeometry.Analysis.Sobolev.Euclidean
