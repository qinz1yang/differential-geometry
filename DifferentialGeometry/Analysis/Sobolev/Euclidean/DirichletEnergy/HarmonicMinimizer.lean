import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.EulerLagrange
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Existence

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_weakly_harmonic_dirichlet_minimizer
    {ι : Type*} [Fintype ι] (hd : 2 ≤ d) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {b : E → EuclideanSpace ℝ ι}
    (hb : ∀ i, DeGiorgi.MemW1p 2 (fun x => b x i) Ω) :
    ∃ (u : E → EuclideanSpace ℝ ι),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      ∃ hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω,
        (∀ (v : E → EuclideanSpace ℝ ι),
          (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) →
          ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
            (∑ i, ∫ x in Ω, ‖(hu i).weakGrad x‖ ^ 2) ≤
              ∑ i, ∫ x in Ω, ‖(hv i).weakGrad x‖ ^ 2) ∧
        ∀ i (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
          (∫ x in Ω, inner ℝ ((hu i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0 := by
  let _ : NeZero d := ⟨by omega⟩
  have hb0 (i : ι) : DeGiorgi.MemW01p 2 (fun x => b x i - b x i) Ω := by
    simpa only [sub_self] using
      DeGiorgi.smoothTest_memH01 hΩ (DeGiorgi.IsSmoothTestOn.zero (Ω := Ω))
  obtain ⟨u, hu0, _, hu, hmin⟩ := exists_dirichlet_integral_minimizer hd hΩ hΩb hb
    (K := Set.univ) isClosed_univ ⟨b, hb0, Filter.Eventually.of_forall fun _ => mem_univ _⟩
  have hmin' : ∀ (v : E → EuclideanSpace ℝ ι),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) →
      ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
        (∑ i, ∫ x in Ω, ‖(hu i).weakGrad x‖ ^ 2) ≤
          ∑ i, ∫ x in Ω, ‖(hv i).weakGrad x‖ ^ 2 := by
    intro v hv0 hv
    exact hmin v hv0 (Filter.Eventually.of_forall fun _ => mem_univ _) hv
  exact ⟨u, hu0, hu, hmin', fun i φ hφ =>
    integral_inner_weakGrad_smoothGrad_eq_zero_of_dirichlet_minimizer hΩ hu hu0 hmin' i hφ⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean
